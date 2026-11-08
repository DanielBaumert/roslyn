// RustSharp: the native compilation pipeline. Roslyn binds and lowers as usual; lowered bodies are
// intercepted in front of the IL emitter, turned into MIR, borrow-checked and handed to LLVM.

using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using System.Text;
using System.Threading;
using Microsoft.CodeAnalysis.CSharp.Symbols;
using Microsoft.CodeAnalysis.Emit;

namespace Microsoft.CodeAnalysis.CSharp.Ownership
{
    /// <summary>Receives every fully lowered method body instead of the IL emitter.</summary>
    internal sealed class LoweredBodySink
    {
        public readonly ConcurrentDictionary<MethodSymbol, BoundStatement> Bodies = new(Symbols.SymbolEqualityComparer.AllIgnoreOptions);
        public void Add(MethodSymbol method, BoundStatement body) => Bodies[method.OriginalDefinition] = body;
    }

    public sealed class NativeOptions
    {
        public string OutputPath = "a.out";
        public string LlvmOutputPath;
        public string MirOutputPath;
        public int OptimizationLevel = 2;
        public bool CheckOnly;
        /// <summary>Instruments the program with AddressSanitizer, to validate the generated memory management.</summary>
        public bool Sanitize;
        /// <summary>Instruments the program with ThreadSanitizer, to look for data races.</summary>
        public bool SanitizeThreads;
        public bool BorrowCheck = true;
        public string Clang = "clang";
        /// <summary>Only diagnostics in trees for which this returns true are reported as user errors.</summary>
        public Func<SyntaxTree, bool> IsUserTree;
    }

    public sealed class NativeLabel
    {
        public Location Location;
        public string Text;
    }

    public sealed class NativeDiagnostic
    {
        public string Code;
        public string Severity = "error";
        public string Message;
        public Location Location;
        public string Label;
        public List<NativeLabel> Secondary = new List<NativeLabel>();
        public string Note;
    }

    public sealed class NativeResult
    {
        public bool Success;
        public List<NativeDiagnostic> Diagnostics = new List<NativeDiagnostic>();
    }

    public static class NativeCompiler
    {
        public static CSharpParseOptions ParseOptions()
            => new CSharpParseOptions(LanguageVersion.Preview, DocumentationMode.None, SourceCodeKind.Regular)
                .WithFeatures(new[] { new KeyValuePair<string, string>("ownership", "true") });

        /// <summary>
        /// The core library is compiled together with the program, but its `internal` members keep the
        /// invariants of safe code (a string is immutable, for one), so user code must not reach them.
        /// </summary>
        private static void CheckLibraryBoundary(MirBody body, Func<SyntaxTree, bool> isUserTree, List<OwnershipDiagnostic> diagnostics)
        {
            bool Hidden(Symbol s)
            {
                bool hidden = false;
                for (var c = s; c is not null and not NamespaceSymbol; c = c.ContainingSymbol)
                    hidden |= c.DeclaredAccessibility is Accessibility.Internal or Accessibility.ProtectedAndInternal;
                if (!hidden) return false;
                var tree = s.OriginalDefinition.DeclaringSyntaxReferences.FirstOrDefault()?.SyntaxTree;
                return tree != null && !isUserTree(tree);
            }

            foreach (var block in body.Reachable())
            {
                if (block.Term is CallTerm { Method: { } m } call && Hidden(m))
                {
                    diagnostics.Add(new OwnershipDiagnostic
                    {
                        Code = (ErrorCode)122,
                        Message = $"`{m.ContainingType.Name}.{m.Name}` is internal to the core library",
                        Location = call.Syntax.Location,
                        Label = "inaccessible from user code"
                    });
                }
            }
        }

        /// <summary>A string is UTF-8 now: `fixed (char* p = s)` would point at nothing sensible.</summary>
        private static void RejectFixedStrings(CSharpCompilation compilation, SyntaxTree tree, List<OwnershipDiagnostic> diagnostics)
        {
            SemanticModel model = null;
            foreach (var f in tree.GetRoot().DescendantNodes().OfType<FixedStatementSyntax>())
                foreach (var v in f.Declaration.Variables)
                {
                    if (v.Initializer?.Value is not { } value) continue;
                    model ??= compilation.GetSemanticModel(tree);
                    if (model.GetTypeInfo(value).Type?.SpecialType != SpecialType.System_String) continue;
                    diagnostics.Add(new OwnershipDiagnostic
                    {
                        Code = ErrorCode.ERR_OwnOwnershipUnsupported,
                        Message = "a string holds UTF-8 bytes, not chars: `fixed` on a string is not supported",
                        Location = value.GetLocation(),
                        Label = "use `s.AsPtr()` for the bytes, or `s.Chars()`",
                    });
                }
        }

        /// <summary>Rust has no inheritance: shared behaviour is a trait (interface), a closed set of cases an enum.</summary>
        private static void RejectInheritance(CSharpCompilation compilation, SyntaxTree tree, List<OwnershipDiagnostic> diagnostics)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var declaration in tree.GetRoot().DescendantNodes().OfType<TypeDeclarationSyntax>())
            {
                if (declaration.BaseList is null || UnionSyntax.IsVariant(declaration)) continue;
                if (model.GetDeclaredSymbol(declaration)?.GetSymbol<NamedTypeSymbol>() is not { TypeKind: TypeKind.Class } type) continue;
                if (type.BaseTypeNoUseSiteDiagnostics is not { SpecialType: not SpecialType.System_Object } baseType) continue;
                var at = declaration.BaseList.Types.First();
                diagnostics.Add(new OwnershipDiagnostic
                {
                    Code = ErrorCode.ERR_OwnNoInheritance,
                    Message = $"`{type.Name}` cannot inherit from `{baseType.Name}`: there is no inheritance",
                    Location = at.GetLocation(),
                    Label = "a base class",
                    Note = "share behaviour through an interface (a trait), or list the cases as an enum with data",
                });
            }
        }

        /// <summary>Rust's E0204: [Copy] needs every field to be Copy, and only value types can be Copy.</summary>
        private static void CheckCopyTypes(CSharpCompilation compilation, SyntaxTree tree, List<OwnershipDiagnostic> diagnostics)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var declaration in tree.GetRoot().DescendantNodes().OfType<BaseTypeDeclarationSyntax>())
            {
                if (model.GetDeclaredSymbol(declaration) is not { } symbol) continue;
                var type = symbol.GetSymbol<NamedTypeSymbol>();
                if (type is null || !OwnershipFacts.HasAttribute(type, "CopyAttribute")) continue;
                if (type.TypeKind is not (TypeKind.Struct or TypeKind.Enum))
                {
                    diagnostics.Add(new OwnershipDiagnostic
                    {
                        Code = ErrorCode.ERR_OwnNotClone,
                        Message = $"`{type.Name}` cannot be Copy: only structs and enums can",
                        Location = declaration.Identifier.GetLocation(),
                        Label = "a class has one owner and is moved",
                    });
                    continue;
                }
                foreach (var field in OwnershipFacts.InstanceFields(type))
                {
                    if (field.Type is TypeParameterSymbol || OwnershipFacts.IsCopy(field.Type)) continue;
                    diagnostics.Add(new OwnershipDiagnostic
                    {
                        Code = ErrorCode.ERR_OwnNotClone,
                        Message = $"`{type.Name}` cannot be Copy: field `{(field.AssociatedSymbol ?? field).Name}` of type `{field.Type.ToDisplayString()}` is not Copy",
                        Location = declaration.Identifier.GetLocation(),
                        Label = "this type is marked [Copy]",
                    });
                }
            }
        }

        /// <summary>Rust has no exceptions: errors are Result values, and bugs panic.</summary>
        private static void RejectExceptions(SyntaxTree tree, List<OwnershipDiagnostic> diagnostics, bool onlyThrow = false)
        {
            foreach (var node in tree.GetRoot().DescendantNodes())
            {
                // The corelib catches panics where a thread or task ends (Rust's catch_unwind); it never throws.
                if (onlyThrow && node is Syntax.TryStatementSyntax) continue;
                var (what, at) = node switch
                {
                    Syntax.ThrowStatementSyntax t => ("throw", t.ThrowKeyword.GetLocation()),
                    Syntax.ThrowExpressionSyntax t => ("throw", t.ThrowKeyword.GetLocation()),
                    Syntax.TryStatementSyntax t => (t.Catches.Count > 0 ? "catch" : "finally", t.TryKeyword.GetLocation()),
                    _ => (null, null),
                };
                if (what is null) continue;
                diagnostics.Add(new OwnershipDiagnostic
                {
                    Code = ErrorCode.ERR_OwnNoExceptions,
                    Message = "there are no exceptions: return a Result for errors, and call Panic.Raise for bugs",
                    Location = at,
                    Label = $"`{what}` does not exist here",
                    Note = what == "throw" ? "an error the caller should handle is a Result<T, E>; `x?` passes it on"
                        : what == "catch" ? "a function that can fail returns a Result; check it with IsOk, `?`, or Unwrap"
                        : "cleanup belongs in a destructor or a `using`, which also runs when a panic unwinds",
                });
            }
        }

        public static NativeResult Compile(CSharpCompilation compilation, NativeOptions options)
        {
            var result = new NativeResult();
            var bag = DiagnosticBag.GetInstance();
            var sink = new LoweredBodySink();

            try
            {
                var emitOptions = EmitOptions.Default.WithDebugInformationFormat(DebugInformationFormat.Embedded);
                var module = (Emit.PEModuleBuilder)compilation.CreateModuleBuilder(
                    emitOptions, null, null, null, null, null, bag, CancellationToken.None);
                if (module != null)
                {
                    module.BodySink = sink;
                    compilation.CompileMethods(module, emittingPdb: false, bag, filterOpt: null, CancellationToken.None);
                }

                // Rust's match on an enum with data: this check replaces Roslyn's CS8509 for those switches.
                var unionSwitches = new HashSet<SyntaxNode>();
                if (options.IsUserTree != null)
                {
                    foreach (var tree in compilation.SyntaxTrees)
                    {
                        if (!options.IsUserTree(tree)) continue;
                        foreach (var (node, union, missing) in UnionExhaustiveness.Check(compilation, tree))
                        {
                            unionSwitches.Add(node);
                            if (missing.Count == 0) continue;
                            var names = string.Join(", ", missing.Select(v => UnionExhaustiveness.Show(union, v)));
                            var at = node is SwitchExpressionSyntax e ? e.SwitchKeyword.GetLocation() : ((SwitchStatementSyntax)node).SwitchKeyword.GetLocation();
                            result.Diagnostics.Add(new NativeDiagnostic
                            {
                                Code = "CS8509",
                                Message = $"non-exhaustive patterns: {names} not covered",
                                Location = at,
                                Label = missing.Count == 1 ? $"pattern {names} not covered" : $"patterns {names} not covered",
                                Note = $"a switch over `{union.Name}` must handle every variant, or end with `_`",
                            });
                        }
                    }
                }

                // Rust has no null, neither in the program nor in its library: the ways C# makes one without writing `null`.
                foreach (var tree in compilation.SyntaxTrees)
                    result.Diagnostics.AddRange(NullSafety.Check(compilation, tree));

                foreach (var d in bag.ToReadOnly())
                {
                    if (d.Code == (int)ErrorCode.WRN_SwitchExpressionNotExhaustive && d.Location.SourceTree is { } where
                        && unionSwitches.Contains(where.GetRoot().FindNode(d.Location.SourceSpan, getInnermostNodeForTie: true).AncestorsAndSelf().FirstOrDefault(x => x is SwitchExpressionSyntax)))
                        continue;
                    // Every field has a value, in the program and in the core library: CS8618 is an error everywhere.
                    // Rust's match is exhaustive, so a non-exhaustive switch is an error in user code. The other nullable
                    // warnings cannot fire for a real null: every source of one (`null`, `default`, `as`, `new T[n]`)
                    // is rejected, and `T?` is an Option.
                    bool promoted = d.Severity == DiagnosticSeverity.Warning && d.Location.SourceTree is { } tree
                        && (d.Code == (int)ErrorCode.WRN_UninitializedNonNullableField
                            || d.Code == (int)ErrorCode.WRN_SwitchExpressionNotExhaustive && options.IsUserTree?.Invoke(tree) == true);
                    if (d.Severity != DiagnosticSeverity.Error && !promoted) continue;
                    var message = d.GetMessage(System.Globalization.CultureInfo.InvariantCulture);
                    result.Diagnostics.Add(new NativeDiagnostic { Code = d.Id, Message = message, Location = d.Location, Note = NullSafety.OptionNote(d.Code, message) });
                }
            }
            finally
            {
                bag.Free();
            }

            if (result.Diagnostics.Count > 0) return result;

            MirBuilder.IsUserTree = options.IsUserTree;
            OwnershipFacts.IsUserTree = options.IsUserTree;
            var ownership = new List<OwnershipDiagnostic>();
            var bodies = new Dictionary<MethodSymbol, MirBody>(Symbols.SymbolEqualityComparer.AllIgnoreOptions);
            var building = new HashSet<MethodSymbol>(Symbols.SymbolEqualityComparer.AllIgnoreOptions);
            MirBody Lookup(MethodSymbol method)
            {
                method = method.OriginalDefinition;
                if (bodies.TryGetValue(method, out var built)) return built;
                if (!sink.Bodies.TryGetValue(method, out var lowered) || !building.Add(method)) return null;
                return bodies[method] = MirBuilder.Build(method, lowered, compilation, ownership, Lookup);
            }

            foreach (var method in sink.Bodies.Keys)
            {
                // Anonymous types are built from their fields; Roslyn's template members stay unused.
                if (method.ContainingType is AnonymousTypeManager.AnonymousTypeTemplateSymbol) continue;
                if (OwnershipFacts.IsGeneratedRecordMember(method)) continue;
                Lookup(method);
            }

            if (options.MirOutputPath != null)
            {
                bool User(MirBody b) => b.Syntax?.SyntaxTree is { } t && (options.IsUserTree?.Invoke(t) ?? true);
                File.WriteAllText(options.MirOutputPath, string.Join("\n", bodies.Values.Where(User).Select(b => b.ToString())));
            }

            if (options.IsUserTree != null)
                foreach (var tree in compilation.SyntaxTrees)
                    if (!options.IsUserTree(tree)) RejectExceptions(tree, ownership, onlyThrow: true);
                    else
                    {
                        RejectExceptions(tree, ownership);
                        CheckCopyTypes(compilation, tree, ownership);
                        RejectInheritance(compilation, tree, ownership);
                        RejectFixedStrings(compilation, tree, ownership);
                    }

            if (options.BorrowCheck)
                foreach (var body in bodies.Values)
                    BorrowChecker.Check(body, ownership);

            if (options.IsUserTree != null)
                foreach (var body in bodies.Values)
                    if (body.Syntax?.SyntaxTree is { } tree && options.IsUserTree(tree))
                    {
                        CheckLibraryBoundary(body, options.IsUserTree, ownership);
                        if (options.BorrowCheck) MutabilityChecker.Check(body, ownership);
                    }

            var reported = new HashSet<(ErrorCode, Location)>();
            foreach (var d in ownership.OrderBy(x => x.Location.SourceTree?.FilePath).ThenBy(x => x.Location.SourceSpan.Start))
            {
                if (!reported.Add((d.Code, d.Location))) continue;

                var nd = new NativeDiagnostic
                {
                    Code = "CS" + ((int)d.Code).ToString("D4"),
                    Message = d.Message,
                    Location = d.Location,
                    Label = d.Label,
                    Note = d.Note
                };
                foreach (var (l, t) in d.Secondary) nd.Secondary.Add(new NativeLabel { Location = l, Text = t });
                result.Diagnostics.Add(nd);
            }

            if (result.Diagnostics.Count > 0) return result;

            var entry = compilation.GetEntryPointAndDiagnostics(CancellationToken.None)?.MethodSymbol;
            if (entry is null)
            {
                result.Diagnostics.Add(new NativeDiagnostic { Code = "CS5001", Message = "program has no entry point" });
                return result;
            }

            var errors = new List<string>();
            var backend = new LlvmBackend(compilation, bodies, errors) { Sanitize = options.Sanitize, SanitizeThreads = options.SanitizeThreads, IsUserTree = options.IsUserTree };
            string ir = backend.Generate(entry);
            ir += "\n!0 = !{!\"branch_weights\", i32 1, i32 100000}\n";

            // Some rules can only be decided on closed types, so checking includes monomorphization.
            if (options.CheckOnly)
            {
                var located = new HashSet<(string, Location)>();
                foreach (var d in backend.Located)
                    if (located.Add((d.Code, d.Location))) result.Diagnostics.Add(d);
                result.Success = result.Diagnostics.Count == 0;
                return result;
            }

            string llPath = options.LlvmOutputPath ?? options.OutputPath + ".ll";
            File.WriteAllText(llPath, ir);

            foreach (var e in errors.Distinct())
                result.Diagnostics.Add(new NativeDiagnostic { Code = "CS9919", Message = "code generation: " + e });
            var seen = new HashSet<(string, Location)>();
            foreach (var d in backend.Located)
                if (seen.Add((d.Code, d.Location))) result.Diagnostics.Add(d);
            if (result.Diagnostics.Count > 0) return result;

            var clang = new ProcessStartInfo(options.Clang) { RedirectStandardError = true, RedirectStandardOutput = true };
            // Sanitized builds stay unoptimized: LLVM would otherwise delete the very bugs we look for,
            // since it may drop unused allocations and fold reads of freed memory.
            int level = options.Sanitize || options.SanitizeThreads ? 0 : options.OptimizationLevel;
            foreach (var a in new[] { "-x", "ir", llPath, "-O" + level, "-Wno-override-module", "-o", options.OutputPath, "-lm" })
                clang.ArgumentList.Add(a);
            if (options.Sanitize) clang.ArgumentList.Add("-fsanitize=address");
            if (options.SanitizeThreads) clang.ArgumentList.Add("-fsanitize=thread");
            if (options.Sanitize || options.SanitizeThreads) clang.ArgumentList.Add("-g");
            clang.ArgumentList.Add("-pthread");
            using (var p = Process.Start(clang))
            {
                var stderr = p.StandardError.ReadToEnd();
                p.WaitForExit();
                if (p.ExitCode != 0)
                {
                    result.Diagnostics.Add(new NativeDiagnostic { Code = "CS9919", Message = "clang failed: " + stderr });
                    return result;
                }
            }

            if (options.LlvmOutputPath is null) File.Delete(llPath);
            result.Success = true;
            return result;
        }
    }
}
