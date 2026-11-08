// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Microsoft.CodeAnalysis.CSharp.Ownership
{
    /// <summary>
    /// Rust has no null: a missing value is Option&lt;T&gt;::None. The binder rejects `null`, `!`, `??` and `?.`
    /// in user code; this pass catches the ways C# makes a null without writing one: `default`, `new T[n]`
    /// and the zeroing `new S()` of a struct that holds references.
    /// </summary>
    internal static class NullSafety
    {
        private const string OptionHint = "A value that may be missing is an Option<T>: write `None`. In generic code `T.Default()` with `where T : IDefault<T>` is Rust's Default";

        public static IEnumerable<NativeDiagnostic> Check(CSharpCompilation compilation, SyntaxTree tree)
        {
            // References are never null, so there is no nullable context to switch.
            foreach (var directive in tree.GetRoot().DescendantTrivia().Select(t => t.GetStructure()).OfType<NullableDirectiveTriviaSyntax>())
                yield return new NativeDiagnostic
                {
                    Code = "CS" + ((int)ErrorCode.ERR_OwnNoNullableContext).ToString(CultureInfo.InvariantCulture),
                    Message = ErrorFacts.GetMessage(ErrorCode.ERR_OwnNoNullableContext, CultureInfo.InvariantCulture),
                    Location = directive.GetLocation(),
                    Label = "remove this line",
                };

            SemanticModel model = null;
            foreach (var node in tree.GetRoot().DescendantNodes())
            {
                if (node is InvocationExpressionSyntax take)
                {
                    // Rust's mem::take needs T: Default. Mem.Take leaves a zeroed value behind, which for a reference is null.
                    model ??= compilation.GetSemanticModel(tree);
                    if (model.GetSymbolInfo(take).Symbol is IMethodSymbol { Name: "Take", TypeArguments: [var taken], ContainingType: { Name: "Mem", ContainingNamespace: { Name: "System", ContainingNamespace.IsGlobalNamespace: true } } }
                        && MayHoldNull(taken))
                        yield return Report(take, "the slot `Mem.Take` leaves behind", taken,
                            "Move the value out with `list.RemoveAt(i)` or `Pop()`, swap in a new one with `Mem.Replace(ref slot, value)`, or keep it in an Option<T> and call its `Take()`", "leaves a zeroed value behind");
                    continue;
                }
                if (node is LiteralExpressionSyntax { RawKind: (int)SyntaxKind.NullLiteralExpression } nullLiteral)
                {
                    if (!InUnsafe(nullLiteral)) continue; // the binder rejects it everywhere else
                    // Unsafe code keeps null pointers (Rust's ptr::null), but nothing else.
                    model ??= compilation.GetSemanticModel(tree);
                    if (model.GetTypeInfo(nullLiteral).ConvertedType is { } target and not (IPointerTypeSymbol or IFunctionPointerTypeSymbol) && target.TypeKind != TypeKind.Error)
                        yield return new NativeDiagnostic
                        {
                            Code = "CS" + ((int)ErrorCode.ERR_OwnNoNull).ToString(CultureInfo.InvariantCulture),
                            Message = ErrorFacts.GetMessage(ErrorCode.ERR_OwnNoNull, CultureInfo.InvariantCulture),
                            Location = nullLiteral.GetLocation(),
                            Label = "only a pointer can be null, even in unsafe code",
                        };
                    continue;
                }
                if (node is not (DefaultExpressionSyntax or LiteralExpressionSyntax { RawKind: (int)SyntaxKind.DefaultLiteralExpression }
                    or ArrayCreationExpressionSyntax or BaseObjectCreationExpressionSyntax)) continue;
                model ??= compilation.GetSemanticModel(tree);
                if (Find(model, node) is { } d) yield return d;
            }
        }

        private static NativeDiagnostic Find(SemanticModel model, SyntaxNode node)
        {
            switch (node)
            {
                case DefaultExpressionSyntax or LiteralExpressionSyntax:
                    {
                        var info = model.GetTypeInfo(node);
                        var type = info.ConvertedType ?? info.Type;
                        if (type is null || type.TypeKind == TypeKind.Error || !MayHoldNull(type)) return null;
                        return Report(node, "`default`", type, OptionHint, "a zeroed value");
                    }
                case ArrayCreationExpressionSyntax { Initializer: null } array:
                    {
                        bool empty = array.Type.RankSpecifiers.SelectMany(r => r.Sizes)
                            .Any(s => model.GetConstantValue(s) is { HasValue: true, Value: 0 });
                        if (empty || model.GetTypeInfo(array).Type is not IArrayTypeSymbol { ElementType: var element } || !MayHoldNull(element)) return null;
                        return Report(array, "every element of this array", element,
                            $"List the elements (`new {element.ToDisplayString()}[] {{ ... }}`), or start a List<{element.ToDisplayString()}> and Add to it", "filled with zeroes");
                    }
                case BaseObjectCreationExpressionSyntax creation:
                    {
                        // `new S()` without a constructor of S's own zeroes every field.
                        if (model.GetSymbolInfo(creation).Symbol is not IMethodSymbol { IsImplicitlyDeclared: true, Parameters.Length: 0, ContainingType: { IsValueType: true } type })
                            return null;
                        var set = new HashSet<string>(creation.Initializer?.Expressions.OfType<AssignmentExpressionSyntax>()
                            .Select(a => (a.Left as IdentifierNameSyntax)?.Identifier.ValueText) ?? Enumerable.Empty<string>());
                        var missing = type.GetMembers().OfType<IFieldSymbol>()
                            .Where(f => !f.IsStatic && MayHoldNull(f.Type))
                            .Select(f => f.AssociatedSymbol?.Name ?? f.Name)
                            .FirstOrDefault(name => !set.Contains(name));
                        if (missing is null) return null;
                        return Report(creation, $"`{missing}` of `new {type.Name}()`", type,
                            $"Give `{type.Name}` a constructor that sets `{missing}`, or set it here: `new {type.Name}() {{ {missing} = ... }}`", "fields left zeroed");
                    }
            }
            return null;
        }

        private static bool InUnsafe(SyntaxNode node)
            => node.AncestorsAndSelf().Any(n => n is UnsafeStatementSyntax
                || n is MemberDeclarationSyntax m && m.Modifiers.Any(SyntaxKind.UnsafeKeyword)
                || n is LocalFunctionStatementSyntax f && f.Modifiers.Any(SyntaxKind.UnsafeKeyword));

        /// <summary>A hint for Roslyn's own errors on an Option: a value never turns into one, or out of one, by itself.</summary>
        internal static string OptionNote(int code, string message)
        {
            const string option = "System.Option<";
            if (code == (int)ErrorCode.ERR_NoImplicitConv || code == (int)ErrorCode.ERR_NoImplicitConvCast)
            {
                int to = message.LastIndexOf(" to '", System.StringComparison.Ordinal);
                if (to >= 0 && message.IndexOf(option, to, System.StringComparison.Ordinal) == to + 5)
                    return "a value is not an Option by itself: wrap it with `Some(x)`. `T?` is a short way to write Option<T>";
                if (message.Contains("type '" + option))
                    return "an Option<T> may be None: match `Some(var v)`, or call `Unwrap()` (it panics on None) or `UnwrapOr(x)`";
            }
            if ((code == (int)ErrorCode.ERR_GenericConstraintNotSatisfiedRefType || code == (int)ErrorCode.ERR_GenericConstraintNotSatisfiedValType)
                && message.Contains("IDefault<"))
                return "this needs Rust's Default (`IDefault<T>`), so no null is left behind. To move a value out of a slot, use `list.RemoveAt(i)` or `Pop()`, `Mem.Replace(ref slot, value)`, or keep it in an Option<T> and call its `Take()`";
            if (code == (int)ErrorCode.WRN_UninitializedNonNullableField)
                return "every field needs a value: set it in each constructor or give it an initializer. A field that may have none is an Option<T>: declare it `T?` and start it at `None`";
            if (code == (int)ErrorCode.ERR_NoSuchMemberOrExtension && message.StartsWith("'Option<", System.StringComparison.Ordinal))
                return "an Option<T> gives its value only after a check: `if (o is Some(var v))`, a switch with `Some(var v)` and `None`, or `Unwrap()`";
            return null;
        }

        /// <summary>Whether a zeroed value of the type contains a null: a reference, or a pointer inside a struct.</summary>
        internal static bool MayHoldNull(ITypeSymbol type, HashSet<ITypeSymbol> seen = null)
        {
            switch (type)
            {
                case IPointerTypeSymbol or IFunctionPointerTypeSymbol:
                    return false; // raw pointers are unsafe code's own business
                case ITypeParameterSymbol p:
                    return !p.HasUnmanagedTypeConstraint;
                case INamedTypeSymbol { Name: "Option" or "NoneValue", ContainingNamespace: { Name: "System", ContainingNamespace.IsGlobalNamespace: true } }:
                    return false; // the zero of an Option is None
                case INamedTypeSymbol { Name: "str", Arity: 0, ContainingNamespace: { Name: "System", ContainingNamespace.IsGlobalNamespace: true } }:
                    return false; // the zero of a str is the empty slice, Rust's `<&str>::default()`
                case INamedTypeSymbol { IsValueType: true } n:
                    if (n.SpecialType != SpecialType.None || n.TypeKind == TypeKind.Enum) return false;
                    seen ??= new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default);
                    if (!seen.Add(n)) return false;
                    return n.GetMembers().OfType<IFieldSymbol>().Any(f => !f.IsStatic && (f.Type is IPointerTypeSymbol || MayHoldNull(f.Type, seen)));
                default:
                    return type.IsReferenceType;
            }
        }

        private static NativeDiagnostic Report(SyntaxNode at, string what, ITypeSymbol type, string hint, string label)
        {
            var name = type.ToDisplayString(SymbolDisplayFormat.MinimallyQualifiedFormat);
            return new NativeDiagnostic
            {
                Code = "CS" + ((int)ErrorCode.ERR_OwnNullDefault).ToString(CultureInfo.InvariantCulture),
                Message = string.Format(CultureInfo.InvariantCulture, ErrorFacts.GetMessage(ErrorCode.ERR_OwnNullDefault, CultureInfo.InvariantCulture), what, name, hint),
                Location = at.GetLocation(),
                Label = label,
            };
        }
    }
}
