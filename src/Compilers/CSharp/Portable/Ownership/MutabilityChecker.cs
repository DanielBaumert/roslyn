// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.
// See the LICENSE file in the project root for more information.

// RustSharp: Rust's rule that a binding is immutable unless it says `mut`. Only user code is checked;
// the core library is written without `mut`.

using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis.CSharp.Symbols;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Microsoft.CodeAnalysis.CSharp.Ownership
{
    internal static class MutabilityChecker
    {
        /// <summary>
        /// The lexer keeps `mut` as trivia in front of the declared type, which makes it work in every
        /// place a type can start a declaration.
        /// </summary>
        public static bool HasMut(SyntaxNode declarator, out SyntaxToken site)
        {
            site = default;
            for (var n = declarator; n != null; n = n.Parent)
            {
                switch (n)
                {
                    case VariableDeclarationSyntax v: return Marked(v.Type.GetFirstToken(), out site);
                    case ForEachStatementSyntax f: return Marked(f.Type.GetFirstToken(), out site);
                    case ForEachVariableStatementSyntax f: return Marked(f.Variable.GetFirstToken(), out site);
                    case DeclarationExpressionSyntax d: return Marked(d.Type.GetFirstToken(), out site);
                    case DeclarationPatternSyntax d: return Marked(d.Type.GetFirstToken(), out site);
                    case VarPatternSyntax p: return Marked(p.GetFirstToken(), out site);
                    case CatchDeclarationSyntax c: return Marked(c.Type.GetFirstToken(), out site);
                    case ParameterSyntax p:
                        return Marked(p.Type is null || p.Modifiers.Count > 0 ? p.GetFirstToken() : p.Type.GetFirstToken(), out site);
                    case StatementSyntax:
                    case MemberDeclarationSyntax:
                        return false;
                }
            }
            return false;
        }

        private static bool Marked(SyntaxToken token, out SyntaxToken site)
        {
            site = token;
            foreach (var t in token.LeadingTrivia)
                if (t.IsKind(SyntaxKind.SingleLineCommentTrivia) && t.ToString() == "mut") return true;
            return false;
        }

        public static void Check(MirBody body, List<OwnershipDiagnostic> diagnostics)
        {
            var seen = new HashSet<(ErrorCode, Location)>();
            void Report(ErrorCode code, string text, string label, SyntaxToken site, SyntaxNode syntax)
            {
                var location = (syntax ?? body.Syntax).Location;
                if (!seen.Add((code, location))) return;
                var at = site.GetLocation()?.GetLineSpan().StartLinePosition;
                diagnostics.Add(new OwnershipDiagnostic
                {
                    Code = code,
                    Message = text,
                    Location = location,
                    Label = label,
                    Note = at is { } p ? $"declare it with `mut` at line {p.Line + 1}, column {p.Character + 1}" : null,
                });
            }

            // Forward analysis: which immutable variables may already hold a value here.
            bool closure = OwnershipFacts.IsClosureBody(body.Method);
            var entry = new Dictionary<BasicBlock, HashSet<object>>();
            var start = new HashSet<object>();
            foreach (var l in body.Locals)
                if (l.Immutable && l.Kind == LocalKind.Arg) start.Add(l);
            entry[body.Blocks[0]] = start;
            var work = new Queue<BasicBlock>();
            work.Enqueue(body.Blocks[0]);
            var visited = new HashSet<BasicBlock>();

            while (work.Count > 0)
            {
                var block = work.Dequeue();
                visited.Add(block);
                var state = new HashSet<object>(entry[block]);
                foreach (var s in block.Statements)
                {
                    switch (s)
                    {
                        case StorageDeadStmt d:
                            state.Remove(body.Locals[d.Local]);
                            break;
                        case AssignStmt a:
                            if (a.Value is RefRv { Mode: RefMode.Mut } r && !IsReborrow(r.Place) && Resolve(r.Place, out var bv) && !IsOutArgument(a.Syntax) && !Declares(a.Syntax))
                                Report(ErrorCode.ERR_OwnBorrowImmutable, $"`{bv.Name}` is not declared `mut`, so it cannot change", "cannot borrow this as mutable, the variable is not `mut`", bv.Site, a.Syntax);
                            if (Resolve(a.Dest, out var v))
                            {
                                if (!v.Whole)
                                {
                                    if (!Declares(a.Syntax))
                                        Report(ErrorCode.ERR_OwnBorrowImmutable, $"`{v.Name}` is not declared `mut`, so it cannot change", "cannot change this, the variable is not `mut`", v.Site, a.Syntax);
                                }
                                else if ((!state.Add(v.Key) || closure && v.Key is Symbol) && !Declares(a.Syntax))
                                {
                                    Report(ErrorCode.ERR_OwnAssignImmutable, $"cannot assign twice to immutable variable `{v.Name}`", "cannot assign twice to an immutable variable", v.Site, a.Syntax);
                                }
                            }
                            break;
                    }
                }

                foreach (var next in block.Term?.Successors ?? Enumerable.Empty<BasicBlock>())
                {
                    if (entry.TryGetValue(next, out var known))
                    {
                        int before = known.Count;
                        known.UnionWith(state);
                        if (known.Count != before || !visited.Contains(next)) work.Enqueue(next);
                    }
                    else
                    {
                        entry[next] = new HashSet<object>(state);
                        work.Enqueue(next);
                    }
                }
            }

            // Writing through a RefMut changes what it points at, not the RefMut: Rust's `node.x = 1` with
            // `node: &mut T` needs no `mut node`.
            bool IsReborrow(Place p)
                => p.Static is null && p.Projs.Length == 0 && body.Locals[p.Local].Type is { IsRef: false, Type: NamedTypeSymbol { Name: "RefMut", Arity: 1 } t }
                    && OwnershipFacts.IsReference(t);

            // The immutable variable behind a place: a local, or a local captured by a closure.
            bool Resolve(Place p, out (object Key, string Name, SyntaxToken Site, bool Whole) found)
            {
                found = default;
                if (p.Static is not null) return false;

                for (int i = p.Projs.Length - 1; i >= 0; i--)
                {
                    if (p.Projs[i] is FieldProj { Field: var f } && f.OriginalDefinition is LambdaCapturedVariable { CapturedSymbol: { } captured })
                    {
                        SyntaxNode declarator = captured switch
                        {
                            Symbols.LocalSymbol { IsCompilerGenerated: false } l => l.GetDeclaratorSyntax(),
                            Symbols.ParameterSymbol { IsThis: false } a => a.GetNonNullSyntaxNode() as ParameterSyntax,
                            _ => null,
                        };
                        if (declarator is null || HasMut(declarator, out var site) || site == default) return false;
                        found = (captured, captured.Name, site, i == p.Projs.Length - 1);
                        return true;
                    }
                }

                var local = body.Locals[p.Local];
                if (!local.Immutable) return false;
                if (p.Projs.Length > 0 && local.Type.IsRef) return false; // only the reference is immutable
                found = (local, local.Name, local.MutSite, p.Projs.Length == 0);
                return true;
            }
        }

        /// <summary>The first value of a variable, even when a loop runs this code again.</summary>
        private static bool Declares(SyntaxNode syntax) => syntax is VariableDeclaratorSyntax or SingleVariableDesignationSyntax
            or ForEachStatementSyntax or ForEachVariableStatementSyntax or DeclarationPatternSyntax or VarPatternSyntax
            or DeclarationExpressionSyntax or CatchDeclarationSyntax or ParenthesizedVariableDesignationSyntax
            or AnonymousFunctionExpressionSyntax; // filling a closure; its body reports what it changes

        private static bool IsOutArgument(SyntaxNode syntax)
        {
            for (var n = syntax; n is ExpressionSyntax or ArgumentSyntax; n = n.Parent)
                if (n is ArgumentSyntax a) return a.RefKindKeyword.IsKind(SyntaxKind.OutKeyword);
            return false;
        }
    }
}
