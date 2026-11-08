// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.
// See the LICENSE file in the project root for more information.

using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.CodeAnalysis.CSharp.Symbols;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Microsoft.CodeAnalysis.CSharp.Ownership
{
    /// <summary>
    /// RustSharp's lifetime parameters, as in <c>ref struct Pair&lt;'a, 'b&gt;</c> and <c>Pair&lt;'a, '_&gt;</c>. Lifetimes
    /// are erased before Roslyn binds, as Rust erases them before code generation: the parser keeps
    /// them as skipped tokens (behind the name, or behind the `&lt;` of a mixed list), so the type has
    /// the arity of its type parameters alone. This class reads them back from the syntax for the
    /// borrow checker, which gives a value of such a type one region per declared lifetime (a slot).
    /// </summary>
    internal static class Lifetimes
    {
        private static readonly ConcurrentDictionary<TypeSymbol, ImmutableArray<string>> s_declared = new(Symbols.SymbolEqualityComparer.AllIgnoreOptions);

        /// <summary>The lifetimes a type declares, in order: <c>['a, 'b]</c> for <c>Pair&lt;'a, 'b&gt;</c>; empty for any other type.</summary>
        public static ImmutableArray<string> Declared(TypeSymbol t)
        {
            if (t is not NamedTypeSymbol n) return ImmutableArray<string>.Empty;
            return s_declared.GetOrAdd(n.OriginalDefinition, static def =>
            {
                foreach (var r in def.DeclaringSyntaxReferences)
                {
                    if (r.GetSyntax() is not TypeDeclarationSyntax decl) continue;
                    var names = decl.TypeParameterList is { } list ? InTrivia(list.LessThanToken.TrailingTrivia) : InTrivia(decl.Identifier.TrailingTrivia);
                    if (names.Count > 0) return names.ToImmutableArray();
                }
                return ImmutableArray<string>.Empty;
            });
        }

        /// <summary>The lifetimes a method declares: <c>['a, 'b]</c> for <c>First&lt;'a, 'b&gt;</c>.</summary>
        public static List<string> Declared(MethodDeclarationSyntax m)
            => m.TypeParameterList is { } list ? InTrivia(list.LessThanToken.TrailingTrivia) : InTrivia(m.Identifier.TrailingTrivia);

        /// <summary>
        /// The lifetime arguments written in a type: <c>['a, '_]</c> for <c>in Pair&lt;'a, '_&gt;</c>. Empty when none
        /// are written, which elides all of them.
        /// </summary>
        public static List<string> Arguments(TypeSyntax syntax)
        {
            while (true)
            {
                switch (syntax)
                {
                    case RefTypeSyntax r: syntax = r.Type; continue;
                    case ScopedTypeSyntax s: syntax = s.Type; continue;
                    case QualifiedNameSyntax q: syntax = q.Right; continue;
                    case AliasQualifiedNameSyntax a: syntax = a.Name; continue;
                    case GenericNameSyntax g: return InTrivia(g.TypeArgumentList.LessThanToken.TrailingTrivia);
                    case IdentifierNameSyntax i: return InTrivia(i.Identifier.TrailingTrivia);
                    default: return new List<string>();
                }
            }
        }

        /// <summary>
        /// One lifetime name per slot of <paramref name="type"/> as written in <paramref name="syntax"/>, or
        /// null when the type declares no lifetimes. An elided or `'_` slot gets a fresh name, unique for
        /// <paramref name="position"/>, so every elided position is a lifetime of its own, as in Rust.
        /// </summary>
        public static string[] Slots(TypeSymbol type, TypeSyntax syntax, string position)
        {
            var declared = Declared(type);
            if (declared.IsEmpty) return null;
            var written = syntax is null ? new List<string>() : Arguments(syntax);
            var slots = new string[declared.Length];
            for (int k = 0; k < slots.Length; k++)
                slots[k] = k < written.Count && written[k] != "'_" ? written[k] : "'#elided" + position + "." + k;
            return slots;
        }

        /// <summary>
        /// The slot of its containing type that a field borrows for: 0 for <c>ref readonly 'a int _x</c> in
        /// <c>Pair&lt;'a, 'b&gt;</c>. -1 when the field names no declared lifetime: then what it borrows lives as
        /// long as the whole value, as before lifetime parameters.
        /// </summary>
        public static int FieldSlot(FieldSymbol field)
        {
            var declared = Declared(field.ContainingType);
            if (declared.IsEmpty) return -1;
            foreach (var r in field.OriginalDefinition.DeclaringSyntaxReferences)
            {
                if (r.GetSyntax() is not VariableDeclaratorSyntax { Parent: VariableDeclarationSyntax decl }) continue;
                string name = decl.Type is RefTypeSyntax refType && refType.LifetimeToken.ValueText is { Length: > 0 } own ? own : null;
                var args = Nested(decl.Type);
                if (name is null && args.Count > 0 && args.All(a => a == args[0])) name = args[0];
                if (name is not null) return declared.IndexOf(name);
            }
            return -1;
        }

        /// <summary>Every lifetime written anywhere in a type: <c>['a]</c> for <c>List&lt;Ref&lt;'a, int&gt;&gt;</c>.</summary>
        private static List<string> Nested(TypeSyntax syntax)
        {
            var names = new List<string>();
            foreach (var node in syntax.DescendantNodesAndSelf())
            {
                if (node is GenericNameSyntax g) names.AddRange(InTrivia(g.TypeArgumentList.LessThanToken.TrailingTrivia));
                else if (node is IdentifierNameSyntax i) names.AddRange(InTrivia(i.Identifier.TrailingTrivia));
            }
            return names;
        }

        private static List<string> InTrivia(SyntaxTriviaList trivia)
        {
            var names = new List<string>();
            foreach (var t in trivia)
                if (t.IsKind(SyntaxKind.SkippedTokensTrivia))
                    foreach (var token in ((SkippedTokensTriviaSyntax)t.GetStructure()).Tokens)
                        if (token.IsKind(SyntaxKind.LifetimeToken)) names.Add(token.ValueText);
            return names;
        }
    }
}
