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
                var names = new List<string>();
                foreach (var r in def.DeclaringSyntaxReferences)
                {
                    if (r.GetSyntax() is not TypeDeclarationSyntax decl) continue;
                    names = decl.TypeParameterList is { } list ? InTrivia(list.LessThanToken.TrailingTrivia) : ListInTrivia(decl.Identifier.TrailingTrivia);
                    if (names.Count > 0) break;
                }
                // After the written lifetimes, one implicit slot per type parameter: the lifetime of what
                // the type holds as that parameter, as Rust's Vec<&'a T> carries 'a in its T.
                // A nested type (an enum's variant) also holds its containing types' parameters.
                foreach (var tp in AllTypeParameters((NamedTypeSymbol)def))
                    if (OwnershipFacts.IsParametric(tp)) names.Add(OwnershipFacts.TypeParameterLifetime(tp));
                return names.ToImmutableArray();
            });
        }

        /// <summary>
        /// The lifetimes a type's declaration writes, read from syntax alone: what the binder checks a
        /// type's lifetime arguments against (CS9939), before any symbol is bound.
        /// </summary>
        public static int WrittenOnly(TypeSymbol t)
        {
            if (t is not NamedTypeSymbol n) return 0;
            foreach (var r in n.OriginalDefinition.DeclaringSyntaxReferences)
                if (r.GetSyntax() is TypeDeclarationSyntax decl
                    && (decl.TypeParameterList is { } list ? InTrivia(list.LessThanToken.TrailingTrivia) : ListInTrivia(decl.Identifier.TrailingTrivia)) is { Count: > 0 } names)
                    return names.Count;
            return 0;
        }

        /// <summary>A type's parameters with those of its containing types first, as C# nests them.</summary>
        private static List<TypeParameterSymbol> AllTypeParameters(NamedTypeSymbol n)
        {
            var all = n.ContainingType is { } outer ? AllTypeParameters(outer) : new List<TypeParameterSymbol>();
            all.AddRange(n.TypeParameters);
            return all;
        }

        /// <summary>A type's arguments with those of its containing types first, matching <see cref="AllTypeParameters"/>.</summary>
        private static List<TypeSymbol> AllTypeArguments(NamedTypeSymbol n)
        {
            var all = n.ContainingType is { } outer ? AllTypeArguments(outer) : new List<TypeSymbol>();
            all.AddRange(n.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics.Select(a => a.Type));
            return all;
        }

        /// <summary>How many of a type's slots are written lifetimes; the rest belong to its type parameters.</summary>
        public static int WrittenCount(TypeSymbol t)
            => Declared(t).Count(n => !n.StartsWith("'#T:", System.StringComparison.Ordinal));

        /// <summary>
        /// The lifetime a type argument brings into an implicit slot: a type parameter's own, 'static for
        /// a type that cannot hold borrows, a single written lifetime (`Ref&lt;'a, int&gt;`), or none (null).
        /// </summary>
        public static string TypeArgumentLifetime(TypeSymbol argument, TypeSyntax syntax)
        {
            var parametric = OwnershipFacts.ParametricIn(argument);
            if (parametric.Count == 1) return OwnershipFacts.TypeParameterLifetime(parametric[0]);
            if (parametric.Count > 1) return null;
            if (!OwnershipFacts.IsBorrowHolder(argument) && !OwnershipFacts.CarriesBorrowsOrSlots(argument)) return "'static";
            if (syntax is not null && Nested(syntax) is { Count: > 0 } written && written.All(w => w == written[0]) && written[0] != "'_") return written[0];
            return null;
        }

        private static TypeSyntax TypeArgumentSyntax(TypeSyntax syntax, int k)
        {
            while (true)
            {
                switch (syntax)
                {
                    case RefTypeSyntax r: syntax = r.Type; continue;
                    case ScopedTypeSyntax s: syntax = s.Type; continue;
                    case QualifiedNameSyntax q: syntax = q.Right; continue;
                    case AliasQualifiedNameSyntax a: syntax = a.Name; continue;
                    case GenericNameSyntax g: return k < g.TypeArgumentList.Arguments.Count ? g.TypeArgumentList.Arguments[k] : null;
                    default: return null;
                }
            }
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
            int writtenCount = WrittenCount(type);
            var slots = new string[declared.Length];
            for (int k = 0; k < slots.Length; k++)
            {
                if (k < writtenCount)
                {
                    slots[k] = k < written.Count && written[k] != "'_" ? written[k] : "'#elided" + position + "." + k;
                    continue;
                }
                // An implicit slot takes the lifetime of the type argument: Stack<T> gives T's, Stack<int> 'static.
                var all = AllTypeParameters(((NamedTypeSymbol)type).OriginalDefinition);
                var args = AllTypeArguments((NamedTypeSymbol)type);
                // Only parametric parameters have a slot: find the argument for slot k.
                int i = -1;
                for (int seen = writtenCount - 1, j = 0; j < all.Count; j++)
                    if (OwnershipFacts.IsParametric(all[j]) && ++seen == k) { i = j; break; }
                int own = i - (all.Count - ((NamedTypeSymbol)type).Arity);
                string name = i >= 0 && i < args.Count ? TypeArgumentLifetime(args[i], syntax is null || own < 0 ? null : TypeArgumentSyntax(syntax, own)) : null;
                slots[k] = name ?? "'#elided" + position + "." + k;
            }
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
            // A field that holds one of the type's parameters (`List<T> _items`) borrows for its slot.
            var parametric = OwnershipFacts.ParametricIn(field.OriginalDefinition.Type);
            if (parametric.Count == 1) return declared.IndexOf(OwnershipFacts.TypeParameterLifetime(parametric[0]));
            return -1;
        }

        /// <summary>The type as a field's declaration writes it, with its lifetimes.</summary>
        public static TypeSyntax FieldTypeSyntax(FieldSymbol field)
        {
            foreach (var r in field.OriginalDefinition.DeclaringSyntaxReferences)
                if (r.GetSyntax() is VariableDeclaratorSyntax { Parent: VariableDeclarationSyntax decl }) return decl.Type;
            return null;
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

        private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<MethodSymbol, NamedTypeSymbol> s_lambdaTargets = new();

        /// <summary>The binder records the delegate type each lambda was converted to.</summary>
        public static void RecordLambdaTarget(MethodSymbol lambda, NamedTypeSymbol delegateType)
        {
            if (lambda is not null && delegateType is not null) s_lambdaTargets.AddOrUpdate(lambda, delegateType);
        }

        /// <summary>The delegate type a closure body's lambda was converted to, or null.</summary>
        public static NamedTypeSymbol TargetDelegate(MethodSymbol closureBody)
            => closureBody.OriginalDefinition is SynthesizedClosureMethod { LambdaOrLocalFunction: { } lambda } && s_lambdaTargets.TryGetValue(lambda, out var t) ? t : null;

        /// <summary>
        /// Whether a delegate type declares lifetimes, as in <c>delegate Ref&lt;'a, int&gt; Id&lt;'a&gt;(Ref&lt;'a, int&gt; x)</c>,
        /// Rust's <c>for&lt;'a&gt; Fn(&amp;'a i32) -&gt; &amp;'a i32</c>: they belong to each call, not to the delegate value.
        /// </summary>
        public static bool DelegateDeclaresLifetimes(TypeSymbol t)
        {
            if (t is not NamedTypeSymbol { TypeKind: TypeKind.Delegate } n) return false;
            foreach (var r in n.OriginalDefinition.DeclaringSyntaxReferences)
                if (r.GetSyntax() is DelegateDeclarationSyntax d
                    && (d.TypeParameterList is { } list ? InTrivia(list.LessThanToken.TrailingTrivia) : InTrivia(d.Identifier.TrailingTrivia)).Count > 0)
                    return true;
            return false;
        }

        /// <summary>The lifetimes of a declaration's list `&lt;'a, 'b&gt;` alone, not of a `where` clause after it.</summary>
        private static List<string> ListInTrivia(SyntaxTriviaList trivia)
        {
            var names = new List<string>();
            bool inside = false;
            foreach (var t in trivia)
                if (t.IsKind(SyntaxKind.SkippedTokensTrivia))
                    foreach (var token in ((SkippedTokensTriviaSyntax)t.GetStructure()).Tokens)
                    {
                        if (token.IsKind(SyntaxKind.LessThanToken)) inside = true;
                        else if (token.IsKind(SyntaxKind.GreaterThanToken)) return names;
                        else if (inside && token.IsKind(SyntaxKind.LifetimeToken)) names.Add(token.ValueText);
                    }
            return names;
        }

        /// <summary>
        /// A type's `where T : 'a` and `where 'a : 'b` clauses, as (longer, shorter): they hold in all its
        /// methods. A type parameter stands for its lifetime 'T.
        /// </summary>
        public static List<(string Longer, string Shorter)> TypeBounds(NamedTypeSymbol type)
        {
            var bounds = new List<(string, string)>();
            var def = type.OriginalDefinition;
            foreach (var r in def.DeclaringSyntaxReferences)
            {
                if (r.GetSyntax() is not TypeDeclarationSyntax decl) continue;
                var trivia = decl.BaseList?.GetTrailingTrivia() ?? decl.TypeParameterList?.GetTrailingTrivia() ?? decl.Identifier.TrailingTrivia;
                var names = new List<string>();
                bool inClause = false;
                foreach (var t in trivia)
                    if (t.IsKind(SyntaxKind.SkippedTokensTrivia))
                        foreach (var token in ((SkippedTokensTriviaSyntax)t.GetStructure()).Tokens)
                        {
                            if (token.ContextualKind() == SyntaxKind.WhereKeyword || token.ValueText == "where") { inClause = true; continue; }
                            if (!inClause) continue;
                            if (token.IsKind(SyntaxKind.LifetimeToken)) names.Add(token.ValueText);
                            else if (token.IsKind(SyntaxKind.IdentifierToken) && def.TypeParameters.FirstOrDefault(p => p.Name == token.ValueText) is { } tp)
                                names.Add(OwnershipFacts.IsParametric(tp) ? OwnershipFacts.TypeParameterLifetime(tp) : "'static");
                        }
                for (int i = 0; i + 1 < names.Count; i += 2) bounds.Add((names[i], names[i + 1]));
            }
            return bounds;
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
