// RustSharp: Rust's match on an enum with data must cover every variant. Roslyn sees an open class
// hierarchy and always asks for `_`; for these enums the variants are known, so this check decides.
using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Microsoft.CodeAnalysis.CSharp.Ownership
{
    internal static class UnionExhaustiveness
    {
        public static bool IsUnion(ITypeSymbol type)
            => type is INamedTypeSymbol n && n.OriginalDefinition.DeclaringSyntaxReferences.Any(r => UnionSyntax.IsUnion(r.GetSyntax()));

        private static bool IsVariant(INamedTypeSymbol t)
            => t.OriginalDefinition.DeclaringSyntaxReferences.Any(r => UnionSyntax.IsVariant(r.GetSyntax()));

        /// <summary>Every switch over an enum with data, with the variants it does not cover.</summary>
        public static IEnumerable<(SyntaxNode Switch, INamedTypeSymbol Union, List<INamedTypeSymbol> Missing)> Check(Compilation compilation, SyntaxTree tree)
        {
            SemanticModel model = null;
            foreach (var node in tree.GetRoot().DescendantNodes())
            {
                ExpressionSyntax governing = node switch
                {
                    SwitchExpressionSyntax e => e.GoverningExpression,
                    SwitchStatementSyntax s => s.Expression,
                    _ => null,
                };
                if (governing is null) continue;
                model ??= compilation.GetSemanticModel(tree);
                if (model.GetTypeInfo(governing).Type is not INamedTypeSymbol union || !IsUnion(union)) continue;

                var variants = union.GetTypeMembers().Where(IsVariant).ToList();
                var covered = new HashSet<INamedTypeSymbol>(SymbolEqualityComparer.Default);
                bool all = false;

                void Cover(PatternSyntax pattern)
                {
                    switch (pattern)
                    {
                        case DiscardPatternSyntax:
                        case VarPatternSyntax:
                            all = true;
                            break;
                        case ParenthesizedPatternSyntax p:
                            Cover(p.Pattern);
                            break;
                        case BinaryPatternSyntax { RawKind: (int)SyntaxKind.OrPattern } b:
                            Cover(b.Left);
                            Cover(b.Right);
                            break;
                        case DeclarationPatternSyntax d:
                            CoverType(d.Type, irrefutable: true);
                            break;
                        case TypePatternSyntax t:
                            CoverType(t.Type, irrefutable: true);
                            break;
                        case ConstantPatternSyntax c:
                            if (model.GetSymbolInfo(c.Expression).Symbol is INamedTypeSymbol) CoverType(c.Expression, irrefutable: true);
                            break;
                        case RecursivePatternSyntax r:
                            bool rest = (r.PositionalPatternClause?.Subpatterns.All(s => Irrefutable(s.Pattern)) ?? true)
                                && (r.PropertyPatternClause?.Subpatterns.All(s => Irrefutable(s.Pattern)) ?? true);
                            if (r.Type is null) { if (rest) all = true; }
                            else CoverType(r.Type, rest);
                            break;
                    }
                }

                void CoverType(ExpressionSyntax typeSyntax, bool irrefutable)
                {
                    if (!irrefutable) return;
                    var t = model.GetTypeInfo(typeSyntax).Type ?? model.GetSymbolInfo(typeSyntax).Symbol as ITypeSymbol;
                    if (t is null) return;
                    if (SymbolEqualityComparer.Default.Equals(t.OriginalDefinition, union.OriginalDefinition)) all = true;
                    else if (t is INamedTypeSymbol n) covered.Add(n.OriginalDefinition);
                }

                if (node is SwitchExpressionSyntax expression)
                {
                    foreach (var arm in expression.Arms)
                        if (arm.WhenClause is null) Cover(arm.Pattern);
                }
                else
                {
                    foreach (var section in ((SwitchStatementSyntax)node).Sections)
                        foreach (var label in section.Labels)
                        {
                            if (label is DefaultSwitchLabelSyntax) all = true;
                            else if (label is CasePatternSwitchLabelSyntax p && p.WhenClause is null) Cover(p.Pattern);
                            else if (label is CaseSwitchLabelSyntax c && model.GetSymbolInfo(c.Value).Symbol is INamedTypeSymbol) CoverType(c.Value, irrefutable: true);
                        }
                }

                var missing = all ? new List<INamedTypeSymbol>() : variants.Where(v => !covered.Contains(v.OriginalDefinition)).ToList();
                yield return (node, union, missing);
            }
        }

        /// <summary>A pattern that matches whatever the field holds.</summary>
        private static bool Irrefutable(PatternSyntax p) => p switch
        {
            DiscardPatternSyntax or VarPatternSyntax => true,
            DeclarationPatternSyntax { Type: IdentifierNameSyntax { IsVar: true } } => true,
            ParenthesizedPatternSyntax inner => Irrefutable(inner.Pattern),
            RecursivePatternSyntax { Type: null } r => (r.PositionalPatternClause?.Subpatterns.All(s => Irrefutable(s.Pattern)) ?? true)
                && (r.PropertyPatternClause?.Subpatterns.All(s => Irrefutable(s.Pattern)) ?? true),
            _ => false,
        };

        /// <summary>How a missing variant reads in the error, as Rust prints `Shape::Rect(..)`.</summary>
        public static string Show(INamedTypeSymbol union, INamedTypeSymbol variant)
        {
            bool positional = variant.GetMembers().OfType<IMethodSymbol>().Any(m => m.MethodKind == MethodKind.Constructor && m.Parameters.Length > 0
                && !(m.Parameters.Length == 1 && SymbolEqualityComparer.Default.Equals(m.Parameters[0].Type, variant)));
            return $"`{union.Name}.{variant.Name}{(positional ? "(..)" : "")}`";
        }
    }
}
