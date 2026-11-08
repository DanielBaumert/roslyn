// RustSharp: Rust's enums with data, parsed into an abstract record with one sealed record per variant.
using System.Linq;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Microsoft.CodeAnalysis.CSharp
{
    internal static class UnionSyntax
    {
        /// <summary>The record that an `enum` with data became: its keyword is missing and carries `enum`.</summary>
        public static bool IsUnion(SyntaxNode node)
            => node is RecordDeclarationSyntax r && r.Keyword.IsMissing
                && r.Keyword.LeadingTrivia.Any(t => t.IsKind(SyntaxKind.SkippedTokensTrivia)
                    && ((SkippedTokensTriviaSyntax)t.GetStructure()).Tokens.Any(k => k.IsKind(SyntaxKind.EnumKeyword)));

        public static bool IsVariant(Symbols.NamedTypeSymbol type, bool unitOnly)
            => type.OriginalDefinition.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is RecordDeclarationSyntax v && IsVariant(v) && (!unitOnly || v.ParameterList is null));

        public static bool IsVariant(SyntaxNode node)
            => node is RecordDeclarationSyntax r && r.Keyword.IsMissing && r.Parent is { } parent && IsUnion(parent);
    }
}
