// RustSharp: Rust's shadowing, `var x = 1; var x = x + 1;`. Every further declaration of a name gets an
// internal name of its own (same text, different ValueText), and the uses after it follow it.
using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Microsoft.CodeAnalysis.CSharp.Ownership
{
    public static class Shadowing
    {
        public static SyntaxTree Apply(SyntaxTree tree)
        {
            var renames = new Dictionary<SyntaxToken, string>();
            foreach (var member in tree.GetRoot().DescendantNodes().OfType<BaseMethodDeclarationSyntax>().Cast<SyntaxNode>()
                         .Concat(tree.GetRoot().DescendantNodes().OfType<AccessorDeclarationSyntax>()))
                new Walker(renames).Run(member);
            // Top-level statements are one body: `int a = 10; { int a = 20; }` shadows like in a method.
            var top = tree.GetRoot().ChildNodes().OfType<GlobalStatementSyntax>().ToList();
            if (top.Count > 0) new Walker(renames).RunAll(top);
            if (renames.Count == 0) return tree;
            var root = tree.GetRoot().ReplaceTokens(renames.Keys, (old, _) =>
                SyntaxFactory.Identifier(old.LeadingTrivia, SyntaxKind.IdentifierToken, old.Text, renames[old], old.TrailingTrivia));
            return tree.WithRootAndOptions(root, tree.Options);
        }

        private sealed class Walker
        {
            private readonly Dictionary<SyntaxToken, string> _renames;
            private readonly List<Dictionary<string, string>> _scopes = new();
            private readonly Dictionary<string, int> _declared = new();
            public Walker(Dictionary<SyntaxToken, string> renames) { _renames = renames; }

            public void Run(SyntaxNode member)
            {
                _scopes.Add(new Dictionary<string, string>());
                if (member is BaseMethodDeclarationSyntax m)
                    foreach (var p in m.ParameterList.Parameters) Declare(p.Identifier);
                Visit(member);
            }

            public void RunAll(List<GlobalStatementSyntax> statements)
            {
                _scopes.Add(new Dictionary<string, string>());
                foreach (var statement in statements) Visit(statement);
            }

            private void Declare(SyntaxToken name)
            {
                string text = name.ValueText;
                int n = _declared.TryGetValue(text, out int k) ? k + 1 : 0;
                _declared[text] = n;
                // Zero-width marks keep diagnostics reading `x`.
                string inner = n == 0 ? text : text + new string('​', n);
                if (n > 0) _renames[name] = inner;
                _scopes[^1][text] = inner;
            }

            private void Use(SyntaxToken name)
            {
                for (int i = _scopes.Count - 1; i >= 0; i--)
                    if (_scopes[i].TryGetValue(name.ValueText, out var inner))
                    {
                        if (inner != name.ValueText) _renames[name] = inner;
                        return;
                    }
            }

            private void Scoped(System.Action body)
            {
                _scopes.Add(new Dictionary<string, string>());
                body();
                _scopes.RemoveAt(_scopes.Count - 1);
            }

            private void Visit(SyntaxNode node)
            {
                switch (node)
                {
                    case VariableDeclaratorSyntax v:
                        // The initializer still sees the old variable: `var x = x + 1`.
                        if (v.Initializer != null) Visit(v.Initializer);
                        Declare(v.Identifier);
                        return;
                    case SingleVariableDesignationSyntax d:
                        Declare(d.Identifier);
                        return;
                    case ForEachStatementSyntax f:
                        Visit(f.Expression);
                        Scoped(() => { Declare(f.Identifier); Visit(f.Statement); });
                        return;
                    case BlockSyntax or ForStatementSyntax or SwitchSectionSyntax or UsingStatementSyntax:
                        Scoped(() => { foreach (var c in node.ChildNodes()) Visit(c); });
                        return;
                    case AnonymousFunctionExpressionSyntax lambda:
                        Scoped(() =>
                        {
                            if (lambda is SimpleLambdaExpressionSyntax s) Declare(s.Parameter.Identifier);
                            if (lambda is ParenthesizedLambdaExpressionSyntax pl) foreach (var p in pl.ParameterList.Parameters) Declare(p.Identifier);
                            if (lambda is AnonymousMethodExpressionSyntax am && am.ParameterList != null) foreach (var p in am.ParameterList.Parameters) Declare(p.Identifier);
                            Visit(lambda.Body);
                        });
                        return;
                    case LocalFunctionStatementSyntax:
                        return;
                    case IdentifierNameSyntax id when !(id.Parent is MemberAccessExpressionSyntax ma && ma.Name == id) && id.Parent is not NameColonSyntax:
                        Use(id.Identifier);
                        return;
                }
                foreach (var c in node.ChildNodes()) Visit(c);
            }
        }
    }
}
