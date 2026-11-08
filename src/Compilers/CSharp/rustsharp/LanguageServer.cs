// rustsharp --lsp: a small language server for the RustSharp VS Code extension.
//
// It speaks the Language Server Protocol over stdin/stdout. The core library is parsed once and
// shared by every compilation, so a check costs only what the open file adds. Each document is
// checked on its own, like `rustsharp file.cs --check`: Roslyn's errors and the ownership checker's.
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Threading;
using System.Xml.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Ownership;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Text;

namespace RustSharp
{
    internal sealed class LanguageServer
    {
        private readonly Stream _in = Console.OpenStandardInput();
        private readonly Stream _out = Console.OpenStandardOutput();
        private readonly object _writeLock = new object();
        private readonly object _compileLock = new object();
        private readonly CSharpParseOptions _parse = NativeCompiler.ParseOptions().WithDocumentationMode(DocumentationMode.Parse);
        private readonly List<SyntaxTree> _corelib = new List<SyntaxTree>();
        private readonly HashSet<string> _corelibPaths = new HashSet<string>(StringComparer.Ordinal);
        private readonly Dictionary<string, Document> _documents = new Dictionary<string, Document>(StringComparer.Ordinal);

        private sealed class Document
        {
            public string Uri;
            public string Path;
            public string Text;
            public int Version;
            public int Generation;
            public (int Generation, CSharpCompilation Compilation, SyntaxTree Tree) Semantic;
        }

        public LanguageServer(string corelib)
        {
            foreach (var path in Directory.GetFiles(corelib, "*.rscs", SearchOption.AllDirectories).OrderBy(p => p, StringComparer.Ordinal))
            {
                string full = System.IO.Path.GetFullPath(path);
                _corelib.Add(CSharpSyntaxTree.ParseText(SourceText.From(File.ReadAllText(full), Encoding.UTF8), _parse, full));
                _corelibPaths.Add(full);
            }
        }

        public int Run()
        {
            while (true)
            {
                var message = Read();
                if (message is null) return 0;
                try
                {
                    if (Handle(message)) return 0;
                }
                catch (Exception e) when (e is not OutOfMemoryException)
                {
                    Log("internal error: " + e);
                    if (message["id"] is { } id) Respond(id, null);
                }
            }
        }

        // ---- protocol

        private JsonObject Read()
        {
            int length = -1;
            var header = new StringBuilder();
            while (true)
            {
                int b = _in.ReadByte();
                if (b < 0) return null;
                if (b == '\n')
                {
                    string line = header.ToString().TrimEnd('\r');
                    header.Clear();
                    if (line.Length == 0) break;
                    if (line.StartsWith("Content-Length:", StringComparison.OrdinalIgnoreCase))
                        length = int.Parse(line.Substring(15).Trim());
                    continue;
                }
                header.Append((char)b);
            }
            if (length < 0) return null;
            var body = new byte[length];
            int read = 0;
            while (read < length)
            {
                int n = _in.Read(body, read, length - read);
                if (n <= 0) return null;
                read += n;
            }
            return JsonNode.Parse(body)?.AsObject();
        }

        private void Send(JsonObject message)
        {
            message["jsonrpc"] = "2.0";
            byte[] body = Encoding.UTF8.GetBytes(message.ToJsonString());
            byte[] header = Encoding.ASCII.GetBytes($"Content-Length: {body.Length}\r\n\r\n");
            lock (_writeLock)
            {
                _out.Write(header, 0, header.Length);
                _out.Write(body, 0, body.Length);
                _out.Flush();
            }
        }

        private void Respond(JsonNode id, JsonNode result)
            => Send(new JsonObject { ["id"] = id.DeepClone(), ["result"] = result });

        private void Notify(string method, JsonNode parameters)
            => Send(new JsonObject { ["method"] = method, ["params"] = parameters });

        private void Log(string text)
            => Notify("window/logMessage", new JsonObject { ["type"] = 4, ["message"] = text });

        /// <summary>True when the client asked the server to exit.</summary>
        private bool Handle(JsonObject message)
        {
            string method = (string)message["method"];
            var id = message["id"];
            var p = message["params"] as JsonObject;
            switch (method)
            {
                case "initialize":
                    Respond(id, new JsonObject
                    {
                        ["capabilities"] = new JsonObject
                        {
                            ["textDocumentSync"] = new JsonObject { ["openClose"] = true, ["change"] = 1, ["save"] = true },
                            ["hoverProvider"] = true,
                            ["definitionProvider"] = true,
                            ["documentSymbolProvider"] = true,
                            ["completionProvider"] = new JsonObject { ["triggerCharacters"] = new JsonArray(".") },
                        },
                        ["serverInfo"] = new JsonObject { ["name"] = "rustsharp", ["version"] = "0.1" },
                    });
                    return false;
                case "shutdown":
                    Respond(id, null);
                    return false;
                case "exit":
                    return true;
                case "textDocument/didOpen":
                {
                    var doc = p["textDocument"];
                    Update((string)doc["uri"], (string)doc["text"], (int)doc["version"]);
                    return false;
                }
                case "textDocument/didChange":
                {
                    var changes = p["contentChanges"].AsArray();
                    if (changes.Count > 0)
                        Update((string)p["textDocument"]["uri"], (string)changes[changes.Count - 1]["text"], (int)p["textDocument"]["version"]);
                    return false;
                }
                case "textDocument/didSave":
                    return false;
                case "textDocument/didClose":
                {
                    string uri = (string)p["textDocument"]["uri"];
                    lock (_documents) _documents.Remove(uri);
                    Notify("textDocument/publishDiagnostics", new JsonObject { ["uri"] = uri, ["diagnostics"] = new JsonArray() });
                    return false;
                }
                case "textDocument/hover":
                    Respond(id, Hover(p));
                    return false;
                case "textDocument/definition":
                    Respond(id, Definition(p));
                    return false;
                case "textDocument/completion":
                    Respond(id, Completion(p));
                    return false;
                case "textDocument/documentSymbol":
                    Respond(id, Symbols(p));
                    return false;
                default:
                    if (id != null) Send(new JsonObject { ["id"] = id.DeepClone(), ["error"] = new JsonObject { ["code"] = -32601, ["message"] = "not supported: " + method } });
                    return false;
            }
        }

        // ---- checking

        private void Update(string uri, string text, int version)
        {
            Document doc;
            lock (_documents)
            {
                if (!_documents.TryGetValue(uri, out doc))
                    _documents[uri] = doc = new Document { Uri = uri, Path = PathOf(uri) };
                doc.Text = text;
                doc.Version = version;
                doc.Generation++;
            }
            int generation = doc.Generation;

            // Typing quickly changes the text again before a check would finish; only the last one runs.
            ThreadPool.QueueUserWorkItem(_ =>
            {
                Thread.Sleep(350);
                lock (_documents) if (doc.Generation != generation) return;
                lock (_compileLock)
                {
                    lock (_documents) if (doc.Generation != generation) return;
                    Check(doc, generation);
                }
            });
        }

        private CSharpCompilation Compile(SyntaxTree user)
        {
            var trees = new List<SyntaxTree> { user };
            trees.AddRange(_corelib.Where(t => !string.Equals(t.FilePath, user.FilePath, StringComparison.Ordinal)));
            return CSharpCompilation.Create(
                System.IO.Path.GetFileNameWithoutExtension(user.FilePath), trees, Array.Empty<MetadataReference>(),
                new CSharpCompilationOptions(OutputKind.ConsoleApplication, allowUnsafe: true, concurrentBuild: false,
                    nullableContextOptions: NullableContextOptions.Enable));
        }

        private void Check(Document doc, int generation)
        {
            string text;
            lock (_documents) text = doc.Text;
            var tree = Shadowing.Apply(CSharpSyntaxTree.ParseText(SourceText.From(text, Encoding.UTF8), _parse, doc.Path));
            bool isCorelib = _corelibPaths.Contains(doc.Path);
            var compilation = Compile(tree);
            lock (_documents) doc.Semantic = (generation, compilation, tree);

            var options = new NativeOptions { CheckOnly = true, OutputPath = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "rustsharp-lsp") };
            // A corelib file is checked as the library it is; user files get the stricter user rules.
            options.IsUserTree = t => !isCorelib && t == tree;
            NativeResult result;
            try
            {
                result = NativeCompiler.Compile(compilation, options);
            }
            catch (Exception e) when (e is not OutOfMemoryException)
            {
                Log("internal compiler error: " + e);
                return;
            }

            lock (_documents) if (doc.Generation != generation) return;
            var list = new JsonArray();
            foreach (var d in result.Diagnostics)
            {
                if (d.Location is not { IsInSource: true } loc || loc.SourceTree != tree) continue;
                list.Add(ToLsp(d, doc.Uri));
            }

            // Errors in other files, such as the corelib, still belong in front of the user.
            var elsewhere = result.Diagnostics.Where(d => d.Location is not { IsInSource: true } l || l.SourceTree != tree).ToList();
            if (elsewhere.Count > 0)
            {
                var first = elsewhere[0];
                string where = first.Location is { IsInSource: true } l ? $"{l.GetLineSpan().Path}:{l.GetLineSpan().StartLinePosition.Line + 1}" : "";
                list.Add(new JsonObject
                {
                    ["range"] = Range(new LinePositionSpan(new LinePosition(0, 0), new LinePosition(0, 0))),
                    ["severity"] = 1,
                    ["source"] = "rustsharp",
                    ["code"] = first.Code,
                    ["message"] = $"{elsewhere.Count} error(s) outside this file, first: {first.Message} {where}",
                });
            }

            Notify("textDocument/publishDiagnostics", new JsonObject
            {
                ["uri"] = doc.Uri,
                ["version"] = doc.Version,
                ["diagnostics"] = list,
            });
        }

        private static JsonObject ToLsp(NativeDiagnostic d, string uri)
        {
            string message = d.Message;
            if (!string.IsNullOrEmpty(d.Label) && !message.Contains(d.Label, StringComparison.Ordinal)) message += "\n" + d.Label;
            if (d.Note != null) message += "\nnote: " + d.Note;
            var related = new JsonArray();
            foreach (var s in d.Secondary)
            {
                if (!s.Location.IsInSource) continue;
                related.Add(new JsonObject
                {
                    ["location"] = new JsonObject { ["uri"] = UriOf(s.Location.GetLineSpan().Path, uri, s.Location.SourceTree), ["range"] = Range(s.Location.GetLineSpan().Span) },
                    ["message"] = s.Text ?? "",
                });
            }
            return new JsonObject
            {
                ["range"] = Range(d.Location.GetLineSpan().Span),
                ["severity"] = d.Severity == "warning" ? 2 : 1,
                ["source"] = "rustsharp",
                ["code"] = d.Code,
                ["message"] = message,
                ["relatedInformation"] = related,
            };
        }

        // ---- navigation

        private (Document Doc, CSharpCompilation Compilation, SyntaxTree Tree, int Position)? Locate(JsonObject p)
        {
            string uri = (string)p["textDocument"]["uri"];
            Document doc;
            lock (_documents) if (!_documents.TryGetValue(uri, out doc)) return null;

            CSharpCompilation compilation;
            SyntaxTree tree;
            lock (_documents)
            {
                (int generation, compilation, tree) = doc.Semantic;
                if (compilation is null || generation != doc.Generation)
                {
                    // The text changed since the last check: binding is lazy, so a fresh compilation is cheap here.
                    tree = Shadowing.Apply(CSharpSyntaxTree.ParseText(SourceText.From(doc.Text, Encoding.UTF8), _parse, doc.Path));
                    compilation = Compile(tree);
                    doc.Semantic = (doc.Generation, compilation, tree);
                }
            }
            var text = tree.GetText();
            if (p["position"] is null) return (doc, compilation, tree, 0);
            int line = (int)p["position"]["line"], character = (int)p["position"]["character"];
            if (line >= text.Lines.Count) return null;
            int position = Math.Min(text.Lines[line].Start + character, text.Length);
            return (doc, compilation, tree, position);
        }

        private static ISymbol SymbolAt(SemanticModel model, SyntaxTree tree, int position)
        {
            var root = tree.GetRoot();
            var token = root.FindToken(position);
            if (position > 0 && !token.Span.Contains(position) && token.Span.Start == position && position > 0)
                token = root.FindToken(position - 1);
            for (var node = token.Parent; node != null; node = node.Parent)
            {
                var symbol = model.GetDeclaredSymbol(node);
                if (symbol != null && (node is not BlockSyntax) && NameToken(node) == token) return symbol;
                var info = model.GetSymbolInfo(node);
                if (info.Symbol != null) return info.Symbol;
                if (info.CandidateSymbols.Length > 0) return info.CandidateSymbols[0];
                if (node is StatementSyntax or MemberDeclarationSyntax) break;
            }
            return null;
        }

        private static SyntaxToken NameToken(SyntaxNode node) => node switch
        {
            VariableDeclaratorSyntax v => v.Identifier,
            MethodDeclarationSyntax m => m.Identifier,
            BaseTypeDeclarationSyntax t => t.Identifier,
            PropertyDeclarationSyntax pr => pr.Identifier,
            ParameterSyntax pa => pa.Identifier,
            SingleVariableDesignationSyntax s => s.Identifier,
            ForEachStatementSyntax f => f.Identifier,
            ConstructorDeclarationSyntax c => c.Identifier,
            DelegateDeclarationSyntax de => de.Identifier,
            EnumMemberDeclarationSyntax e => e.Identifier,
            LocalFunctionStatementSyntax lf => lf.Identifier,
            _ => default,
        };

        private JsonNode Hover(JsonObject p)
        {
            if (Locate(p) is not { } at) return null;
            var model = at.Compilation.GetSemanticModel(at.Tree);
            var symbol = SymbolAt(model, at.Tree, at.Position);
            if (symbol is null) return null;

            string shown = symbol.ToDisplayString(SymbolDisplayFormat.MinimallyQualifiedFormat);
            // `var` always infers a nullable reference type in C#; show what the initializer gives.
            if (symbol is ILocalSymbol { IsRef: false } local && local.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is VariableDeclaratorSyntax
                { Parent: VariableDeclarationSyntax { Type.IsVar: true } } && local.Type.IsReferenceType)
                shown = local.Type.WithNullableAnnotation(NullableAnnotation.NotAnnotated).ToDisplayString(SymbolDisplayFormat.MinimallyQualifiedFormat) + " " + local.Name;
            if (symbol is ILocalSymbol or IParameterSymbol && symbol.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is { } declared && HasMut(declared))
                shown = "mut " + shown;
            string kind = symbol switch
            {
                ILocalSymbol => "local",
                IParameterSymbol => "parameter",
                IFieldSymbol => "field",
                IPropertySymbol => "property",
                IMethodSymbol m => m.MethodKind == MethodKind.Constructor ? "constructor" : "method",
                INamedTypeSymbol t => t.TypeKind.ToString().ToLowerInvariant(),
                _ => symbol.Kind.ToString().ToLowerInvariant(),
            };

            shown = shown.Replace("\u200B", ""); // the marks shadowing adds to a redeclared name
            var markdown = new StringBuilder();
            markdown.Append("```csharp\n(").Append(kind).Append(") ").Append(shown).Append("\n```");
            string summary = Summary(symbol);
            if (summary != null) markdown.Append("\n\n").Append(summary);
            if (TypeOf(symbol) is { } type && Traits(type) is { Length: > 0 } traits) markdown.Append("\n\n").Append(traits);
            return new JsonObject { ["contents"] = new JsonObject { ["kind"] = "markdown", ["value"] = markdown.ToString() } };
        }

        private static ITypeSymbol TypeOf(ISymbol s) => s switch
        {
            ILocalSymbol l => l.Type,
            IParameterSymbol p => p.Type,
            IFieldSymbol f => f.Type,
            IPropertySymbol pr => pr.Type,
            INamedTypeSymbol t => t,
            _ => null,
        };

        /// <summary>What Rust would print as the type's traits: whether a value is copied or moved.</summary>
        private static string Traits(ITypeSymbol type)
        {
            if (type.TypeKind == TypeKind.Error || type is ITypeParameterSymbol) return null;
            bool copy = type.SpecialType switch
            {
                SpecialType.System_Boolean or SpecialType.System_Char or SpecialType.System_SByte or SpecialType.System_Byte
                    or SpecialType.System_Int16 or SpecialType.System_UInt16 or SpecialType.System_Int32 or SpecialType.System_UInt32
                    or SpecialType.System_Int64 or SpecialType.System_UInt64 or SpecialType.System_Single or SpecialType.System_Double
                    or SpecialType.System_Decimal or SpecialType.System_IntPtr or SpecialType.System_UIntPtr => true,
                _ => type.TypeKind == TypeKind.Enum || type.TypeKind == TypeKind.Pointer,
            };
            if (type.SpecialType == SpecialType.System_String) return "*shared: strings are reference counted and immutable*";
            if (copy) return "*Copy: assigning or passing it copies the value*";
            if (type.TypeKind is TypeKind.Class or TypeKind.Array or TypeKind.Delegate or TypeKind.Interface) return "*moves: assigning or passing it hands over ownership*";
            return null;
        }

        private static bool HasMut(SyntaxNode declared)
        {
            for (var n = declared; n != null; n = n.Parent)
            {
                SyntaxToken first = n switch
                {
                    VariableDeclarationSyntax v => v.Type.GetFirstToken(),
                    ParameterSyntax p => p.GetFirstToken(),
                    ForEachStatementSyntax f => f.Type.GetFirstToken(),
                    DeclarationExpressionSyntax d => d.Type.GetFirstToken(),
                    _ => default,
                };
                if (first != default) return first.LeadingTrivia.Any(t => t.ToString() == "mut");
                if (n is StatementSyntax) return false;
            }
            return false;
        }

        private static string Summary(ISymbol symbol)
        {
            string xml = symbol.GetDocumentationCommentXml();
            if (string.IsNullOrWhiteSpace(xml)) return null;
            try
            {
                var summary = XElement.Parse(xml).Element("summary");
                if (summary is null) return null;
                var text = new StringBuilder();
                foreach (var node in summary.Nodes())
                {
                    if (node is XText t) text.Append(t.Value);
                    else if (node is XElement e) text.Append('`').Append(e.Attribute("cref")?.Value?.Split(':').Last() ?? e.Attribute("name")?.Value ?? e.Value).Append('`');
                }
                return string.Join(" ", text.ToString().Split(new[] { ' ', '\n', '\r', '\t' }, StringSplitOptions.RemoveEmptyEntries));
            }
            catch (System.Xml.XmlException)
            {
                return null;
            }
        }

        private JsonNode Definition(JsonObject p)
        {
            if (Locate(p) is not { } at) return null;
            var symbol = SymbolAt(at.Compilation.GetSemanticModel(at.Tree), at.Tree, at.Position);
            if (symbol is null) return null;
            if (symbol is IMethodSymbol { ReducedFrom: { } reduced }) symbol = reduced;
            var result = new JsonArray();
            foreach (var loc in symbol.OriginalDefinition.Locations)
            {
                if (!loc.IsInSource) continue;
                var span = loc.GetLineSpan();
                result.Add(new JsonObject { ["uri"] = UriOf(span.Path, at.Doc.Uri, loc.SourceTree == at.Tree ? at.Tree : null), ["range"] = Range(span.Span) });
            }
            return result;
        }

        private JsonNode Completion(JsonObject p)
        {
            if (Locate(p) is not { } at) return new JsonArray();
            var model = at.Compilation.GetSemanticModel(at.Tree);
            var token = at.Tree.GetRoot().FindToken(Math.Max(0, at.Position - 1));
            IEnumerable<ISymbol> symbols;
            if (token.IsKind(SyntaxKind.DotToken) && token.Parent is MemberAccessExpressionSyntax access)
            {
                var left = model.GetTypeInfo(access.Expression).Type;
                var target = model.GetSymbolInfo(access.Expression).Symbol;
                if (target is INamespaceOrTypeSymbol container && target is not ITypeSymbol { IsReferenceType: false } && access.Expression is not ThisExpressionSyntax && left is null)
                    symbols = model.LookupSymbols(at.Position, container);
                else if (target is INamedTypeSymbol staticType && model.GetTypeInfo(access.Expression).Type is null)
                    symbols = model.LookupStaticMembers(at.Position, staticType);
                else if (left != null)
                    symbols = model.LookupSymbols(at.Position, left, includeReducedExtensionMethods: true).Where(s => !s.IsStatic || s is IMethodSymbol { IsExtensionMethod: true } || s.Kind == SymbolKind.Method && ((IMethodSymbol)s).ReducedFrom != null);
                else
                    symbols = Array.Empty<ISymbol>();
            }
            else
            {
                symbols = model.LookupSymbols(at.Position);
            }

            var items = new JsonArray();
            foreach (var group in symbols.Where(s => s.CanBeReferencedByName && s.DeclaredAccessibility != Accessibility.Private || s.Locations.Any(l => l.SourceTree == at.Tree) || s is ILocalSymbol or IParameterSymbol)
                         .Where(s => s.CanBeReferencedByName)
                         .GroupBy(s => s.Name).Take(400))
            {
                var s = group.First();
                items.Add(new JsonObject
                {
                    ["label"] = s.Name,
                    ["kind"] = s switch
                    {
                        IMethodSymbol => 2,
                        IFieldSymbol => 5,
                        IPropertySymbol => 10,
                        ILocalSymbol or IParameterSymbol => 6,
                        INamedTypeSymbol { TypeKind: TypeKind.Interface } => 8,
                        INamedTypeSymbol { TypeKind: TypeKind.Enum } => 13,
                        INamedTypeSymbol { TypeKind: TypeKind.Struct } => 22,
                        INamedTypeSymbol => 7,
                        INamespaceSymbol => 9,
                        _ => 1,
                    },
                    ["detail"] = s.ToDisplayString(SymbolDisplayFormat.MinimallyQualifiedFormat) + (group.Count() > 1 ? $" (+{group.Count() - 1} overloads)" : ""),
                });
            }
            return items;
        }

        private JsonNode Symbols(JsonObject p)
        {
            if (Locate(p) is not { } at) return new JsonArray();
            var result = new JsonArray();
            foreach (var type in at.Tree.GetRoot().DescendantNodes().OfType<BaseTypeDeclarationSyntax>())
            {
                var children = new JsonArray();
                if (type is TypeDeclarationSyntax withMembers)
                {
                    foreach (var member in withMembers.Members)
                    {
                        var (name, kind, selection) = member switch
                        {
                            MethodDeclarationSyntax m => (m.Identifier.Text, 6, m.Identifier.Span),
                            ConstructorDeclarationSyntax c => (c.Identifier.Text, 9, c.Identifier.Span),
                            PropertyDeclarationSyntax pr => (pr.Identifier.Text, 7, pr.Identifier.Span),
                            FieldDeclarationSyntax f => (f.Declaration.Variables.First().Identifier.Text, 8, f.Declaration.Variables.First().Identifier.Span),
                            DestructorDeclarationSyntax d => ("~" + d.Identifier.Text, 9, d.Identifier.Span),
                            _ => (null, 0, default(TextSpan)),
                        };
                        if (name is null) continue;
                        children.Add(SymbolNode(at.Tree, name, kind, member.Span, selection, new JsonArray()));
                    }
                }
                int typeKind = type switch { InterfaceDeclarationSyntax => 11, StructDeclarationSyntax => 23, EnumDeclarationSyntax => 10, _ => 5 };
                result.Add(SymbolNode(at.Tree, type.Identifier.Text, typeKind, type.Span, type.Identifier.Span, children));
            }
            return result;
        }

        private static JsonObject SymbolNode(SyntaxTree tree, string name, int kind, TextSpan span, TextSpan selection, JsonArray children)
            => new JsonObject
            {
                ["name"] = name,
                ["kind"] = kind,
                ["range"] = Range(tree.GetLineSpan(span).Span),
                ["selectionRange"] = Range(tree.GetLineSpan(selection).Span),
                ["children"] = children,
            };

        // ---- helpers

        private static JsonObject Range(LinePositionSpan span) => new JsonObject
        {
            ["start"] = new JsonObject { ["line"] = span.Start.Line, ["character"] = span.Start.Character },
            ["end"] = new JsonObject { ["line"] = span.End.Line, ["character"] = span.End.Character },
        };

        private static string PathOf(string uri)
        {
            try { return new Uri(uri).LocalPath; }
            catch (UriFormatException) { return uri; }
        }

        private static string UriOf(string path, string currentUri, SyntaxTree current)
            => current != null ? currentUri : new Uri(System.IO.Path.GetFullPath(path)).AbsoluteUri;
    }
}
