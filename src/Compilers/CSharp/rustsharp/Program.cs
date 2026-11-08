// rustsharp: the RustSharp command line driver.
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Ownership;
using Microsoft.CodeAnalysis.Text;

namespace RustSharp
{
    internal static class Program
    {
        private static void Usage() => Console.Error.WriteLine(
@"usage: rustsharp [options] file.rscs...
  -o <path>         output executable (default: first source without extension)
  -O0|-O1|-O2|-O3   LLVM optimization level (default -O2)
  --check           run the ownership and borrow checker only
  --asan            instrument with AddressSanitizer (memory-safety self test)
  --tsan            instrument with ThreadSanitizer (data-race self test)
  --emit-llvm <p>   keep the generated LLVM IR at <p>
  --emit-mir <p>    write MIR of user code to <p>
  --no-borrowck     skip ownership checks (still compiles natively)
  --corelib <dir>   core library source directory
  --lsp             run as a language server on stdin/stdout (for the VS Code extension)");

        private static int Main(string[] args)
        {
            var sources = new List<string>();
            var options = new NativeOptions { OutputPath = null };
            bool lsp = false;
            string corelib = Environment.GetEnvironmentVariable("RUSTSHARP_CORELIB")
                ?? Path.GetFullPath(Path.Combine(AppContext.BaseDirectory, "corelib"));

            for (int i = 0; i < args.Length; i++)
            {
                string a = args[i];
                switch (a)
                {
                    case "-o": options.OutputPath = args[++i]; break;
                    case "-O0": case "-O1": case "-O2": case "-O3": options.OptimizationLevel = a[2] - '0'; break;
                    case "--check": options.CheckOnly = true; break;
                    case "--asan": options.Sanitize = true; break;
                    case "--tsan": options.SanitizeThreads = true; break;
                    case "--emit-llvm": options.LlvmOutputPath = args[++i]; break;
                    case "--emit-mir": options.MirOutputPath = args[++i]; break;
                    case "--no-borrowck": options.BorrowCheck = false; break;
                    case "--corelib": corelib = args[++i]; break;
                    case "--lsp": lsp = true; break;
                    case "-h": case "--help": Usage(); return 0;
                    default:
                        if (a.StartsWith("-", StringComparison.Ordinal)) { Console.Error.WriteLine("unknown option " + a); Usage(); return 2; }
                        sources.Add(a);
                        break;
                }
            }

            if (lsp)
            {
                if (!Directory.Exists(corelib)) { Console.Error.WriteLine($"error: core library not found at {corelib}"); return 2; }
                return new LanguageServer(corelib).Run();
            }

            if (sources.Count == 0) { Usage(); return 2; }
            options.OutputPath ??= Path.ChangeExtension(sources[0], null);

            if (!Directory.Exists(corelib))
            {
                Console.Error.WriteLine($"error: core library not found at {corelib}");
                return 2;
            }

            var parse = NativeCompiler.ParseOptions();
            var trees = new List<SyntaxTree>();
            var user = new HashSet<SyntaxTree>();
            foreach (var path in sources)
            {
                var tree = Shadowing.Apply(CSharpSyntaxTree.ParseText(SourceText.From(File.ReadAllText(path), Encoding.UTF8), parse, path));
                trees.Add(tree);
                user.Add(tree);
            }
            foreach (var path in Directory.GetFiles(corelib, "*.rscs", SearchOption.AllDirectories).OrderBy(p => p, StringComparer.Ordinal))
                trees.Add(CSharpSyntaxTree.ParseText(SourceText.From(File.ReadAllText(path), Encoding.UTF8), parse, path));

            var compilation = CSharpCompilation.Create(
                Path.GetFileNameWithoutExtension(sources[0]), trees, Array.Empty<MetadataReference>(),
                new CSharpCompilationOptions(OutputKind.ConsoleApplication, allowUnsafe: true, concurrentBuild: false,
                    nullableContextOptions: NullableContextOptions.Enable));

            options.IsUserTree = user.Contains;
            NativeResult result;
            try
            {
                result = NativeCompiler.Compile(compilation, options);
            }
            catch (Exception e) when (e is not OutOfMemoryException)
            {
                Console.Error.WriteLine($"internal compiler error: {e.GetType().Name}: {e.Message}");
                Console.Error.WriteLine(e.StackTrace);
                return 70;
            }

            foreach (var d in result.Diagnostics) Render(d);
            int errors = result.Diagnostics.Count;
            if (errors > 0)
                Console.Error.WriteLine($"error: aborting due to {errors} previous error{(errors == 1 ? "" : "s")}");
            return result.Success ? 0 : 1;
        }

        private static void Render(NativeDiagnostic d)
        {
            var w = Console.Error;
            w.WriteLine($"error[{d.Code}]: {d.Message}");
            if (d.Location is { IsInSource: true } loc)
            {
                var labels = new List<(Location Loc, string Text, char Mark)> { (loc, d.Label, '^') };
                foreach (var s in d.Secondary)
                    if (s.Location.IsInSource) labels.Add((s.Location, s.Text, '-'));

                var span = loc.GetLineSpan();
                w.WriteLine($"  --> {span.Path}:{span.StartLinePosition.Line + 1}:{span.StartLinePosition.Character + 1}");

                var sameFile = labels.Where(l => l.Loc.SourceTree == loc.SourceTree)
                    .OrderBy(l => l.Loc.GetLineSpan().StartLinePosition.Line).ToList();
                var text = loc.SourceTree.GetText();
                int width = (sameFile.Max(l => l.Loc.GetLineSpan().StartLinePosition.Line) + 1).ToString().Length;
                string pad = new string(' ', width);
                w.WriteLine($"{pad} |");
                int previous = -1;
                foreach (var group in sameFile.GroupBy(l => l.Loc.GetLineSpan().StartLinePosition.Line))
                {
                    int line = group.Key;
                    if (previous >= 0 && line > previous + 1) w.WriteLine("...");
                    previous = line;
                    string source = text.Lines[line].ToString().TrimEnd();
                    w.WriteLine($"{(line + 1).ToString().PadLeft(width)} | {source}");
                    foreach (var l in group)
                    {
                        var ls = l.Loc.GetLineSpan();
                        int start = ls.StartLinePosition.Character;
                        int end = ls.EndLinePosition.Line == line ? ls.EndLinePosition.Character : source.Length;
                        int len = Math.Max(1, end - start);
                        w.WriteLine($"{pad} | {new string(' ', start)}{new string(l.Mark, len)} {l.Text}");
                    }
                }
                w.WriteLine($"{pad} |");
                if (d.Note != null) w.WriteLine($"{pad} = note: {d.Note}");
            }
            w.WriteLine();
        }
    }
}
