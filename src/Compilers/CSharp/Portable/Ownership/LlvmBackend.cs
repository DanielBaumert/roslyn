// RustSharp: monomorphizing LLVM IR generator. Whole-program by construction: starting at the entry
// point, closed method instances are compiled on demand. Virtual dispatch, interface dispatch, type
// tests and drop glue are switch stubs over the object's type id, generated at the worklist fixpoint
// when every instantiated type is known, so there are no vtables.

using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Globalization;
using System.Linq;
using System.Text;
using Microsoft.CodeAnalysis.CSharp.Symbols;
using Microsoft.CodeAnalysis.PooledObjects;

namespace Microsoft.CodeAnalysis.CSharp.Ownership
{
    internal sealed partial class LlvmBackend
    {
        private enum ObjKind { Class, Array, Box, String }

        private sealed class ObjType
        {
            public ObjKind Kind;
            public TypeSymbol Type;
            public int Id;
            public bool GlueDone, CloneDone, EqDone, HashDone;
        }

        private sealed class Layout
        {
            public string LlvmType;
            public List<FieldSymbol> Fields = new List<FieldSymbol>();
            public Dictionary<FieldSymbol, int> Index = new Dictionary<FieldSymbol, int>(Symbols.SymbolEqualityComparer.AllIgnoreOptions);
            public int AliveIndex = -1;
        }

        private sealed class Dispatch
        {
            public MethodSymbol Method;
            public string Name;
            public Dictionary<int, (string Fn, bool Unbox)> Cases = new Dictionary<int, (string, bool)>();
            public HashSet<int> Seen = new HashSet<int>();
        }

        private sealed class IsInstFn
        {
            public TypeSymbol Target;
            public string Name;
        }

        private static readonly EqualityComparer<Symbol> s_cmp = Symbols.SymbolEqualityComparer.AllIgnoreOptions;

        private readonly CSharpCompilation _compilation;
        private readonly Dictionary<MethodSymbol, MirBody> _bodies;
        private readonly List<string> _errors;
        private readonly StringBuilder _types = new StringBuilder();
        private readonly StringBuilder _globals = new StringBuilder();
        private readonly StringBuilder _code = new StringBuilder();
        private readonly Dictionary<string, string> _declares = new Dictionary<string, string>();

        private readonly Dictionary<MethodSymbol, string> _fns = new Dictionary<MethodSymbol, string>(s_cmp);
        private readonly Queue<MethodSymbol> _work = new Queue<MethodSymbol>();
        private readonly Dictionary<TypeSymbol, Layout> _layouts = new Dictionary<TypeSymbol, Layout>(s_cmp);
        private readonly Dictionary<(ObjKind, TypeSymbol), ObjType> _objByType = new Dictionary<(ObjKind, TypeSymbol), ObjType>(new ObjKeyComparer());
        private readonly List<ObjType> _objs = new List<ObjType>();
        private readonly Dictionary<MethodSymbol, Dispatch> _dispatch = new Dictionary<MethodSymbol, Dispatch>(s_cmp);
        private readonly Dictionary<TypeSymbol, IsInstFn> _isInst = new Dictionary<TypeSymbol, IsInstFn>(s_cmp);
        private readonly Dictionary<TypeSymbol, string> _drops = new Dictionary<TypeSymbol, string>(s_cmp);
        private readonly Queue<TypeSymbol> _dropWork = new Queue<TypeSymbol>();
        private readonly Dictionary<string, string> _statics = new Dictionary<string, string>();
        private readonly Dictionary<TypeSymbol, string> _guards = new Dictionary<TypeSymbol, string>(s_cmp);
        private readonly Dictionary<string, string> _strings = new Dictionary<string, string>();
        private int _next;
        public bool Sanitize;
        public bool SanitizeThreads;
        public readonly List<NativeDiagnostic> Located = new List<NativeDiagnostic>();

        public System.Func<SyntaxTree, bool> IsUserTree;
        private readonly Dictionary<MethodSymbol, (MethodSymbol Caller, SyntaxNode Site)> _origin = new Dictionary<MethodSymbol, (MethodSymbol, SyntaxNode)>(s_cmp);
        private MethodSymbol _currentMethod;
        private SyntaxNode _currentSite;

        // IsUserTree (above) also decides where user code records its position for "panicked at".

        internal string SiteText(SyntaxNode syntax)
        {
            var span = syntax.GetLocation().GetLineSpan();
            // Like rustc: relative to where the compiler ran, when the file is below it.
            string path = span.Path;
            if (System.IO.Path.IsPathRooted(path))
            {
                string relative = System.IO.Path.GetRelativePath(System.IO.Directory.GetCurrentDirectory(), path);
                if (!relative.StartsWith("..", System.StringComparison.Ordinal)) path = relative;
            }
            return $"{path}:{span.StartLinePosition.Line + 1}:{span.StartLinePosition.Character + 1}";
        }

        /// <summary>Errors found inside generic library code point at the user's call that instantiated it.</summary>
        private void Report(ErrorCode code, string message, SyntaxNode syntax, string label = null)
        {
            var method = _currentMethod;
            while (syntax != null && IsUserTree != null && !IsUserTree(syntax.SyntaxTree) && method != null && _origin.TryGetValue(method, out var origin))
            {
                syntax = origin.Site;
                method = origin.Caller;
            }
            Located.Add(new NativeDiagnostic { Code = "CS" + (int)code, Message = message, Location = syntax?.Location, Label = label });
        }

        private sealed class ObjKeyComparer : IEqualityComparer<(ObjKind, TypeSymbol)>
        {
            public bool Equals((ObjKind, TypeSymbol) a, (ObjKind, TypeSymbol) b) => a.Item1 == b.Item1 && s_cmp.Equals(a.Item2, b.Item2);
            public int GetHashCode((ObjKind, TypeSymbol) k) => s_cmp.GetHashCode(k.Item2) * 4 + (int)k.Item1;
        }

        public LlvmBackend(CSharpCompilation compilation, Dictionary<MethodSymbol, MirBody> bodies, List<string> errors)
        {
            _compilation = compilation;
            _bodies = bodies;
            _errors = errors;
        }

        private static string Quote(string s)
        {
            var sb = new StringBuilder("\"");
            foreach (char c in s)
            {
                if (c == '"' || c == '\\' || c < 32 || c > 126) sb.Append('\\').Append(((int)c & 0xff).ToString("X2"));
                else sb.Append(c);
            }
            return sb.Append('"').ToString();
        }

        private string Unique(string baseName) => "@" + Quote(baseName + "#" + _next++);

        private void Declare(string name, string signature)
        {
            if (!_declares.ContainsKey(name)) _declares[name] = signature;
        }

        // ---- types

        private static bool IsHandle(TypeSymbol t) => t.IsReferenceType;

        private static TypeSymbol Unenum(TypeSymbol t) => t.TypeKind == TypeKind.Enum ? t.GetEnumUnderlyingType() : t;

        private string Ty(TypeSymbol t)
        {
            t = Unenum(t);
            switch (t.SpecialType)
            {
                case SpecialType.System_Void: return "void";
                case SpecialType.System_Boolean:
                case SpecialType.System_Byte:
                case SpecialType.System_SByte: return "i8";
                case SpecialType.System_Char:
                case SpecialType.System_Int16:
                case SpecialType.System_UInt16: return "i16";
                case SpecialType.System_Int32:
                case SpecialType.System_UInt32: return "i32";
                case SpecialType.System_Int64:
                case SpecialType.System_UInt64:
                case SpecialType.System_IntPtr:
                case SpecialType.System_UIntPtr: return "i64";
                case SpecialType.System_Single: return "float";
                case SpecialType.System_Double: return "double";
            }
            if (t.TypeKind is TypeKind.Pointer or TypeKind.FunctionPointer || IsHandle(t)) return "ptr";
            if (t.IsValueType) return LayoutOf(t).LlvmType;
            _errors.Add("cannot lay out type " + t.ToDisplayString());
            return "ptr";
        }

        private string Ty(MirType t) => t.IsRef ? "ptr" : Ty(t.Type);

        private static bool IsPrimitive(TypeSymbol t) => t.SpecialType is
            SpecialType.System_Boolean or SpecialType.System_Byte or SpecialType.System_SByte or SpecialType.System_Char or
            SpecialType.System_Int16 or SpecialType.System_UInt16 or SpecialType.System_Int32 or SpecialType.System_UInt32 or
            SpecialType.System_Int64 or SpecialType.System_UInt64 or SpecialType.System_IntPtr or SpecialType.System_UIntPtr or
            SpecialType.System_Single or SpecialType.System_Double;

        private Layout LayoutOf(TypeSymbol t)
        {
            if (_layouts.TryGetValue(t, out var layout)) return layout;
            var key = t;
            if (t.IsAnonymousType) t = AnonymousTypeManager.TranslateAnonymousTypeSymbol((NamedTypeSymbol)t);
            layout = new Layout { LlvmType = "%" + Quote(key.ToDisplayString() + (t.IsValueType ? "" : ".obj") + "#" + _next++) };
            _layouts[key] = layout;

            var parts = new List<string>();
            if (!t.IsValueType) parts.Add("i64");

            void AddFields(NamedTypeSymbol type)
            {
                if (!type.IsValueType && type.BaseTypeNoUseSiteDiagnostics is { } b) AddFields(b);
                foreach (var f in OwnershipFacts.InstanceFields(type))
                {
                    layout.Index[f.OriginalDefinition] = parts.Count;
                    layout.Fields.Add(f);
                    parts.Add(f.RefKind != RefKind.None ? "ptr" : Ty(f.Type));
                }
            }

            if (t is NamedTypeSymbol n) AddFields(n);
            if (t.IsValueType && OwnershipFacts.FindDestructor(t) is not null)
            {
                layout.AliveIndex = parts.Count;
                parts.Add("i8");
            }
            // An empty struct still takes a byte, as in C++: a zero-sized store at the end of an alloca
            // trips AddressSanitizer, and Option<Unit> puts exactly such a field last.
            if (t.IsValueType && parts.Count == 0) parts.Add("i8");

            _types.Append(layout.LlvmType).Append(" = type { ").Append(string.Join(", ", parts)).Append(" }\n");
            return layout;
        }

        private ObjType Obj(ObjKind kind, TypeSymbol t)
        {
            if (_objByType.TryGetValue((kind, t), out var o)) return o;
            o = new ObjType { Kind = kind, Type = t, Id = _objs.Count + 1 };
            _objByType[(kind, t)] = o;
            _objs.Add(o);
            return o;
        }

        private ObjType ObjOfClass(TypeSymbol t) => Obj(OwnershipFacts.IsString(t) ? ObjKind.String : ObjKind.Class, t);

        private static bool Assignable(ObjType o, TypeSymbol target)
        {
            if (target.SpecialType == SpecialType.System_Object) return true;
            switch (o.Kind)
            {
                case ObjKind.Array:
                    return s_cmp.Equals(o.Type, target) || target.SpecialType == SpecialType.System_Array;
                case ObjKind.Box:
                    if (s_cmp.Equals(o.Type, target) || target.SpecialType == SpecialType.System_ValueType) return true;
                    return ((NamedTypeSymbol)o.Type).AllInterfacesNoUseSiteDiagnostics.Any(i => s_cmp.Equals(i, target));
                default:
                    for (TypeSymbol b = o.Type; b is not null; b = b.BaseTypeNoUseSiteDiagnostics)
                        if (s_cmp.Equals(b, target)) return true;
                    return o.Type is NamedTypeSymbol n && n.AllInterfacesNoUseSiteDiagnostics.Any(i => s_cmp.Equals(i, target));
            }
        }

        // ---- generic instantiation

        private static TypeMap MapFor(MethodSymbol closed)
        {
            var from = ArrayBuilder<TypeParameterSymbol>.GetInstance();
            var to = ArrayBuilder<TypeWithAnnotations>.GetInstance();
            for (var t = closed.ContainingType; t is not null; t = t.ContainingType)
            {
                from.AddRange(t.OriginalDefinition.TypeParameters);
                to.AddRange(t.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics);
            }
            from.AddRange(closed.OriginalDefinition.TypeParameters);
            to.AddRange(closed.TypeArgumentsWithAnnotations);
            return new TypeMap(from.ToImmutableAndFree(), to.ToImmutableAndFree());
        }

        private static MethodSymbol Close(MethodSymbol m, TypeMap map)
        {
            var container = (NamedTypeSymbol)map.SubstituteType(m.ContainingType).Type;
            var def = m.OriginalDefinition;
            var member = container.IsDefinition ? def : def.AsMember(container);
            if (m.Arity > 0)
                member = member.Construct(m.TypeArgumentsWithAnnotations.SelectAsArray(static (a, map) => map.SubstituteType(a.Type), map));
            return member;
        }

        internal MethodSymbol FindImplementation(TypeSymbol concrete, MethodSymbol m) => FindImpl(concrete, m);

        private static MethodSymbol FindImpl(TypeSymbol concrete, MethodSymbol m)
        {
            MethodSymbol impl = null;
            if (m.ContainingType.IsInterface)
            {
                var slot = m.IsGenericMethod ? m.ConstructedFrom : m;
                impl = concrete.FindImplementationForInterfaceMember(slot) as MethodSymbol;

                // The implementation may be a virtual slot on a base class that `concrete` overrides.
                if (impl is { ContainingType.IsInterface: false } && (impl.IsVirtual || impl.IsAbstract || impl.IsOverride))
                    impl = FindImpl(concrete, impl) ?? impl;
            }
            else
            {
                var root = m.OriginalDefinition.GetLeastOverriddenMethod(null).OriginalDefinition;
                for (var t = concrete; t is not null && impl is null; t = t.BaseTypeNoUseSiteDiagnostics)
                {
                    foreach (var mem in t.GetMembers(m.Name).OfType<MethodSymbol>())
                    {
                        if (mem.IsAbstract || !(mem.IsVirtual || mem.IsOverride)) continue;
                        if (s_cmp.Equals(mem.OriginalDefinition.GetLeastOverriddenMethod(null).OriginalDefinition, root))
                        {
                            impl = mem;
                            break;
                        }
                    }
                }
            }

            if (impl is { IsGenericMethod: true } && m.IsGenericMethod && impl.IsDefinition)
                impl = impl.Construct(m.TypeArgumentsWithAnnotations.SelectAsArray(a => a.Type));
            return impl;
        }

        private string Fn(MethodSymbol closed)
        {
            if (_fns.TryGetValue(closed, out var name)) return name;
            name = Unique(closed.ToDisplayString());
            _fns[closed] = name;
            _origin[closed] = (_currentMethod, _currentSite);
            _work.Enqueue(closed);
            return name;
        }

        private string ReturnTy(MethodSymbol m) => m.RefKind != RefKind.None ? "ptr" : Ty(m.ReturnType);

        private string ThisTy(MethodSymbol m)
            => OwnershipFacts.GetThisMode(m) == ThisMode.Value ? Ty(m.ContainingType) : "ptr";

        private List<string> ParamTys(MethodSymbol m)
        {
            var l = new List<string>();
            if (!m.IsStatic) l.Add(ThisTy(m));
            foreach (var p in m.Parameters) l.Add(p.RefKind != RefKind.None ? "ptr" : Ty(p.Type));
            return l;
        }

        /// <summary>Offset of the first element: multidimensional arrays store their dimensions in front.</summary>
        private static int ArrayDataOffset(int rank) => rank == 1 ? 16 : 16 + 8 * rank;

        private readonly Dictionary<string, string> _faults = new Dictionary<string, string>();
        private string _blockOn, _blockOnInt, _mainResult, _mainResultType;

        /// <summary>The core library function that creates the exception for a runtime fault.</summary>
        private string FaultFn(string kind) => _faults[kind];

        // ---- driver

        public string Generate(MethodSymbol entry)
        {
            Obj(ObjKind.String, _compilation.GetSpecialType(SpecialType.System_String));
            var runtime = _compilation.GetTypeByMetadataName("System.Startup");
            var unhandled = runtime?.GetMembers("ReportUnhandled").OfType<MethodSymbol>().FirstOrDefault();
            var makeArgs = runtime?.GetMembers("MakeArgs").OfType<MethodSymbol>().FirstOrDefault();

            foreach (var kind in new[] { "Null", "Bounds", "DivideByZero", "Cast", "Overflow" })
            {
                var factory = runtime?.GetMembers("Fault" + kind).OfType<MethodSymbol>().FirstOrDefault();
                if (factory is null) _errors.Add("core library lacks System.Startup.Fault" + kind);
                else _faults[kind] = Fn(factory);
            }

            // `Result<T, E> Main`, also inside a Task: the startup code turns it into the exit code.
            if (CSharpCompilation.IsResultMain(entry, out bool resultInTask))
            {
                var result = (NamedTypeSymbol)(resultInTask ? ((NamedTypeSymbol)entry.ReturnType).TypeArgumentsWithAnnotationsNoUseSiteDiagnostics[0].Type : entry.ReturnType);
                var helper = runtime.GetMembers(resultInTask ? "RunMainResult" : "MainResult").OfType<MethodSymbol>().First()
                    .Construct(result.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics);
                if (resultInTask) _blockOnInt = Fn(helper);
                else
                {
                    _mainResult = Fn(helper);
                    _mainResultType = Ty(result);
                }
            }
            // `async Task Main`: the startup code runs the returned task to completion.
            else if (entry.IsAsync)
            {
                bool hasResult = entry.ReturnType is NamedTypeSymbol { Arity: 1 };
                var run = runtime.GetMembers(hasResult ? "RunMainInt" : "RunMain").OfType<MethodSymbol>().First();
                if (hasResult) _blockOnInt = Fn(run);
                else _blockOn = Fn(run);
            }

            var main = Fn(entry);
            var unhandledFn = unhandled is null ? null : Fn(unhandled);
            bool wantsArgs = entry.ParameterCount == 1;
            var makeArgsFn = wantsArgs && makeArgs != null ? Fn(makeArgs) : null;

            bool progress = true;
            while (progress)
            {
                progress = false;
                while (_work.Count > 0)
                {
                    progress = true;
                    CompileMethod(_work.Dequeue());
                }
                while (_dropWork.Count > 0)
                {
                    progress = true;
                    EmitDropGlue(_dropWork.Dequeue());
                }
                for (int i = 0; i < _objs.Count; i++)
                {
                    var o = _objs[i];
                    if (!o.GlueDone)
                    {
                        o.GlueDone = true;
                        progress = true;
                        EmitObjectGlue(o);
                    }
                    if (_needClone && !o.CloneDone && _cloneTargets.Any(t => Assignable(o, t)))
                    {
                        o.CloneDone = true;
                        progress = true;
                        EmitObjectClone(o);
                    }
                    if (_needEq && !o.EqDone)
                    {
                        o.EqDone = true;
                        progress = true;
                        EmitObjectEq(o);
                    }
                    if (_needHash && !o.HashDone)
                    {
                        o.HashDone = true;
                        progress = true;
                        EmitObjectHash(o);
                    }
                    foreach (var d in _dispatch.Values.ToList())
                    {
                        if (!d.Seen.Add(o.Id)) continue;
                        progress = true;
                        AddDispatchCase(d, o);
                    }
                }
            }

            foreach (var d in _dispatch.Values) EmitDispatch(d);
            foreach (var f in _isInst.Values) EmitIsInst(f);
            EmitDropObj();
            EmitObjectSwitches();
            EmitRuntime();
            EmitMain(entry, main, unhandledFn, makeArgsFn);

            var sb = new StringBuilder();
            sb.Append("; generated by rustsharp\n\n");
            sb.Append(_types).Append('\n').Append(_globals).Append('\n');
            string code = _code.ToString();
            if (Sanitize || SanitizeThreads)
                code = System.Text.RegularExpressions.Regex.Replace(code, @"^(define .*\)) ?(.*)\{$", "$1 $2" + (Sanitize ? "sanitize_address" : "sanitize_thread") + " {", System.Text.RegularExpressions.RegexOptions.Multiline);
            sb.Append(code).Append('\n');
            foreach (var kv in _declares) sb.Append(kv.Value).Append('\n');
            return sb.ToString();
        }

        private void CompileMethod(MethodSymbol closed)
        {
            if (!_bodies.TryGetValue(closed.OriginalDefinition, out var body))
            {
                if (TryEmitRecordMember(closed)) return;
                _errors.Add("method has no body: " + closed.ToDisplayString());
                return;
            }
            _currentMethod = closed;
            var emitter = new FnEmitter(this, closed, body);
            if (OwnershipFacts.IsCoroutine(closed.OriginalDefinition)) emitter.EmitCoroutine();
            else emitter.Emit();
        }

        private void EmitMain(MethodSymbol entry, string main, string unhandled, string makeArgs)
        {
            var sb = _code;
            sb.Append("define i32 @main(i32 %argc, ptr %argv) {\n");
            string call;
            bool returnsInt = entry.ReturnType.SpecialType == SpecialType.System_Int32 || _blockOnInt != null;
            string args = "";
            if (makeArgs != null)
            {
                sb.Append($"  %args = call ptr {makeArgs}(i32 %argc, ptr %argv)\n");
                args = "ptr %args";
            }
            if (_blockOn != null || _blockOnInt != null)
            {
                sb.Append($"  %task = call ptr {main}({args})\n");
                call = _blockOnInt != null ? $"call i32 {_blockOnInt}(ptr %task)" : $"call void {_blockOn}(ptr %task)";
            }
            else if (_mainResult != null)
            {
                sb.Append($"  %result = call {_mainResultType} {main}({args})\n");
                call = null;
            }
            else
            {
                call = $"call {(returnsInt ? "i32" : "void")} {main}({args})";
            }
            if (call != null) sb.Append(returnsInt ? $"  %r = {call}\n" : $"  {call}\n");
            sb.Append("  %p = load ptr, ptr @__pending\n  %has = icmp ne ptr %p, null\n  br i1 %has, label %bad, label %ok\n");
            sb.Append("bad:\n");
            if (unhandled != null) sb.Append($"  store ptr null, ptr @__pending\n  call void {unhandled}(ptr %p)\n");
            sb.Append("  ret i32 101\nok:\n");
            if (_mainResult != null)
            {
                sb.Append($"  %code = call i32 {_mainResult}({_mainResultType} %result)\n");
                sb.Append("  %p2 = load ptr, ptr @__pending\n  %has2 = icmp ne ptr %p2, null\n  br i1 %has2, label %bad2, label %done\n");
                sb.Append("bad2:\n  ret i32 101\ndone:\n  ret i32 %code\n");
            }
            else sb.Append(returnsInt ? "  ret i32 %r\n" : "  ret i32 0\n");
            sb.Append("}\n\n");
        }

        private void EmitRuntime()
        {
            Declare("calloc", "declare noalias ptr @calloc(i64, i64)");
            Declare("free", "declare void @free(ptr)");
            Declare("llvm.memcpy.p0.p0.i64", "declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)");
            Declare("write", "declare i64 @write(i32, ptr, i64)");
            Declare("exit", "declare void @exit(i32) noreturn");
            _globals.Append("@__pending = internal thread_local global ptr null\n");
            _globals.Append("@__panic_loc = internal thread_local global ptr null\n");

            void Panic(string name, string message)
            {
                var bytes = Encoding.UTF8.GetBytes(message + "\n");
                string lit = string.Concat(bytes.Select(b => "\\" + b.ToString("X2")));
                _globals.Append($"@msg.{name} = private constant [{bytes.Length} x i8] c\"{lit}\"\n");
                _code.Append($"define internal void @__panic_{name}() noreturn cold noinline {{\n  call i64 @write(i32 2, ptr @msg.{name}, i64 {bytes.Length})\n  call void @exit(i32 134)\n  unreachable\n}}\n\n");
            }

            Panic("null", "panic: null reference");
            Panic("bounds", "panic: index out of range");
            Panic("div", "panic: division by zero");
            Panic("cast", "panic: invalid cast");
            Panic("oom", "panic: out of memory");
            Panic("size", "panic: negative array size");
            Panic("dispatch", "panic: no implementation for virtual call");
            Panic("overflow", "panic: arithmetic overflow");
            Panic("clone", "panic: value does not implement Clone");

            _code.Append(@"define internal ptr @__alloc(i64 %n) {
  %p = call ptr @calloc(i64 1, i64 %n)
  %bad = icmp eq ptr %p, null
  br i1 %bad, label %oom, label %ok
oom:
  call void @__panic_oom()
  unreachable
ok:
  ret ptr %p
}

; A string handle is { i64 type id, i32 handle state, i32 length, ptr bytes, i32 capacity }; the bytes
; sit behind an i64 count that static literals set to -1. Retaining makes a new handle on the same
; bytes, so every handle has one owner and a change copies shared bytes first (see String.MakeUnique).
define internal ptr @__str_retain(ptr %s) {
  %isnull = icmp eq ptr %s, null
  br i1 %isnull, label %null, label %live
null:
  ret ptr null
live:
  %h = call ptr @__alloc(i64 32)
  call void @llvm.memcpy.p0.p0.i64(ptr %h, ptr %s, i64 32, i1 false)
  %state = getelementptr i8, ptr %h, i64 8
  store i32 1, ptr %state
  %dp = getelementptr i8, ptr %s, i64 16
  %data = load ptr, ptr %dp
  %cp = getelementptr i8, ptr %data, i64 -8
  %count = load atomic i64, ptr %cp monotonic, align 8
  %static = icmp slt i64 %count, 0
  br i1 %static, label %done, label %inc
inc:
  %old = atomicrmw add ptr %cp, i64 1 monotonic
  br label %done
done:
  ret ptr %h
}

define internal void @__str_release(ptr %s) {
  %isnull = icmp eq ptr %s, null
  br i1 %isnull, label %done, label %live
live:
  %state = getelementptr i8, ptr %s, i64 8
  %st = load i32, ptr %state
  %template = icmp slt i32 %st, 0
  br i1 %template, label %done, label %bytes
bytes:
  %dp = getelementptr i8, ptr %s, i64 16
  %data = load ptr, ptr %dp
  %cp = getelementptr i8, ptr %data, i64 -8
  %count = load atomic i64, ptr %cp monotonic, align 8
  %static = icmp slt i64 %count, 0
  br i1 %static, label %handle, label %dec
dec:
  %old = atomicrmw sub ptr %cp, i64 1 acq_rel
  %last = icmp eq i64 %old, 1
  br i1 %last, label %freebytes, label %handle
freebytes:
  call void @free(ptr %cp)
  br label %handle
handle:
  call void @free(ptr %s)
  br label %done
done:
  ret void
}

");
        }

        private string StringLiteral(string value)
        {
            if (_strings.TryGetValue(value, out var name)) return name;
            name = "@str." + _strings.Count;
            _strings[value] = name;
            // UTF-8 bytes behind a count of -1, and a template handle (state -1) that is never freed.
            var bytes = System.Text.Encoding.UTF8.GetBytes(value);
            int n = bytes.Length + 1;
            var text = string.Join(", ", bytes.Select(b => "i8 " + b).Append("i8 0"));
            _globals.Append($"{name}.bytes = private constant {{ i64, [{n} x i8] }} {{ i64 -1, [{n} x i8] [{text}] }}, align 8\n");
            _globals.Append($"{name} = private global {{ i64, i32, i32, ptr, i32 }} {{ i64 1, i32 -1, i32 {bytes.Length}, ptr getelementptr inbounds ({{ i64, [{n} x i8] }}, ptr {name}.bytes, i32 0, i32 1), i32 -1 }}, align 8\n");
            return name;
        }

        // ---- statics

        private string StaticGlobal(FieldSymbol closed)
        {
            string key = closed.ContainingType.ToDisplayString() + "::" + closed.Name;
            if (_statics.TryGetValue(key, out var name)) return name;
            name = Unique("static." + key);
            _statics[key] = name;
            string ty = closed.RefKind != RefKind.None ? "ptr" : Ty(closed.Type);
            bool perThread = closed.OriginalDefinition.GetAttributes().Any(a => a.AttributeClass?.Name == "ThreadStaticAttribute");
            _globals.Append($"{name} = internal {(perThread ? "thread_local " : "")}global {ty} zeroinitializer\n");

            // All threads can reach a readonly static without any synchronization.
            if (closed.IsReadOnly && !OwnershipFacts.IsSync(closed.Type))
                Report(ErrorCode.ERR_OwnNotSync, $"`{closed.Type.ToDisplayString()}` cannot be shared between threads safely", closed.GetNonNullSyntaxNode(), "a readonly static must be Sync");
            return name;
        }

        /// <summary>A per-type once-guard around the static constructor, or null when there is none.</summary>
        private string CctorGuard(NamedTypeSymbol closed)
        {
            if (_guards.TryGetValue(closed, out var guard)) return guard;
            var cctor = closed.GetMembers(WellKnownMemberNames.StaticConstructorName).OfType<MethodSymbol>().FirstOrDefault();
            if (cctor is null || !_bodies.ContainsKey(cctor.OriginalDefinition))
            {
                _guards[closed] = null;
                return null;
            }

            guard = Unique("cctor.guard." + closed.ToDisplayString());
            _guards[closed] = guard;
            // 0 = not started, 1 = finished, anything else = the thread running it. That thread may reach
            // the guard again through a cycle between static constructors, and must not wait for itself.
            string flag = Unique("cctor.flag");
            _globals.Append($"{flag} = internal global i64 0\n");
            string fn = Fn(cctor);
            Declare("pthread_self", "declare i64 @pthread_self()");
            Declare("sched_yield", "declare i32 @sched_yield()");
            _code.Append($@"define internal void {guard}() {{
  %f = load atomic i64, ptr {flag} acquire, align 8
  %ran = icmp eq i64 %f, 1
  br i1 %ran, label %done, label %claim
claim:
  %me = call i64 @pthread_self()
  %pair = cmpxchg ptr {flag}, i64 0, i64 %me acq_rel acquire
  %won = extractvalue {{ i64, i1 }} %pair, 1
  br i1 %won, label %run, label %busy
run:
  call void {fn}()
  store atomic i64 1, ptr {flag} release, align 8
  br label %done
busy:
  %owner = extractvalue {{ i64, i1 }} %pair, 0
  %mine = icmp eq i64 %owner, %me
  br i1 %mine, label %done, label %wait
wait:
  %now = load atomic i64, ptr {flag} acquire, align 8
  %finished = icmp eq i64 %now, 1
  br i1 %finished, label %done, label %spin
spin:
  %y = call i32 @sched_yield()
  br label %wait
done:
  ret void
}}

");
            return guard;
        }

        // ---- drop glue

        private string DropFn(TypeSymbol t)
        {
            if (_drops.TryGetValue(t, out var name)) return name;
            name = Unique("drop." + t.ToDisplayString());
            _drops[t] = name;
            _dropWork.Enqueue(t);
            return name;
        }

        private void EmitDropGlue(TypeSymbol t)
        {
            var sb = _code;
            string name = _drops[t];
            sb.Append($"define internal void {name}(ptr %slot) {{\n");
            if (IsHandle(t))
            {
                sb.Append("  %v = load ptr, ptr %slot\n  %isnull = icmp eq ptr %v, null\n  br i1 %isnull, label %done, label %live\nlive:\n  store ptr null, ptr %slot\n");
                sb.Append("  call void @__dropobj(ptr %v)\n  br label %done\ndone:\n  ret void\n}\n\n");
                return;
            }

            var layout = LayoutOf(t);
            int tmp = 0;
            var dtor = OwnershipFacts.FindDestructor(t);
            if (dtor != null)
            {
                sb.Append($"  %alive.p = getelementptr {layout.LlvmType}, ptr %slot, i32 0, i32 {layout.AliveIndex}\n");
                sb.Append("  %alive = load i8, ptr %alive.p\n  %live = icmp ne i8 %alive, 0\n  br i1 %live, label %run, label %done\nrun:\n");
                sb.Append("  store i8 0, ptr %alive.p\n");
                sb.Append($"  call void {Fn(dtor)}(ptr %slot)\n");
            }
            EmitFieldDrops(sb, layout, "%slot", ref tmp);
            if (dtor != null) sb.Append("  br label %done\ndone:\n");
            sb.Append("  ret void\n}\n\n");
        }

        private void EmitFieldDrops(StringBuilder sb, Layout layout, string baseName, ref int tmp)
        {
            foreach (var f in layout.Fields)
            {
                if (f.RefKind != RefKind.None || !OwnershipFacts.NeedsDrop(f.Type) || OwnershipFacts.IsLinkField(f)) continue;
                int t = tmp++;
                sb.Append($"  %f{t} = getelementptr {layout.LlvmType}, ptr {baseName}, i32 0, i32 {layout.Index[f.OriginalDefinition]}\n");
                sb.Append($"  call void {DropFn(f.Type)}(ptr %f{t})\n");
            }
        }

        private static string ObjGlueName(ObjType o) => "@__dropbody." + o.Id;

        private void EmitObjectGlue(ObjType o)
        {
            var sb = _code;
            if (o.Kind == ObjKind.String) return;
            sb.Append($"define internal void {ObjGlueName(o)}(ptr %o) {{\n");
            int tmp = 0;
            switch (o.Kind)
            {
                case ObjKind.Class:
                {
                    for (var t = o.Type; t is not null; t = t.BaseTypeNoUseSiteDiagnostics)
                    {
                        var dtor = OwnershipFacts.FindDestructor(t);
                        if (dtor != null)
                        {
                            sb.Append($"  call void {Fn(dtor)}(ptr %o)\n");
                            break;
                        }
                    }
                    if (o.Type.IsDelegateType())
                    {
                        // Delegate._owner is the owned receiver's address, 0 when the closure only borrows.
                        sb.Append("  %ownp = getelementptr i8, ptr %o, i64 8\n  %own = load ptr, ptr %ownp\n  %noown = icmp eq ptr %own, null\n");
                        sb.Append("  br i1 %noown, label %owndone, label %ownlive\nownlive:\n  call void @__dropobj(ptr %own)\n  br label %owndone\nowndone:\n");
                    }
                    EmitFieldDrops(sb, LayoutOf(o.Type), "%o", ref tmp);
                    break;
                }
                case ObjKind.Box:
                    if (OwnershipFacts.NeedsDrop(o.Type))
                        sb.Append($"  %p = getelementptr i8, ptr %o, i64 8\n  call void {DropFn(o.Type)}(ptr %p)\n");
                    break;
                case ObjKind.Array:
                {
                    var array = (ArrayTypeSymbol)o.Type;
                    var element = array.ElementType;
                    if (OwnershipFacts.NeedsDrop(element))
                    {
                        string ety = Ty(element);
                        sb.Append($"  %lenp = getelementptr i8, ptr %o, i64 8\n  %len = load i64, ptr %lenp\n  %data = getelementptr i8, ptr %o, i64 {ArrayDataOffset(array.Rank)}\n  br label %head\n");
                        sb.Append("head:\n  %i = phi i64 [ 0, %0 ], [ %next, %body ]\n  %more = icmp ult i64 %i, %len\n  br i1 %more, label %body, label %end\n");
                        sb.Append($"body:\n  %e = getelementptr {ety}, ptr %data, i64 %i\n  call void {DropFn(element)}(ptr %e)\n  %next = add i64 %i, 1\n  br label %head\nend:\n");
                    }
                    break;
                }
            }
            sb.Append("  call void @free(ptr %o)\n  ret void\n}\n\n");
        }

        private void EmitDropObj()
        {
            var sb = _code;
            sb.Append("define internal void @__dropobj(ptr %o) {\n  %id = load i64, ptr %o\n  switch i64 %id, label %bad [\n");
            foreach (var o in _objs) sb.Append($"    i64 {o.Id}, label %t{o.Id}\n");
            sb.Append("  ]\nbad:\n  call void @__panic_dispatch()\n  unreachable\n");
            foreach (var o in _objs)
            {
                sb.Append($"t{o.Id}:\n");
                sb.Append(o.Kind == ObjKind.String ? "  call void @__str_release(ptr %o)\n" : $"  call void {ObjGlueName(o)}(ptr %o)\n");
                sb.Append("  ret void\n");
            }
            sb.Append("}\n\n");
        }

        // ---- dispatch

        private string DispatchStub(MethodSymbol closed)
        {
            if (!_dispatch.TryGetValue(closed, out var d))
            {
                d = new Dispatch { Method = closed, Name = Unique("virt." + closed.ToDisplayString()) };
                _dispatch[closed] = d;
            }
            return d.Name;
        }

        private void AddDispatchCase(Dispatch d, ObjType o)
        {
            if (o.Kind == ObjKind.Array) return;
            if (!Assignable(o, d.Method.ContainingType)) return;
            if (o.Type.IsAnonymousType && d.Method.Name == "ToString" && d.Method.ParameterCount == 0)
            {
                d.Cases[o.Id] = (AnonymousToString(o), false);
                return;
            }
            if (o.Type.IsAnonymousType && d.Method.Name == "GetHashCode" && d.Method.ParameterCount == 0)
            {
                d.Cases[o.Id] = (HashOfThis(o.Type), false);
                return;
            }
            var impl = FindImpl(o.Type, d.Method);
            if (impl is null || impl.IsAbstract) return;
            d.Cases[o.Id] = (Fn(impl), o.Kind == ObjKind.Box && impl.ContainingType.IsValueType);
        }

        /// <summary>
        /// `{ A = 1, B = x }`. Written here because Roslyn's generated ToString moves every field into a
        /// boxed argument, which would empty the object it is supposed to print.
        /// </summary>
        private string AnonymousToString(ObjType o)
        {
            string name = Unique("anon.tostring");
            var names = ((AnonymousTypeManager.AnonymousTypePublicSymbol)o.Type).Properties;
            var layout = LayoutOf(o.Type);
            EmitMembersToString(name, layout, layout.Fields.Select((f, i) => (f, names[i].Name)).ToList(), "{ ");
            return name;
        }

        private void EmitMembersToString(string name, Layout layout, List<(FieldSymbol Field, string Label)> members, string opening, string closing = " }", bool labels = true)
        {
            var compilationString = _compilation.GetSpecialType(SpecialType.System_String);
            var concat = compilationString.GetMembers("Concat").OfType<MethodSymbol>().First(m => m.ParameterCount == 2 && m.Parameters[0].Type.SpecialType == SpecialType.System_String);
            string concatFn = Fn(concat);
            var objectToString = _compilation.GetSpecialType(SpecialType.System_Object).GetMembers("ToString").OfType<MethodSymbol>().First();

            var sb = new StringBuilder($"define internal ptr {name}(ptr %self) {{\n");
            int tmp = 0;
            string acc = StringLiteral(opening);
            for (int i = 0; i < members.Count; i++)
            {
                var f = members[i].Field;
                var type = f.Type;
                string prefix = (i > 0 ? ", " : "") + (labels ? members[i].Label + " = " : "");
                sb.Append($"  %a{tmp} = call ptr {concatFn}(ptr {acc}, ptr {StringLiteral(prefix)})\n");
                acc = "%a" + tmp++;
                sb.Append($"  %p{tmp} = getelementptr {layout.LlvmType}, ptr %self, i32 0, i32 {layout.Index[f.OriginalDefinition]}\n");
                string slot = "%p" + tmp++;
                string text;
                if (OwnershipFacts.IsString(type))
                {
                    sb.Append($"  %v{tmp} = load ptr, ptr {slot}\n  %s{tmp} = call ptr @__str_retain(ptr %v{tmp})\n");
                    text = "%s" + tmp++;
                }
                else if (IsHandle(type))
                {
                    int n = tmp++;
                    sb.Append($"  %h{n} = load ptr, ptr {slot}\n  %isnull{n} = icmp eq ptr %h{n}, null\n  br i1 %isnull{n}, label %nil{n}, label %obj{n}\n");
                    sb.Append($"obj{n}:\n  %r{n} = call ptr {DispatchStub(objectToString)}(ptr %h{n})\n  br label %join{n}\nnil{n}:\n  br label %join{n}\n");
                    sb.Append($"join{n}:\n  %t{n} = phi ptr [ %r{n}, %obj{n} ], [ null, %nil{n} ]\n");
                    text = "%t" + n;
                }
                else
                {
                    var impl = FindImpl(type, objectToString);
                    if (impl is { ContainingType.IsValueType: true })
                    {
                        sb.Append($"  %s{tmp} = call ptr {Fn(impl)}(ptr {slot})\n");
                        text = "%s" + tmp++;
                    }
                    else
                    {
                        text = StringLiteral(type.ToDisplayString());
                    }
                }
                sb.Append($"  %a{tmp} = call ptr {concatFn}(ptr {acc}, ptr {text})\n");
                acc = "%a" + tmp++;
            }
            sb.Append($"  %end = call ptr {concatFn}(ptr {acc}, ptr {StringLiteral(closing)})\n  ret ptr %end\n}}\n\n");
            _code.Append(sb);
        }

        private void EmitDispatch(Dispatch d)
        {
            var sb = _code;
            var m = d.Method;
            string ret = ReturnTy(m);
            var tys = ParamTys(m);
            var ps = tys.Select((t, i) => $"{t} %a{i}").ToList();
            sb.Append($"define internal {ret} {d.Name}({string.Join(", ", ps)}) {{\n");
            // A call on null raises the exception; the caller's check after the call picks it up.
            string zero = ret == "void" ? "ret void" : ret == "ptr" ? "ret ptr null" : $"ret {ret} zeroinitializer";
            sb.Append($"  %isnull = icmp eq ptr %a0, null\n  br i1 %isnull, label %nil, label %go\nnil:\n  %e = call ptr {FaultFn("Null")}()\n  store ptr %e, ptr @__pending\n  {zero}\ngo:\n");
            sb.Append("  %id = load i64, ptr %a0\n  switch i64 %id, label %bad [\n");
            foreach (var id in d.Cases.Keys) sb.Append($"    i64 {id}, label %t{id}\n");
            sb.Append("  ]\nbad:\n  call void @__panic_dispatch()\n  unreachable\n");
            foreach (var (id, c) in d.Cases)
            {
                sb.Append($"t{id}:\n");
                string self = "%a0";
                if (c.Unbox)
                {
                    sb.Append($"  %self{id} = getelementptr i8, ptr %a0, i64 8\n");
                    self = "%self" + id;
                }
                var args = new List<string> { "ptr " + self };
                args.AddRange(ps.Skip(1));
                string call = $"call {ret} {c.Fn}({string.Join(", ", args)})";
                if (ret == "void") sb.Append($"  {call}\n  ret void\n");
                else sb.Append($"  %r{id} = {call}\n  ret {ret} %r{id}\n");
            }
            sb.Append("}\n\n");
        }

        /// <summary>A non-capturing lambda ignores its receiver, so a delegate can call it without one.</summary>
        private string ReceiverlessThunk(MethodSymbol method)
        {
            string target = Fn(method);
            string name = Unique("thunk." + method.ToDisplayString());
            string ret = ReturnTy(method);
            var tys = ParamTys(method).Skip(1).ToList();
            var ps = tys.Select((t, i) => $"{t} %a{i}").ToList();
            string args = string.Join(", ", new[] { "ptr null" }.Concat(ps));
            _code.Append($"define internal {ret} {name}({string.Join(", ", ps)}) {{\n");
            if (ret == "void") _code.Append($"  call void {target}({args})\n  ret void\n}}\n\n");
            else _code.Append($"  %r = call {ret} {target}({args})\n  ret {ret} %r\n}}\n\n");
            return name;
        }

        private string IsInstFnName(TypeSymbol target)
        {
            if (!_isInst.TryGetValue(target, out var f))
            {
                f = new IsInstFn { Target = target, Name = Unique("isinst." + target.ToDisplayString()) };
                _isInst[target] = f;
            }
            return f.Name;
        }

        private void EmitIsInst(IsInstFn f)
        {
            var sb = _code;
            sb.Append($"define internal i8 {f.Name}(ptr %o) {{\n  %isnull = icmp eq ptr %o, null\n  br i1 %isnull, label %no, label %go\ngo:\n  %id = load i64, ptr %o\n  switch i64 %id, label %no [\n");
            foreach (var o in _objs.Where(o => Assignable(o, f.Target))) sb.Append($"    i64 {o.Id}, label %yes\n");
            sb.Append("  ]\nyes:\n  ret i8 1\nno:\n  ret i8 0\n}\n\n");
        }
    }
}
