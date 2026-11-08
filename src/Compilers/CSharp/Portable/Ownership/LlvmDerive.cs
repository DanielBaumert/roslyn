// RustSharp: structural glue that Rust would get from #[derive]: Clone, PartialEq, Hash and Debug-style
// ToString. Records and anonymous types use it for the members Roslyn would otherwise synthesize.

using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.CodeAnalysis.CSharp.Symbols;

namespace Microsoft.CodeAnalysis.CSharp.Ownership
{
    internal sealed partial class LlvmBackend
    {
        private bool _needClone, _needEq, _needHash, _needTypeName;

        private static readonly SymbolDisplayFormat s_typeNames = new SymbolDisplayFormat(
            typeQualificationStyle: SymbolDisplayTypeQualificationStyle.NameAndContainingTypesAndNamespaces,
            genericsOptions: SymbolDisplayGenericsOptions.IncludeTypeParameters);

        private string TypeName(TypeSymbol t) => t.ToDisplayString(s_typeNames);

        /// <summary>Static types that get cloned: only objects assignable to one of them need clone code.</summary>
        private readonly HashSet<TypeSymbol> _cloneTargets = new HashSet<TypeSymbol>(s_cmp);
        private readonly Dictionary<TypeSymbol, string> _clones = new Dictionary<TypeSymbol, string>(s_cmp);
        private readonly Dictionary<TypeSymbol, string> _eqs = new Dictionary<TypeSymbol, string>(s_cmp);
        private readonly Dictionary<TypeSymbol, string> _hashes = new Dictionary<TypeSymbol, string>(s_cmp);

        private static string ObjCloneName(ObjType o) => "@__clonebody." + o.Id;
        private static string ObjEqName(ObjType o) => "@__eqbody." + o.Id;
        private static string ObjHashName(ObjType o) => "@__hashbody." + o.Id;

        private static bool HasStructuralEquality(TypeSymbol t)
            => t.IsAnonymousType || t.IsRecord || t.IsRecordStruct || OwnershipFacts.HasAttribute(t, "EqAttribute");

        /// <summary>
        /// Ref&lt;T&gt; and RefMut&lt;T&gt; compare, test and hash what they point at, like Rust's impls for &amp;T.
        /// Emits a load of the pointer in <paramref name="slot"/> into <c>%{name}</c> and returns T.
        /// </summary>
        private TypeSymbol DerefReference(StringBuilder sb, TypeSymbol t, string slot, string name)
        {
            if (!OwnershipFacts.IsReference(t)) return null;
            var layout = LayoutOf(t);
            var field = layout.Fields.First(f => f.Type is PointerTypeSymbol);
            sb.Append($"  %{name}.f = getelementptr {layout.LlvmType}, ptr {slot}, i32 0, i32 {layout.Index[field.OriginalDefinition]}\n  %{name} = load ptr, ptr %{name}.f\n");
            return ((PointerTypeSymbol)field.Type).PointedAtType;
        }

        private readonly Dictionary<TypeSymbol, string> _compares = new Dictionary<TypeSymbol, string>(s_cmp);

        /// <summary><c>i32 compare(ptr a, ptr b)</c>: negative, zero or positive, like Rust's Ord.</summary>
        public string CompareFn(TypeSymbol t)
        {
            if (_compares.TryGetValue(t, out var name)) return name;
            name = Unique("cmp." + t.ToDisplayString());
            _compares[t] = name;
            var sb = new StringBuilder($"define internal i32 {name}(ptr %a, ptr %b) {{\n");
            string ty = Ty(t);
            var u = Unenum(t);
            bool handle = IsHandle(t);

            if (DerefReference(sb, t, "%a", "ra") is { } ordTarget)
            {
                DerefReference(sb, t, "%b", "rb");
                sb.Append($"  %r = call i32 {CompareFn(ordTarget)}(ptr %ra, ptr %rb)\n  ret i32 %r\n");
            }
            else if (OwnershipFacts.UserTrait(t, "IOrd", "Compare", generic: true) is { } user)
            {
                string self = "%a";
                if (handle) { sb.Append("  %self = load ptr, ptr %a\n"); self = "%self"; }
                sb.Append($"  %r = call i32 {Fn(user)}(ptr {self}, ptr %b)\n  ret i32 %r\n");
            }
            else if (OwnershipFacts.IsString(t))
            {
                var compare = _compilation.GetSpecialType(SpecialType.System_String).GetMembers("CompareOrdinal").OfType<MethodSymbol>().First();
                sb.Append($"  %r = call i32 {Fn(compare)}(ptr %a, ptr %b)\n  ret i32 %r\n");
            }
            else if (ty is "float" or "double" or "i8" or "i16" or "i32" or "i64")
            {
                bool isFloat = ty is "float" or "double";
                bool signed = u.SpecialType is SpecialType.System_SByte or SpecialType.System_Int16 or SpecialType.System_Int32 or SpecialType.System_Int64 or SpecialType.System_IntPtr;
                string lt = isFloat ? "fcmp olt" : signed ? "icmp slt" : "icmp ult";
                string gt = isFloat ? "fcmp ogt" : signed ? "icmp sgt" : "icmp ugt";
                sb.Append($"  %x = load {ty}, ptr %a\n  %y = load {ty}, ptr %b\n  %l = {lt} {ty} %x, %y\n  %g = {gt} {ty} %x, %y\n");
                sb.Append("  %li = zext i1 %l to i32\n  %gi = zext i1 %g to i32\n  %r = sub i32 %gi, %li\n  ret i32 %r\n");
            }
            else if (t is NamedTypeSymbol)
            {
                var layout = LayoutOf(t);
                string left = "%a", right = "%b";
                if (handle)
                {
                    sb.Append("  %x = load ptr, ptr %a\n  %y = load ptr, ptr %b\n");
                    left = "%x";
                    right = "%y";
                }
                int n = 0;
                foreach (var f in layout.Fields)
                {
                    if (f.RefKind != RefKind.None) continue;
                    int i = layout.Index[f.OriginalDefinition];
                    sb.Append($"  %pa{n} = getelementptr {layout.LlvmType}, ptr {left}, i32 0, i32 {i}\n  %pb{n} = getelementptr {layout.LlvmType}, ptr {right}, i32 0, i32 {i}\n");
                    sb.Append($"  %c{n} = call i32 {CompareFn(f.Type)}(ptr %pa{n}, ptr %pb{n})\n  %z{n} = icmp eq i32 %c{n}, 0\n  br i1 %z{n}, label %f{n + 1}, label %out{n}\nout{n}:\n  ret i32 %c{n}\nf{n + 1}:\n");
                    n++;
                }
                sb.Append("  ret i32 0\n");
            }
            else
            {
                sb.Append("  ret i32 0\n");
            }

            _code.Append(sb.Append("}\n\n"));
            return name;
        }

        private string ObjectSize(StringBuilder sb, TypeSymbol type, string result)
        {
            sb.Append($"  %{result}.g = getelementptr {LayoutOf(type).LlvmType}, ptr null, i32 1\n  %{result} = ptrtoint ptr %{result}.g to i64\n");
            return "%" + result;
        }

        private string ElementSize(StringBuilder sb, TypeSymbol type, string result)
        {
            sb.Append($"  %{result}.g = getelementptr {Ty(type)}, ptr null, i32 1\n  %{result} = ptrtoint ptr %{result}.g to i64\n");
            return "%" + result;
        }

        /// <summary><c>T clone(ptr slot)</c>: a deep copy of the value in a slot.</summary>
        public string CloneFn(TypeSymbol t)
        {
            if (_clones.TryGetValue(t, out var name)) return name;
            name = Unique("clone." + t.ToDisplayString());
            _clones[t] = name;
            string ty = Ty(t);
            var sb = new StringBuilder($"define internal {ty} {name}(ptr %s) {{\n");

            if (OwnershipFacts.IsString(t))
            {
                sb.Append("  %v = load ptr, ptr %s\n  %r = call ptr @__str_retain(ptr %v)\n  ret ptr %r\n");
            }
            else if (IsHandle(t))
            {
                _needClone = true;
                _cloneTargets.Add(t);
                sb.Append("  %v = load ptr, ptr %s\n  %isnull = icmp eq ptr %v, null\n  br i1 %isnull, label %nil, label %obj\nnil:\n  ret ptr null\n");
                sb.Append("obj:\n  %r = call ptr @__cloneobj(ptr %v)\n  ret ptr %r\n");
            }
            else if (!OwnershipFacts.NeedsDrop(t))
            {
                sb.Append($"  %v = load {ty}, ptr %s\n  ret {ty} %v\n");
            }
            else if (OwnershipFacts.UserClone(t) is { } user)
            {
                sb.Append($"  %r = call {ty} {Fn(user)}(ptr %s)\n  ret {ty} %r\n");
            }
            else
            {
                var layout = LayoutOf(t);
                sb.Append($"  %r = alloca {ty}\n  %v = load {ty}, ptr %s\n  store {ty} %v, ptr %r\n");
                int n = 0;
                foreach (var f in layout.Fields)
                {
                    if (f.RefKind != RefKind.None || !OwnershipFacts.NeedsDrop(f.Type)) continue;
                    int i = layout.Index[f.OriginalDefinition];
                    string fty = Ty(f.Type);
                    sb.Append($"  %f{n} = getelementptr {layout.LlvmType}, ptr %s, i32 0, i32 {i}\n  %c{n} = call {fty} {CloneFn(f.Type)}(ptr %f{n})\n");
                    sb.Append($"  %d{n} = getelementptr {layout.LlvmType}, ptr %r, i32 0, i32 {i}\n  store {fty} %c{n}, ptr %d{n}\n");
                    n++;
                }
                sb.Append($"  %out = load {ty}, ptr %r\n  ret {ty} %out\n");
            }

            _code.Append(sb.Append("}\n\n"));
            return name;
        }

        private void EmitObjectClone(ObjType o)
        {
            if (o.Kind == ObjKind.String) return;
            Declare("llvm.memcpy.p0.p0.i64", "declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)");
            var sb = new StringBuilder($"define internal ptr {ObjCloneName(o)}(ptr %o) {{\n");
            switch (o.Kind)
            {
                case ObjKind.Class:
                {
                    if (OwnershipFacts.UserClone(o.Type) is { } user)
                    {
                        sb.Append($"  %u = call ptr {Fn(user)}(ptr %o)\n  ret ptr %u\n}}\n\n");
                        _code.Append(sb);
                        return;
                    }
                    if (!OwnershipFacts.IsClone(o.Type))
                    {
                        sb.Append("  call void @__panic_clone()\n  unreachable\n}\n\n");
                        _code.Append(sb);
                        return;
                    }
                    var layout = LayoutOf(o.Type);
                    string size = ObjectSize(sb, o.Type, "size");
                    sb.Append($"  %r = call ptr @__alloc(i64 {size})\n  call void @llvm.memcpy.p0.p0.i64(ptr %r, ptr %o, i64 {size}, i1 false)\n");
                    int n = 0;
                    foreach (var f in layout.Fields)
                    {
                        if (f.RefKind != RefKind.None || !OwnershipFacts.NeedsDrop(f.Type)) continue;
                        int i = layout.Index[f.OriginalDefinition];
                        string fty = Ty(f.Type);
                        sb.Append($"  %f{n} = getelementptr {layout.LlvmType}, ptr %o, i32 0, i32 {i}\n  %c{n} = call {fty} {CloneFn(f.Type)}(ptr %f{n})\n");
                        sb.Append($"  %d{n} = getelementptr {layout.LlvmType}, ptr %r, i32 0, i32 {i}\n  store {fty} %c{n}, ptr %d{n}\n");
                        n++;
                    }
                    break;
                }
                case ObjKind.Box:
                {
                    string size = ElementSize(sb, o.Type, "size");
                    string ty = Ty(o.Type);
                    sb.Append($"  %total = add i64 {size}, 8\n  %r = call ptr @__alloc(i64 %total)\n  store i64 {o.Id}, ptr %r\n");
                    sb.Append($"  %src = getelementptr i8, ptr %o, i64 8\n  %dst = getelementptr i8, ptr %r, i64 8\n  %v = call {ty} {CloneFn(o.Type)}(ptr %src)\n  store {ty} %v, ptr %dst\n");
                    break;
                }
                case ObjKind.Array:
                {
                    var array = (ArrayTypeSymbol)o.Type;
                    string ety = Ty(array.ElementType);
                    int offset = ArrayDataOffset(array.Rank);
                    string size = ElementSize(sb, array.ElementType, "size");
                    sb.Append($"  %lenp = getelementptr i8, ptr %o, i64 8\n  %len = load i64, ptr %lenp\n  %bytes = mul i64 %len, {size}\n  %total = add i64 %bytes, {offset}\n");
                    sb.Append("  %r = call ptr @__alloc(i64 %total)\n  call void @llvm.memcpy.p0.p0.i64(ptr %r, ptr %o, i64 %total, i1 false)\n");
                    if (OwnershipFacts.NeedsDrop(array.ElementType))
                    {
                        sb.Append($"  %from = getelementptr i8, ptr %o, i64 {offset}\n  %to = getelementptr i8, ptr %r, i64 {offset}\n  br label %head\n");
                        sb.Append("head:\n  %i = phi i64 [ 0, %0 ], [ %next, %body ]\n  %more = icmp ult i64 %i, %len\n  br i1 %more, label %body, label %end\n");
                        sb.Append($"body:\n  %e = getelementptr {ety}, ptr %from, i64 %i\n  %c = call {ety} {CloneFn(array.ElementType)}(ptr %e)\n  %d = getelementptr {ety}, ptr %to, i64 %i\n  store {ety} %c, ptr %d\n  %next = add i64 %i, 1\n  br label %head\nend:\n");
                    }
                    break;
                }
            }
            _code.Append(sb.Append("  ret ptr %r\n}\n\n"));
        }

        /// <summary><c>i8 eq(ptr a, ptr b)</c> over two slots.</summary>
        public string EqFn(TypeSymbol t)
        {
            if (_eqs.TryGetValue(t, out var name)) return name;
            name = Unique("eq." + t.ToDisplayString());
            _eqs[t] = name;
            var sb = new StringBuilder($"define internal i8 {name}(ptr %a, ptr %b) {{\n");
            string ty = Ty(t);
            var u = Unenum(t);

            if (DerefReference(sb, t, "%a", "ra") is { } eqTarget)
            {
                DerefReference(sb, t, "%b", "rb");
                sb.Append($"  %r = call i8 {EqFn(eqTarget)}(ptr %ra, ptr %rb)\n  ret i8 %r\n");
            }
            else if (OwnershipFacts.UserTrait(t, "IEq", "Eq", generic: true) is { } user)
            {
                string self = "%a";
                if (IsHandle(t)) { sb.Append("  %self = load ptr, ptr %a\n"); self = "%self"; }
                sb.Append($"  %r = call i8 {Fn(user)}(ptr {self}, ptr %b)\n  ret i8 %r\n");
            }
            else if (OwnershipFacts.IsString(t))
            {
                var equals = _compilation.GetSpecialType(SpecialType.System_String).GetMembers(WellKnownMemberNames.EqualityOperatorName).OfType<MethodSymbol>().First();
                sb.Append($"  %x = load ptr, ptr %a\n  %y = load ptr, ptr %b\n  %rx = call ptr @__str_retain(ptr %x)\n  %ry = call ptr @__str_retain(ptr %y)\n  %r = call i8 {Fn(equals)}(ptr %rx, ptr %ry)\n  ret i8 %r\n");
            }
            else if (IsHandle(t))
            {
                _needEq = true;
                EqFn(_compilation.GetSpecialType(SpecialType.System_String)); // the object switch handles strings
                sb.Append("  %x = load ptr, ptr %a\n  %y = load ptr, ptr %b\n  %same = icmp eq ptr %x, %y\n  br i1 %same, label %yes, label %test\nyes:\n  ret i8 1\n");
                sb.Append("test:\n  %xn = icmp eq ptr %x, null\n  %yn = icmp eq ptr %y, null\n  %anynull = or i1 %xn, %yn\n  br i1 %anynull, label %no, label %ids\nno:\n  ret i8 0\n");
                sb.Append("ids:\n  %ix = load i64, ptr %x\n  %iy = load i64, ptr %y\n  %sameid = icmp eq i64 %ix, %iy\n  br i1 %sameid, label %deep, label %no\ndeep:\n  %r = call i8 @__eqobj(ptr %x, ptr %y)\n  ret i8 %r\n");
            }
            else if (ty is "float" or "double")
            {
                sb.Append($"  %x = load {ty}, ptr %a\n  %y = load {ty}, ptr %b\n  %c = fcmp oeq {ty} %x, %y\n  %r = zext i1 %c to i8\n  ret i8 %r\n");
            }
            else if (u.TypeKind == TypeKind.Pointer || ty.StartsWith("i", System.StringComparison.Ordinal))
            {
                sb.Append($"  %x = load {ty}, ptr %a\n  %y = load {ty}, ptr %b\n  %c = icmp eq {ty} %x, %y\n  %r = zext i1 %c to i8\n  ret i8 %r\n");
            }
            else
            {
                EmitFieldEq(sb, LayoutOf(t));
                sb.Append("  ret i8 1\n");
            }

            _code.Append(sb.Append("}\n\n"));
            return name;
        }

        private void EmitFieldEq(StringBuilder sb, Layout layout)
        {
            int n = 0;
            sb.Append("  br label %f0\n");
            foreach (var f in layout.Fields)
            {
                if (f.RefKind != RefKind.None) continue;
                int i = layout.Index[f.OriginalDefinition];
                sb.Append($"f{n}:\n  %pa{n} = getelementptr {layout.LlvmType}, ptr %a, i32 0, i32 {i}\n  %pb{n} = getelementptr {layout.LlvmType}, ptr %b, i32 0, i32 {i}\n");
                sb.Append($"  %e{n} = call i8 {EqFn(f.Type)}(ptr %pa{n}, ptr %pb{n})\n  %t{n} = icmp ne i8 %e{n}, 0\n  br i1 %t{n}, label %f{n + 1}, label %differ\n");
                n++;
            }
            sb.Append($"differ:\n  ret i8 0\nf{n}:\n");
        }

        private void EmitObjectEq(ObjType o)
        {
            if (o.Kind == ObjKind.String) return;
            var sb = new StringBuilder($"define internal i8 {ObjEqName(o)}(ptr %a, ptr %b) {{\n");
            if (o.Kind == ObjKind.Class && HasStructuralEquality(o.Type))
            {
                EmitFieldEq(sb, LayoutOf(o.Type));
                sb.Append("  ret i8 1\n");
            }
            else if (o.Kind == ObjKind.Box)
            {
                sb.Append($"  %x = getelementptr i8, ptr %a, i64 8\n  %y = getelementptr i8, ptr %b, i64 8\n  %r = call i8 {EqFn(o.Type)}(ptr %x, ptr %y)\n  ret i8 %r\n");
            }
            else
            {
                sb.Append("  %c = icmp eq ptr %a, %b\n  %r = zext i1 %c to i8\n  ret i8 %r\n");
            }
            _code.Append(sb.Append("}\n\n"));
        }

        /// <summary><c>i32 hash(ptr slot)</c>.</summary>
        public string HashFn(TypeSymbol t)
        {
            if (_hashes.TryGetValue(t, out var name)) return name;
            name = Unique("hash." + t.ToDisplayString());
            _hashes[t] = name;
            var sb = new StringBuilder($"define internal i32 {name}(ptr %s) {{\n");
            string ty = Ty(t);

            if (DerefReference(sb, t, "%s", "rs") is { } hashTarget)
            {
                sb.Append($"  %r = call i32 {HashFn(hashTarget)}(ptr %rs)\n  ret i32 %r\n");
            }
            else if (OwnershipFacts.UserTrait(t, "IHash", "Hash", generic: false) is { } user)
            {
                string self = "%s";
                if (IsHandle(t)) { sb.Append("  %self = load ptr, ptr %s\n"); self = "%self"; }
                sb.Append($"  %r = call i32 {Fn(user)}(ptr {self})\n  ret i32 %r\n");
            }
            else if (IsHandle(t))
            {
                _needHash = true;
                sb.Append("  %v = load ptr, ptr %s\n  %isnull = icmp eq ptr %v, null\n  br i1 %isnull, label %nil, label %obj\nnil:\n  ret i32 0\nobj:\n  %r = call i32 @__hashobj(ptr %v)\n  ret i32 %r\n");
            }
            else if (ty is "float" or "double")
            {
                string bits = ty == "float" ? "i32" : "i64";
                sb.Append($"  %v = load {bits}, ptr %s\n");
                sb.Append(bits == "i32" ? "  ret i32 %v\n" : "  %r = trunc i64 %v to i32\n  ret i32 %r\n");
            }
            else if (ty == "ptr")
            {
                sb.Append("  ret i32 0\n");
            }
            else if (ty.StartsWith("i", System.StringComparison.Ordinal))
            {
                sb.Append($"  %v = load {ty}, ptr %s\n");
                if (ty == "i32") sb.Append("  ret i32 %v\n");
                else if (ty == "i64") sb.Append("  %r = trunc i64 %v to i32\n  ret i32 %r\n");
                else sb.Append($"  %r = zext {ty} %v to i32\n  ret i32 %r\n");
            }
            else
            {
                EmitFieldHash(sb, LayoutOf(t), "%s");
            }

            _code.Append(sb.Append("}\n\n"));
            return name;
        }

        private void EmitFieldHash(StringBuilder sb, Layout layout, string self)
        {
            string acc = "17";
            int n = 0;
            foreach (var f in layout.Fields)
            {
                if (f.RefKind != RefKind.None) continue;
                sb.Append($"  %p{n} = getelementptr {layout.LlvmType}, ptr {self}, i32 0, i32 {layout.Index[f.OriginalDefinition]}\n  %h{n} = call i32 {HashFn(f.Type)}(ptr %p{n})\n");
                sb.Append($"  %m{n} = mul i32 {acc}, 31\n  %acc{n} = add i32 %m{n}, %h{n}\n");
                acc = "%acc" + n;
                n++;
            }
            sb.Append($"  ret i32 {acc}\n");
        }

        private void EmitObjectHash(ObjType o)
        {
            var sb = new StringBuilder($"define internal i32 {ObjHashName(o)}(ptr %o) {{\n");
            if (o.Kind == ObjKind.String)
            {
                var hash = _compilation.GetSpecialType(SpecialType.System_String).GetMembers("GetHashCode").OfType<MethodSymbol>().First();
                sb.Append($"  %r = call i32 {Fn(hash)}(ptr %o)\n  ret i32 %r\n");
            }
            else if (o.Kind == ObjKind.Class && HasStructuralEquality(o.Type))
            {
                EmitFieldHash(sb, LayoutOf(o.Type), "%o");
            }
            else if (o.Kind == ObjKind.Box)
            {
                sb.Append($"  %p = getelementptr i8, ptr %o, i64 8\n  %r = call i32 {HashFn(o.Type)}(ptr %p)\n  ret i32 %r\n");
            }
            else
            {
                sb.Append($"  ret i32 {o.Id}\n");
            }
            _code.Append(sb.Append("}\n\n"));
        }

        private void EmitObjectSwitches()
        {
            void Switch(string signature, string call, string ret, System.Func<ObjType, string> target, System.Func<ObjType, string> special = null)
            {
                var sb = _code;
                sb.Append($"{signature} {{\n  %id = load i64, ptr %a\n  switch i64 %id, label %bad [\n");
                foreach (var o in _objs) sb.Append($"    i64 {o.Id}, label %t{o.Id}\n");
                sb.Append("  ]\nbad:\n  call void @__panic_dispatch()\n  unreachable\n");
                foreach (var o in _objs)
                {
                    sb.Append($"t{o.Id}:\n");
                    if (special?.Invoke(o) is { } text) sb.Append(text);
                    else sb.Append($"  %r{o.Id} = call {ret} {target(o)}({call})\n  ret {ret} %r{o.Id}\n");
                }
                sb.Append("}\n\n");
            }

            if (_needClone)
                Switch("define internal ptr @__cloneobj(ptr %a)", "ptr %a", "ptr", ObjCloneName,
                    o => o.Kind == ObjKind.String ? "  %s = call ptr @__str_retain(ptr %a)\n  ret ptr %s\n"
                        : o.CloneDone ? null : "  call void @__panic_clone()\n  unreachable\n");
            if (_needEq)
                Switch("define internal i8 @__eqobj(ptr %a, ptr %b)", "ptr %a, ptr %b", "i8", ObjEqName,
                    o => o.Kind == ObjKind.String ? $"  %s = call i8 {_eqs[_compilation.GetSpecialType(SpecialType.System_String)]}(ptr %a, ptr %b)\n  ret i8 %s\n" : null);
            if (_needTypeName)
                Switch("define internal ptr @__typename(ptr %a)", "ptr %a", "ptr", null,
                    o => $"  ret ptr {StringLiteral(TypeName(o.Type))}\n");
            if (_needHash)
                Switch("define internal i32 @__hashobj(ptr %a)", "ptr %a", "i32", ObjHashName);
        }

        private string HashOfThis(TypeSymbol type)
        {
            _needHash = true;
            string name = Unique("hash.this");
            _code.Append($"define internal i32 {name}(ptr %self) {{\n  %r = call i32 @__hashobj(ptr %self)\n  ret i32 %r\n}}\n\n");
            return name;
        }

        /// <summary>Compiles a record member from the record's fields.</summary>
        private bool TryEmitRecordMember(MethodSymbol m)
        {
            var def = m.OriginalDefinition;
            string name = _fns[m];
            var type = m.ContainingType;
            bool isClass = !type.IsValueType;
            string ret = ReturnTy(m);
            var ps = ParamTys(m).Select((t, i) => $"{t} %a{i}");
            string header = $"define internal {ret} {name}({string.Join(", ", ps)}) {{\n";

            // Struct members receive `this` as a slot; classes pass the object, which needs one.
            string SelfSlot(StringBuilder sb)
            {
                if (!isClass) return "%a0";
                sb.Append("  %self = alloca ptr\n  store ptr %a0, ptr %self\n");
                return "%self";
            }

            switch (def)
            {
                case SynthesizedRecordClone:
                    _needClone = true;
                    _cloneTargets.Add(type);
                    _code.Append(header).Append("  %r = call ptr @__cloneobj(ptr %a0)\n  ret ptr %r\n}\n\n");
                    return true;
                case SynthesizedRecordToString:
                {
                    var layout = LayoutOf(type);
                    var members = layout.Fields
                        .Where(f => (f.AssociatedSymbol ?? f).DeclaredAccessibility == Accessibility.Public)
                        .Select(f => (f, (f.AssociatedSymbol ?? f).Name)).ToList();
                    // A variant of an enum with data prints as Rust's Debug does: `Rect(1, 2)`, `Empty`.
                    if (type.OriginalDefinition.DeclaringSyntaxReferences.Any(r => UnionSyntax.IsVariant(r.GetSyntax())))
                        EmitMembersToString(name, layout, members, members.Count == 0 ? type.Name : type.Name + "(", members.Count == 0 ? "" : ")", labels: false);
                    else
                        EmitMembersToString(name, layout, members, type.Name + " { ");
                    return true;
                }
                case SynthesizedRecordGetHashCode:
                {
                    var sb = new StringBuilder(header);
                    string slot = SelfSlot(sb);
                    sb.Append($"  %r = call i32 {HashFn(type)}(ptr {slot})\n  ret i32 %r\n}}\n\n");
                    _code.Append(sb);
                    return true;
                }
                case SynthesizedRecordEquals:
                case SynthesizedRecordBaseEquals:
                {
                    // Dynamic path, as through IEquatable<T>: the argument was passed by value.
                    var sb = new StringBuilder(header);
                    string slot = SelfSlot(sb);
                    string ty = Ty(m.Parameters[0].Type);
                    sb.Append($"  %other = alloca {ty}\n  store {ty} %a1, ptr %other\n  %r = call i8 {EqFn(type)}(ptr {slot}, ptr %other)\n");
                    if (OwnershipFacts.NeedsDrop(m.Parameters[0].Type)) sb.Append($"  call void {DropFn(m.Parameters[0].Type)}(ptr %other)\n");
                    _code.Append(sb).Append("  ret i8 %r\n}\n\n");
                    return true;
                }
                case SynthesizedRecordObjEquals:
                {
                    var sb = new StringBuilder(header);
                    string test = IsInstFnName(isClass ? type : type);
                    sb.Append($"  %other = alloca ptr\n  store ptr %a1, ptr %other\n");
                    if (isClass)
                    {
                        string slot = SelfSlot(sb);
                        sb.Append($"  %is = call i8 {test}(ptr %a1)\n  %ok = icmp ne i8 %is, 0\n  br i1 %ok, label %cmp, label %no\ncmp:\n  %r = call i8 {EqFn(type)}(ptr {slot}, ptr %other)\n  br label %done\nno:\n  br label %done\ndone:\n  %v = phi i8 [ %r, %cmp ], [ 0, %no ]\n");
                    }
                    else
                    {
                        sb.Append("  %v = add i8 0, 0\n");
                    }
                    sb.Append($"  call void {DropFn(m.Parameters[0].Type)}(ptr %other)\n  ret i8 %v\n");
                    _code.Append(sb).Append("}\n\n");
                    return true;
                }
                case SynthesizedRecordPrintMembers:
                    _code.Append(header).Append("  ret i8 0\n}\n\n");
                    return true;
                case SynthesizedRecordCopyCtor:
                    _code.Append(header).Append("  ret void\n}\n\n");
                    return true;
                default:
                    if (def.AssociatedSymbol is SynthesizedRecordEqualityContractProperty)
                    {
                        _code.Append(header).Append("  ret ptr null\n}\n\n");
                        return true;
                    }
                    return false;
            }
        }
    }
}
