// RustSharp: emits one closed method instance as an LLVM function. Every MIR local is an alloca; clang's
// mem2reg/SROA turn them back into SSA, which also folds away most zero-on-move stores and null checks.

using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Text;
using Microsoft.CodeAnalysis.CSharp.Symbols;

namespace Microsoft.CodeAnalysis.CSharp.Ownership
{
    internal sealed partial class LlvmBackend
    {
        private sealed class FnEmitter
        {
            private readonly LlvmBackend _g;
            private readonly MethodSymbol _m;
            private readonly MirBody _b;
            private readonly TypeMap _map;
            private readonly StringBuilder _sb = new StringBuilder();
            private readonly MirType[] _localTypes;
            private int _t;
            private BasicBlock _fault;

            public FnEmitter(LlvmBackend g, MethodSymbol closed, MirBody body)
            {
                _g = g;
                _m = closed;
                _b = body;
                _map = MapFor(closed);
                _localTypes = body.Locals.Select(l => Closed(l.Type)).ToArray();
            }

            private TypeSymbol Closed(TypeSymbol t) => _map.SubstituteType(t).Type;
            private MirType Closed(MirType t) => new MirType(Closed(t.Type), t.Ref, t.Contents);
            private string Tmp() => "%t" + _t++;
            private void L(string s) => _sb.Append("  ").Append(s).Append('\n');
            private void Label(string s) => _sb.Append(s).Append(":\n");
            private string NewLabel(string hint) => hint + "." + _t++;

            public void Emit()
            {
                string ret = _g.ReturnTy(_m);
                var tys = _g.ParamTys(_m);
                var ps = tys.Select((t, i) => $"{t} %a{i}");
                _sb.Append($"; {_m.ToDisplayString()}\ndefine internal {ret} {_g._fns[_m]}({string.Join(", ", ps)}) {{\nentry:\n");

                for (int i = 0; i < _localTypes.Length; i++)
                {
                    var t = _localTypes[i];
                    if (!t.IsRef && t.Type.SpecialType == SpecialType.System_Void) continue;
                    L($"%l{i} = alloca {_g.Ty(t)}");
                }

                // Argument slots first and only once: sanitizers may hoist these stores to the very top
                // of the function, so nothing else may write to an argument slot in the prologue.
                for (int i = 0; i < tys.Count; i++) L($"store {tys[i]} %a{i}, ptr %l{i + 1}");

                // Dropping storage that was never initialized must be a no-op.
                for (int i = tys.Count + 1; i < _localTypes.Length; i++)
                {
                    var t = _localTypes[i];
                    if (t.IsRef || t.Type.SpecialType == SpecialType.System_Void || !OwnershipFacts.NeedsDrop(t.Type)) continue;
                    L($"store {_g.Ty(t)} zeroinitializer, ptr %l{i}");
                }
                if (_localTypes.Length > 0 && !_localTypes[0].IsRef && _localTypes[0].Type.SpecialType != SpecialType.System_Void && OwnershipFacts.NeedsDrop(_localTypes[0].Type))
                    L($"store {_g.Ty(_localTypes[0])} zeroinitializer, ptr %l0");
                L("br label %bb0");

                foreach (var block in _b.Reachable())
                {
                    Label("bb" + block.Index);
                    _fault = block.Term switch
                    {
                        FaultEdgeTerm f => f.Unwind,
                        CallTerm c => c.Unwind,
                        _ => null
                    };
                    foreach (var s in block.Statements) Statement(s);
                    Term(block.Term);
                }

                _sb.Append("}\n\n");
                _g._code.Append(_sb);
            }

            private bool _coroutine;
            private readonly Dictionary<SuspendTerm, int> _suspendStates = new Dictionary<SuspendTerm, int>();
            private string _frameType;

            /// <summary>
            /// A coroutine: the method body turns into a resume function whose locals live in a heap
            /// frame, so references between them stay valid across suspensions without any pinning.
            /// Dropping an unfinished coroutine drops what the frame holds; moved-from slots are zero.
            /// </summary>
            public void EmitCoroutine()
            {
                _coroutine = true;
                string name = _g._fns[_m];
                string resume = _g.Unique("resume." + _m.ToDisplayString());
                string drop = _g.Unique("frame.drop." + _m.ToDisplayString());
                _frameType = "%" + Quote("frame." + _m.ToDisplayString() + "#" + _g._next++);

                var fields = new List<string> { "i32" };
                var slots = new int[_localTypes.Length];
                for (int i = 0; i < _localTypes.Length; i++)
                {
                    slots[i] = -1;
                    var t = _localTypes[i];
                    if (!t.IsRef && t.Type.SpecialType == SpecialType.System_Void) continue;
                    slots[i] = fields.Count;
                    fields.Add(_g.Ty(t));
                }
                _g._types.Append($"{_frameType} = type {{ {string.Join(", ", fields)} }}\n");

                _sb.Append($"; resume of {_m.ToDisplayString()}\ndefine internal i32 {resume}(ptr %frame, ptr %out) {{\nentry:\n");
                for (int i = 0; i < slots.Length; i++)
                    if (slots[i] >= 0) L($"%l{i} = getelementptr {_frameType}, ptr %frame, i32 0, i32 {slots[i]}");

                var reachable = _b.Reachable();
                int state = 1;
                var cases = new StringBuilder("  %state = load i32, ptr %frame\n  switch i32 %state, label %finished [ i32 0, label %bb0 ");
                foreach (var block in reachable)
                {
                    if (block.Term is not SuspendTerm s) continue;
                    _suspendStates[s] = state;
                    cases.Append($"i32 {state}, label %bb{s.Resume.Index} ");
                    state++;
                }
                if (!OwnershipFacts.IsFrameSend(_localTypes))
                {
                    // Holds something like an Rc: the task must stay on this thread from now on.
                    var runtime = _g._compilation.GetTypeByMetadataName("System.Threading.Tasks.Runtime");
                    L($"call void {_g.Fn(runtime.GetMembers("PinCurrent").OfType<MethodSymbol>().First())}()");
                }
                _sb.Append(cases).Append("]\nfinished:\n  ret i32 1\n");

                foreach (var block in reachable)
                {
                    Label("bb" + block.Index);
                    _fault = block.Term switch
                    {
                        FaultEdgeTerm f => f.Unwind,
                        CallTerm c => c.Unwind,
                        _ => null
                    };
                    foreach (var s in block.Statements) Statement(s);
                    Term(block.Term);
                }
                _sb.Append("}\n\n");

                _sb.Append($"define internal void {drop}(ptr %frame) {{\n");
                for (int i = _localTypes.Length - 1; i >= 0; i--)
                {
                    var t = _localTypes[i];
                    if (slots[i] < 0 || t.IsRef || !OwnershipFacts.NeedsDrop(t.Type)) continue;
                    L($"%l{i} = getelementptr {_frameType}, ptr %frame, i32 0, i32 {slots[i]}");
                    L($"call void {_g.DropFn(t.Type)}(ptr %l{i})");
                }
                L("call void @free(ptr %frame)");
                L("ret void");
                _sb.Append("}\n\n");

                // The method itself only creates the frame and the object that drives it.
                var tys = _g.ParamTys(_m);
                var ps = tys.Select((t, i) => $"{t} %a{i}");
                _sb.Append($"; {_m.ToDisplayString()}\ndefine internal {_g.Ty(new MirType(Closed(_m.ReturnType)))} {name}({string.Join(", ", ps)}) {{\n");
                var size = SizeOf(_frameType);
                L($"%frame = call ptr @__alloc(i64 {size})");
                for (int i = 0; i < tys.Count; i++)
                {
                    var a = Tmp();
                    L($"{a} = getelementptr {_frameType}, ptr %frame, i32 0, i32 {slots[i + 1]}");
                    L($"store {tys[i]} %a{i}, ptr {a}");
                }
                var factory = CoroutineFactory();
                var r = Tmp();
                string returned = _g.Ty(new MirType(Closed(factory.ReturnType)));
                L($"{r} = call {returned} {_g.Fn(factory)}(ptr %frame, ptr {resume}, ptr {drop})");
                L($"ret {returned} {r}");
                _sb.Append("}\n\n");
                _g._code.Append(_sb);
            }

            private MethodSymbol CoroutineFactory()
            {
                NamedTypeSymbol owner;
                if (_m.IsIterator)
                {
                    var generator = _g._compilation.GetTypeByMetadataName(_m.IsAsync ? "System.Threading.Tasks.AsyncGenerator`1" : "System.Collections.Generic.Generator`1");
                    owner = generator.Construct(Closed(_b.Locals[_b.YieldSlot].Type.Type));
                }
                else
                {
                    owner = (NamedTypeSymbol)_m.ReturnType;
                }
                return owner.GetMembers("FromCoroutine").OfType<MethodSymbol>().First();
            }

            private void ReturnFromCoroutine()
            {
                L("store i32 -1, ptr %frame");
                var result = _localTypes[0];
                if (result.Type.SpecialType != SpecialType.System_Void)
                {
                    string ty = _g.Ty(result);
                    var v = Tmp();
                    L($"{v} = load {ty}, ptr %l0");
                    L($"store {ty} {v}, ptr %out");
                    if (OwnershipFacts.NeedsDrop(result.Type)) L($"store {ty} zeroinitializer, ptr %l0");
                }
                L("ret i32 1");
            }

            // ---- places

            private (string Addr, MirType Type) Addr(Place p)
            {
                string addr;
                MirType t;
                if (p.Static is not null)
                {
                    var container = (NamedTypeSymbol)Closed(p.Static.ContainingType);
                    var field = container.GetMembers(p.Static.Name).OfType<FieldSymbol>().First();
                    if (_g.CctorGuard(container) is { } guard && !IsOwnCctor(container)) L($"call void {guard}()");
                    addr = _g.StaticGlobal(field);
                    t = new MirType(field.Type, field.RefKind == RefKind.None ? RefMode.None : RefMode.Mut);
                }
                else
                {
                    addr = "%l" + p.Local;
                    t = _localTypes[p.Local];
                }

                foreach (var proj in p.Projs)
                {
                    switch (proj)
                    {
                        case DerefProj:
                        {
                            var v = Tmp();
                            L($"{v} = load ptr, ptr {addr}");
                            if (t.IsRef)
                            {
                                t = t.Pointee;
                            }
                            else if (t.Type is PointerTypeSymbol ptr)
                            {
                                t = new MirType(ptr.PointedAtType);
                            }
                            else
                            {
                                NullCheck(v);
                                t = new MirType(t.Type, RefMode.None, contents: true);
                            }
                            addr = v;
                            break;
                        }
                        case FieldProj f:
                        {
                            if (IsPrimitive(t.Type)) break; // `this` of a primitive has no field structure
                            var layout = _g.LayoutOf(t.Type);
                            var key = f.Field.OriginalDefinition;
                            if (!layout.Index.TryGetValue(key, out int index))
                            {
                                // The place was typed by a base class: resolve against the declaring type.
                                var owner = (NamedTypeSymbol)Closed(f.Field.ContainingType);
                                layout = _g.LayoutOf(owner);
                                index = layout.Index[key];
                            }
                            var closedField = layout.Fields.First(x => s_cmp.Equals(x.OriginalDefinition, key));
                            var a = Tmp();
                            L($"{a} = getelementptr {layout.LlvmType}, ptr {addr}, i32 0, i32 {index}");
                            addr = a;
                            t = new MirType(closedField.Type, closedField.RefKind == RefKind.None ? RefMode.None
                                : closedField.RefKind == RefKind.RefReadOnly ? RefMode.Shared : RefMode.Mut);
                            break;
                        }
                        case IndexProj i:
                        {
                            var arrayType = (ArrayTypeSymbol)t.Type;
                            var element = arrayType.ElementType;
                            string linear = null;
                            for (int d = 0; d < i.Indices.Length; d++)
                            {
                                var (value, valueType) = Val(i.Indices[d]);
                                var index = ToI64(value, valueType, i.Indices[d]);
                                var lenp = Tmp();
                                L($"{lenp} = getelementptr i8, ptr {addr}, i64 {(arrayType.IsSZArray ? 8 : 16 + 8 * d)}");
                                var len = Tmp();
                                L($"{len} = load i64, ptr {lenp}");
                                var ok = Tmp();
                                L($"{ok} = icmp ult i64 {index}, {len}");
                                string good = NewLabel("inb"), bad = NewLabel("oob");
                                L($"br i1 {ok}, label %{good}, label %{bad}");
                                Label(bad);
                                Raise("Bounds", "bounds");
                                Label(good);
                                if (linear is null)
                                {
                                    linear = index;
                                }
                                else
                                {
                                    var scaled = Tmp();
                                    L($"{scaled} = mul i64 {linear}, {len}");
                                    var sum = Tmp();
                                    L($"{sum} = add i64 {scaled}, {index}");
                                    linear = sum;
                                }
                            }
                            var data = Tmp();
                            L($"{data} = getelementptr i8, ptr {addr}, i64 {ArrayDataOffset(arrayType.Rank)}");
                            var e = Tmp();
                            L($"{e} = getelementptr {_g.Ty(element)}, ptr {data}, i64 {linear}");
                            addr = e;
                            t = new MirType(element);
                            break;
                        }
                    }
                }
                return (addr, t);
            }

            /// <summary>
            /// Raises a runtime fault at the current position. Inside a block with an unwind edge it is an
            /// ordinary exception. Code without one (cleanup paths) cannot continue and aborts.
            /// </summary>
            private void Raise(string kind, string panic)
            {
                if (_fault is null)
                {
                    L($"call void @__panic_{panic}()");
                    L("unreachable");
                    return;
                }
                Located(_site);
                var e = Tmp();
                L($"{e} = call ptr {_g.FaultFn(kind)}()");
                L($"store ptr {e}, ptr %l{_b.ExceptionSlot}");
                L($"br label %bb{_fault.Index}");
            }

            private bool IsOwnCctor(NamedTypeSymbol container)
                => _m.MethodKind == MethodKind.StaticConstructor && s_cmp.Equals(_m.ContainingType, container);

            private void NullCheck(string v)
            {
                var isNull = Tmp();
                L($"{isNull} = icmp eq ptr {v}, null");
                string good = NewLabel("nn"), bad = NewLabel("nil");
                L($"br i1 {isNull}, label %{bad}, label %{good}");
                Label(bad);
                Raise("Null", "null");
                Label(good);
            }

            private string ToI64(string value, string type, Operand op)
            {
                if (type == "i64") return value;
                var r = Tmp();
                bool signed = OperandType(op) is { } t && IsSigned(t);
                L($"{r} = {(signed ? "sext" : "zext")} {type} {value} to i64");
                return r;
            }

            private TypeSymbol OperandType(Operand op) => op switch
            {
                ConstOp k => k.Type is null ? null : Closed(k.Type),
                CopyOp c => PlaceType(c.Place).Type,
                MoveOp m => PlaceType(m.Place).Type,
                _ => null
            };

            private MirType PlaceType(Place p)
            {
                var t = p.Static is null ? _localTypes[p.Local] : Closed(new MirType(p.Static.Type));
                foreach (var proj in p.Projs)
                {
                    if (proj is FieldProj f)
                    {
                        if (IsPrimitive(t.Type)) continue;
                        var owner = t.Type is NamedTypeSymbol n ? n : (NamedTypeSymbol)Closed(f.Field.ContainingType);
                        var layout = _g.LayoutOf(owner);
                        var key = f.Field.OriginalDefinition;
                        if (!layout.Index.ContainsKey(key)) layout = _g.LayoutOf((NamedTypeSymbol)Closed(f.Field.ContainingType));
                        var cf = layout.Fields.First(x => s_cmp.Equals(x.OriginalDefinition, key));
                        t = new MirType(cf.Type, cf.RefKind == RefKind.None ? RefMode.None : cf.RefKind == RefKind.RefReadOnly ? RefMode.Shared : RefMode.Mut);
                    }
                    else
                    {
                        t = MirBody.Project(t, proj);
                    }
                }
                return t;
            }

            // ---- values

            private (string Value, string Type) Val(Operand op)
            {
                switch (op)
                {
                    case ConstOp k:
                        return Const(k);
                    case CopyOp c:
                    {
                        var (addr, t) = Addr(c.Place);
                        string ty = _g.Ty(t);
                        var v = Tmp();
                        L($"{v} = load {ty}, ptr {addr}");
                        return (v, ty);
                    }
                    case MoveOp m:
                    {
                        var (addr, t) = Addr(m.Place);
                        string ty = _g.Ty(t);
                        var v = Tmp();
                        L($"{v} = load {ty}, ptr {addr}");
                        if (!t.IsRef && OwnershipFacts.NeedsDrop(t.Type)) L($"store {ty} zeroinitializer, ptr {addr}");
                        return (v, ty);
                    }
                    default:
                        throw ExceptionUtilities.UnexpectedValue(op);
                }
            }

            private (string, string) Const(ConstOp k)
            {
                var type = k.Type is null ? null : Closed(k.Type);
                if (k.Value is null || k.Value.IsNull)
                    return type is null || IsHandle(type) || type.TypeKind is TypeKind.Pointer ? ("null", "ptr") : ("zeroinitializer", _g.Ty(type));

                string ty = type is null ? null : _g.Ty(type);
                switch (k.Value.Discriminator)
                {
                    case ConstantValueTypeDiscriminator.String:
                    {
                        // Every use of a literal is a String of its own (it may be changed), sharing the static bytes.
                        var handle = Tmp();
                        L($"{handle} = call ptr @__str_retain(ptr {_g.StringLiteral(k.Value.StringValue)})");
                        return (handle, "ptr");
                    }
                    case ConstantValueTypeDiscriminator.Boolean:
                        return (k.Value.BooleanValue ? "1" : "0", "i8");
                    case ConstantValueTypeDiscriminator.Double:
                        return (FloatBits(k.Value.DoubleValue), ty ?? "double");
                    case ConstantValueTypeDiscriminator.Single:
                        return (FloatBits(k.Value.SingleValue), ty ?? "float");
                    case ConstantValueTypeDiscriminator.Char:
                        return (((int)k.Value.CharValue).ToString(), ty ?? "i16");
                    case ConstantValueTypeDiscriminator.Decimal:
                    case ConstantValueTypeDiscriminator.DateTime:
                        _g._errors.Add("unsupported constant type: " + k.Value.Discriminator);
                        return ("0", ty ?? "i32");
                    default:
                        return (Integer(k.Value), ty ?? "i64");
                }
            }

            private static string Integer(ConstantValue v) => v.Discriminator switch
            {
                ConstantValueTypeDiscriminator.UInt64 or ConstantValueTypeDiscriminator.NUInt => v.UInt64Value.ToString(CultureInfo.InvariantCulture),
                ConstantValueTypeDiscriminator.Int64 => v.Int64Value.ToString(CultureInfo.InvariantCulture),
                ConstantValueTypeDiscriminator.UInt32 => v.UInt32Value.ToString(CultureInfo.InvariantCulture),
                ConstantValueTypeDiscriminator.Int32 or ConstantValueTypeDiscriminator.NInt => v.Int32Value.ToString(CultureInfo.InvariantCulture),
                ConstantValueTypeDiscriminator.UInt16 => v.UInt16Value.ToString(CultureInfo.InvariantCulture),
                ConstantValueTypeDiscriminator.Int16 => v.Int16Value.ToString(CultureInfo.InvariantCulture),
                ConstantValueTypeDiscriminator.Byte => v.ByteValue.ToString(CultureInfo.InvariantCulture),
                ConstantValueTypeDiscriminator.SByte => v.SByteValue.ToString(CultureInfo.InvariantCulture),
                _ => throw ExceptionUtilities.UnexpectedValue(v.Discriminator)
            };

            private static string FloatBits(double d) => "0x" + BitConverter.DoubleToInt64Bits(d).ToString("X16");

            private static bool IsSigned(TypeSymbol t)
            {
                t = Unenum(t);
                return t.SpecialType is SpecialType.System_SByte or SpecialType.System_Int16 or SpecialType.System_Int32
                    or SpecialType.System_Int64 or SpecialType.System_IntPtr;
            }

            private static bool IsFloat(TypeSymbol t) => t.SpecialType is SpecialType.System_Single or SpecialType.System_Double;

            private static int Width(string ty) => ty switch { "i8" => 8, "i16" => 16, "i32" => 32, "i64" => 64, _ => 0 };

            private string ZextBool(string i1)
            {
                var r = Tmp();
                L($"{r} = zext i1 {i1} to i8");
                return r;
            }

            private string Truthy(string i8)
            {
                var r = Tmp();
                L($"{r} = icmp ne i8 {i8}, 0");
                return r;
            }

            // ---- statements

            private SyntaxNode _site;
            private bool? _user;

            private bool InUserCode => _user ??= _b.Syntax?.SyntaxTree is { } t && _g.IsUserTree?.Invoke(t) == true;

            /// <summary>Remembers where user code is, for the message of a panic that follows.</summary>
            private void Located(SyntaxNode syntax)
            {
                if (syntax is null || !InUserCode) return;
                L($"store ptr {_g.StringLiteral(_g.SiteText(syntax))}, ptr @__panic_loc");
            }

            private void Statement(Statement s)
            {
                _site = s.Syntax ?? _site;
                switch (s)
                {
                    case AssignStmt a:
                        Assign(a);
                        break;
                    case DropStmt d:
                    {
                        var type = PlaceType(d.Place);
                        if (type.IsRef || !OwnershipFacts.NeedsDrop(type.Type)) break;
                        var (addr, _) = Addr(d.Place);
                        L($"call void {_g.DropFn(type.Type)}(ptr {addr})");
                        break;
                    }
                }
            }

            private void Store(Place dest, string value, string type)
            {
                var (addr, _) = Addr(dest);
                L($"store {type} {value}, ptr {addr}");
            }

            private void Assign(AssignStmt a)
            {
                var (value, type) = Rvalue(a.Value, a.Dest);
                if (value != null) Store(a.Dest, value, type);
            }

            private (string, string) Rvalue(Rvalue rv, Place dest)
            {
                switch (rv)
                {
                    case UseRv u:
                    {
                        var (v, t) = Val(u.Op);
                        return (v, ConstStoreType(u.Op, t, dest));
                    }
                    case RefRv { CastTo: { } castTo } r:
                    {
                        // The place ends in the Deref of the handle; test before dereferencing, since
                        // a null handle simply fails the test.
                        var handle = new Place(r.Place.Local, r.Place.Projs.RemoveAt(r.Place.Projs.Length - 1));
                        var (slot, _) = r.Place.Static is null ? Addr(handle) : Addr(new Place(r.Place.Static, r.Place.Projs.RemoveAt(r.Place.Projs.Length - 1)));
                        var v = Tmp();
                        L($"{v} = load ptr, ptr {slot}");
                        var test = Tmp();
                        L($"{test} = call i8 {_g.IsInstFnName(Closed(castTo))}(ptr {v})");
                        var result = Tmp();
                        L($"{result} = select i1 {Truthy(test)}, ptr {v}, ptr null");
                        return (result, "ptr");
                    }
                    case RefRv r:
                        return (Addr(r.Place).Addr, "ptr");
                    case AddrOfRv r:
                        return (Addr(r.Place).Addr, "ptr");
                    case BinaryRv b:
                        return Binary(b);
                    case UnaryRv u:
                        return Unary(u);
                    case ConvertRv c:
                        return Convert(c);
                    case RefCastRv c:
                        return RefCast(c);
                    case IsInstRv i:
                        return IsInst(i);
                    case IsNullRv i:
                    {
                        var type = PlaceType(i.Place);
                        if (!IsHandle(type.Type) && !type.IsRef && !type.Contents && type.Type.TypeKind != TypeKind.Pointer) return ("0", "i8");
                        var (addr, _) = Addr(i.Place);
                        var v = Tmp();
                        L($"{v} = load ptr, ptr {addr}");
                        var c = Tmp();
                        L($"{c} = icmp eq ptr {v}, null");
                        return (ZextBool(c), "i8");
                    }
                    case StaticStringRv s:
                        return (_g.StringLiteral(s.Value), "ptr");
                    case TypeOfRv t:
                    {
                        var of = _g._compilation.GetTypeByMetadataName("System.Type").GetMembers("Of").OfType<MethodSymbol>().First();
                        var r = Tmp();
                        L($"{r} = call ptr {_g.Fn(of)}(ptr {_g.StringLiteral(_g.TypeName(Closed(t.Type)))})");
                        return (r, "ptr");
                    }
                    case NewObjRv n:
                    {
                        var type = Closed(n.Type);
                        var obj = _g.ObjOfClass(type);
                        var size = SizeOf(_g.LayoutOf(type).LlvmType);
                        var p = Tmp();
                        L($"{p} = call ptr @__alloc(i64 {size})");
                        L($"store i64 {obj.Id}, ptr {p}");
                        return (p, "ptr");
                    }
                    case DefaultRv d:
                    {
                        var type = Closed(d.Type);
                        string ty = _g.Ty(type);
                        if (d.Alive && type.IsValueType && !IsPrimitive(type) && type.TypeKind != TypeKind.Enum && _g.LayoutOf(type).AliveIndex is var idx and >= 0)
                        {
                            var v = Tmp();
                            L($"{v} = insertvalue {ty} zeroinitializer, i8 1, {idx}");
                            return (v, ty);
                        }
                        return ("zeroinitializer", ty);
                    }
                    case NewArrayRv n:
                        return NewArray(n);
                    case ArrayDimRv a:
                        return ArrayDim(a);
                    case StackAllocRv a:
                        return StackAlloc(a);
                    case ArrayLenRv a:
                    {
                        var (addr, _) = Addr(a.Array);
                        var p = Tmp();
                        L($"{p} = getelementptr i8, ptr {addr}, i64 8");
                        var v = Tmp();
                        L($"{v} = load i64, ptr {p}");
                        var r = Tmp();
                        L($"{r} = trunc i64 {v} to i32");
                        return (r, "i32");
                    }
                    case PeekBoxRv b:
                    {
                        var type = Closed(b.Type);
                        var (addr, _) = Addr(b.Place);
                        var v = Tmp();
                        L($"{v} = load ptr, ptr {addr}");
                        var payload = Tmp();
                        L($"{payload} = getelementptr i8, ptr {v}, i64 8");
                        string ty = _g.Ty(type);
                        var r = Tmp();
                        L($"{r} = load {ty}, ptr {payload}");
                        return (r, ty);
                    }
                    case LinkRv l:
                    {
                        var (slot, _) = Addr(l.Source);
                        var v = Tmp();
                        L($"{v} = load ptr, ptr {slot}");
                        return (v, "ptr");
                    }
                    case StructEqRv e:
                    {
                        var (left, _) = Addr(e.Left);
                        var (right, _) = Addr(e.Right);
                        var r = Tmp();
                        L($"{r} = call i8 {_g.EqFn(Closed(e.Type))}(ptr {left}, ptr {right})");
                        return (r, "i8");
                    }
                    case BoxRv b:
                        return Box(b);
                    case UnboxRv u:
                        return Unbox(u);
                    case RetainRv r:
                    {
                        var (addr, _) = Addr(r.Place);
                        var v = Tmp();
                        L($"{v} = load ptr, ptr {addr}");
                        var o = Tmp();
                        L($"{o} = call ptr @__str_retain(ptr {v})");
                        return (o, "ptr");
                    }
                    case SizeOfRv s:
                    {
                        var size = SizeOf(_g.Ty(Closed(s.Type)));
                        string want = _g.Ty(PlaceType(dest));
                        if (want == "i64") return (size, want);
                        var r = Tmp();
                        L($"{r} = trunc i64 {size} to {want}");
                        return (r, want);
                    }
                    case FnPtrRv f:
                        return (_g.Fn(Close(f.Method, _map)), "ptr");
                    case NewDelegateRv d:
                        return NewDelegate(d);
                    default:
                        throw ExceptionUtilities.UnexpectedValue(rv);
                }
            }

            /// <summary>Integer constants take their width from the destination.</summary>
            private string ConstStoreType(Operand op, string type, Place dest)
                => op is ConstOp && type != "ptr" ? _g.Ty(PlaceType(dest)) : type;

            private string SizeOf(string ty)
            {
                var g = Tmp();
                L($"{g} = getelementptr {ty}, ptr null, i32 1");
                var s = Tmp();
                L($"{s} = ptrtoint ptr {g} to i64");
                return s;
            }

            private (string, string) Unary(UnaryRv u)
            {
                var (v, t) = Val(u.Value);
                var type = Unenum(Closed(u.OperandType));
                var r = Tmp();
                switch (u.Op.Operator())
                {
                    case UnaryOperatorKind.LogicalNegation:
                        L($"{r} = xor i8 {v}, 1");
                        return (r, "i8");
                    case UnaryOperatorKind.BitwiseComplement:
                        L($"{r} = xor {t} {v}, -1");
                        return (r, t);
                    case UnaryOperatorKind.UnaryMinus:
                        if (!IsFloat(type) && (u.Op & UnaryOperatorKind.Checked) != 0)
                            return CheckedArithmetic(BinaryOperatorKind.Subtraction, true, t, "0", v);
                        L(IsFloat(type) ? $"{r} = fneg {t} {v}" : $"{r} = sub {t} 0, {v}");
                        return (r, t);
                    case UnaryOperatorKind.UnaryPlus:
                        return (v, t);
                    default:
                        _g._errors.Add("unsupported unary operator " + u.Op);
                        return (v, t);
                }
            }

            private (string, string) Binary(BinaryRv b)
            {
                var (l, lt) = Val(b.Left);
                var (r, rt) = Val(b.Right);
                var type = Unenum(Closed(b.OperandType));
                var op = b.Op.Operator();
                var result = Tmp();

                bool leftPtr = type.TypeKind == TypeKind.Pointer;
                bool rightPtr = Closed(b.RightType).TypeKind == TypeKind.Pointer;
                if (leftPtr || rightPtr)
                    return PointerOp(op, b, l, lt, r, rt, result);

                if (lt == "ptr" || rt == "ptr")
                {
                    var c = Tmp();
                    L($"{c} = icmp {(op == BinaryOperatorKind.Equal ? "eq" : "ne")} ptr {l}, {r}");
                    return (ZextBool(c), "i8");
                }

                if (lt != rt && b.Left is ConstOp) lt = rt;
                if (lt != rt && b.Right is ConstOp && op is not (BinaryOperatorKind.LeftShift or BinaryOperatorKind.RightShift or BinaryOperatorKind.UnsignedRightShift)) rt = lt;

                // Pointer arithmetic lowering multiplies a long by an int-typed sizeof.
                if (Width(lt) != 0 && Width(rt) != 0 && Width(lt) != Width(rt) && op is not (BinaryOperatorKind.LeftShift or BinaryOperatorKind.RightShift or BinaryOperatorKind.UnsignedRightShift))
                {
                    var wide = Tmp();
                    if (Width(lt) < Width(rt))
                    {
                        L($"{wide} = {(IsSigned(type) ? "sext" : "zext")} {lt} {l} to {rt}");
                        l = wide;
                        lt = rt;
                    }
                    else
                    {
                        L($"{wide} = {(IsSigned(Unenum(Closed(b.RightType))) ? "sext" : "zext")} {rt} {r} to {lt}");
                        r = wide;
                        rt = lt;
                    }
                }

                if (Width(lt) != 0 && Width(rt) != 0 && Width(rt) != Width(lt) && op is BinaryOperatorKind.LeftShift or BinaryOperatorKind.RightShift or BinaryOperatorKind.UnsignedRightShift)
                {
                    var c = Tmp();
                    L(Width(rt) < Width(lt) ? $"{c} = zext {rt} {r} to {lt}" : $"{c} = trunc {rt} {r} to {lt}");
                    r = c;
                }

                string ty = lt;
                if (IsFloat(type))
                {
                    string i = op switch
                    {
                        BinaryOperatorKind.Addition => "fadd",
                        BinaryOperatorKind.Subtraction => "fsub",
                        BinaryOperatorKind.Multiplication => "fmul",
                        BinaryOperatorKind.Division => "fdiv",
                        BinaryOperatorKind.Remainder => "frem",
                        _ => null
                    };
                    if (i != null)
                    {
                        L($"{result} = {i} {ty} {l}, {r}");
                        return (result, ty);
                    }
                    string cc = op switch
                    {
                        BinaryOperatorKind.Equal => "oeq",
                        BinaryOperatorKind.NotEqual => "une",
                        BinaryOperatorKind.LessThan => "olt",
                        BinaryOperatorKind.LessThanOrEqual => "ole",
                        BinaryOperatorKind.GreaterThan => "ogt",
                        _ => "oge"
                    };
                    L($"{result} = fcmp {cc} {ty} {l}, {r}");
                    return (ZextBool(result), "i8");
                }

                bool signed = IsSigned(type);
                if ((b.Op & BinaryOperatorKind.Checked) != 0 && op is BinaryOperatorKind.Addition or BinaryOperatorKind.Subtraction or BinaryOperatorKind.Multiplication)
                    return CheckedArithmetic(op, signed, ty, l, r);

                switch (op)
                {
                    case BinaryOperatorKind.Addition: L($"{result} = add {ty} {l}, {r}"); return (result, ty);
                    case BinaryOperatorKind.Subtraction: L($"{result} = sub {ty} {l}, {r}"); return (result, ty);
                    case BinaryOperatorKind.Multiplication: L($"{result} = mul {ty} {l}, {r}"); return (result, ty);
                    case BinaryOperatorKind.And: L($"{result} = and {ty} {l}, {r}"); return (result, ty);
                    case BinaryOperatorKind.Or: L($"{result} = or {ty} {l}, {r}"); return (result, ty);
                    case BinaryOperatorKind.Xor: L($"{result} = xor {ty} {l}, {r}"); return (result, ty);
                    case BinaryOperatorKind.Division:
                    case BinaryOperatorKind.Remainder:
                        return Divide(op, signed, ty, l, r);
                    case BinaryOperatorKind.LeftShift:
                    case BinaryOperatorKind.RightShift:
                    case BinaryOperatorKind.UnsignedRightShift:
                    {
                        var masked = Tmp();
                        L($"{masked} = and {ty} {r}, {Width(ty) - 1}");
                        string ins = op == BinaryOperatorKind.LeftShift ? "shl" : op == BinaryOperatorKind.RightShift && signed ? "ashr" : "lshr";
                        L($"{result} = {ins} {ty} {l}, {masked}");
                        return (result, ty);
                    }
                }

                string pred = op switch
                {
                    BinaryOperatorKind.Equal => "eq",
                    BinaryOperatorKind.NotEqual => "ne",
                    BinaryOperatorKind.LessThan => signed ? "slt" : "ult",
                    BinaryOperatorKind.LessThanOrEqual => signed ? "sle" : "ule",
                    BinaryOperatorKind.GreaterThan => signed ? "sgt" : "ugt",
                    BinaryOperatorKind.GreaterThanOrEqual => signed ? "sge" : "uge",
                    _ => null
                };
                if (pred is null)
                {
                    _g._errors.Add("unsupported binary operator " + b.Op);
                    return ("0", ty);
                }
                L($"{result} = icmp {pred} {ty} {l}, {r}");
                return (ZextBool(result), "i8");
            }

            private void OverflowPanicIf(string flag)
            {
                string good = NewLabel("noovf"), bad = NewLabel("ovf");
                L($"br i1 {flag}, label %{bad}, label %{good}");
                Label(bad);
                Raise("Overflow", "overflow");
                Label(good);
            }

            private (string, string) CheckedArithmetic(BinaryOperatorKind op, bool signed, string ty, string l, string r)
            {
                string name = (signed ? "s" : "u") + (op == BinaryOperatorKind.Addition ? "add" : op == BinaryOperatorKind.Subtraction ? "sub" : "mul");
                string intrinsic = $"llvm.{name}.with.overflow.{ty}";
                _g.Declare(intrinsic, $"declare {{ {ty}, i1 }} @{intrinsic}({ty}, {ty})");
                var pair = Tmp();
                L($"{pair} = call {{ {ty}, i1 }} @{intrinsic}({ty} {l}, {ty} {r})");
                var overflow = Tmp();
                L($"{overflow} = extractvalue {{ {ty}, i1 }} {pair}, 1");
                OverflowPanicIf(overflow);
                var result = Tmp();
                L($"{result} = extractvalue {{ {ty}, i1 }} {pair}, 0");
                return (result, ty);
            }

            private (string, string) Divide(BinaryOperatorKind op, bool signed, string ty, string l, string r)
            {
                var zero = Tmp();
                L($"{zero} = icmp eq {ty} {r}, 0");
                string good = NewLabel("div"), bad = NewLabel("div0");
                L($"br i1 {zero}, label %{bad}, label %{good}");
                Label(bad);
                Raise("DivideByZero", "div");
                Label(good);
                var result = Tmp();
                bool div = op == BinaryOperatorKind.Division;
                if (!signed)
                {
                    L($"{result} = {(div ? "udiv" : "urem")} {ty} {l}, {r}");
                    return (result, ty);
                }

                // INT_MIN / -1 is undefined in LLVM: route the -1 divisor around sdiv.
                var neg1 = Tmp();
                L($"{neg1} = icmp eq {ty} {r}, -1");
                var safe = Tmp();
                L($"{safe} = select i1 {neg1}, {ty} 1, {ty} {r}");
                var q = Tmp();
                L($"{q} = {(div ? "sdiv" : "srem")} {ty} {l}, {safe}");
                var alt = Tmp();
                L(div ? $"{alt} = sub {ty} 0, {l}" : $"{alt} = add {ty} 0, 0");
                L($"{result} = select i1 {neg1}, {ty} {alt}, {ty} {q}");
                return (result, ty);
            }

            private (string, string) PointerOp(BinaryOperatorKind op, BinaryRv b, string l, string lt, string r, string rt, string result)
            {
                string AsI64(string v, string t)
                {
                    if (t == "i64") return v;
                    var c = Tmp();
                    L(t == "ptr" ? $"{c} = ptrtoint ptr {v} to i64" : $"{c} = sext {t} {v} to i64");
                    return c;
                }

                switch (op)
                {
                    case BinaryOperatorKind.Addition:
                        if (lt == "ptr") L($"{result} = getelementptr i8, ptr {l}, i64 {AsI64(r, rt)}");
                        else L($"{result} = getelementptr i8, ptr {r}, i64 {AsI64(l, lt)}");
                        return (result, "ptr");
                    case BinaryOperatorKind.Subtraction:
                        if (rt == "ptr")
                        {
                            var a = AsI64(l, lt);
                            var c = AsI64(r, rt);
                            L($"{result} = sub i64 {a}, {c}");
                            return (result, "i64");
                        }
                        var neg = Tmp();
                        L($"{neg} = sub i64 0, {AsI64(r, rt)}");
                        L($"{result} = getelementptr i8, ptr {l}, i64 {neg}");
                        return (result, "ptr");
                    default:
                    {
                        string pred = op switch
                        {
                            BinaryOperatorKind.Equal => "eq",
                            BinaryOperatorKind.NotEqual => "ne",
                            BinaryOperatorKind.LessThan => "ult",
                            BinaryOperatorKind.LessThanOrEqual => "ule",
                            BinaryOperatorKind.GreaterThan => "ugt",
                            _ => "uge"
                        };
                        L($"{result} = icmp {pred} ptr {l}, {r}");
                        return (ZextBool(result), "i8");
                    }
                }
            }

            private (string, string) Convert(ConvertRv c)
            {
                var (v, ft) = Val(c.Value);
                var from = Unenum(Closed(c.From));
                var to = Unenum(Closed(c.To));
                string tt = _g.Ty(to);
                if (c.Value is ConstOp) ft = _g.Ty(from);
                if (ft == tt && !(c.Checked && Width(ft) != 0 && IsSigned(from) != IsSigned(to))) return (v, tt);
                var r = Tmp();

                if (ft == tt)
                {
                    // Same width, different sign: only the top bit can make the value unrepresentable.
                    var negative = Tmp();
                    L($"{negative} = icmp slt {ft} {v}, 0");
                    OverflowPanicIf(negative);
                    return (v, tt);
                }

                if (ft == "ptr")
                {
                    L($"{r} = ptrtoint ptr {v} to {tt}");
                    return (r, tt);
                }
                if (tt == "ptr")
                {
                    var wide = v;
                    if (ft != "i64")
                    {
                        wide = Tmp();
                        L($"{wide} = {(IsSigned(from) ? "sext" : "zext")} {ft} {v} to i64");
                    }
                    L($"{r} = inttoptr i64 {wide} to ptr");
                    return (r, tt);
                }
                if (IsFloat(from) && IsFloat(to))
                {
                    L($"{r} = {(tt == "double" ? "fpext" : "fptrunc")} {ft} {v} to {tt}");
                    return (r, tt);
                }
                if (IsFloat(from))
                {
                    string name = $"llvm.fpto{(IsSigned(to) ? "s" : "u")}i.sat.{tt}.{(ft == "double" ? "f64" : "f32")}";
                    _g.Declare(name, $"declare {tt} @{name}({ft})");
                    L($"{r} = call {tt} @{name}({ft} {v})");
                    return (r, tt);
                }
                if (IsFloat(to))
                {
                    L($"{r} = {(IsSigned(from) ? "sitofp" : "uitofp")} {ft} {v} to {tt}");
                    return (r, tt);
                }
                int fw = Width(ft), tw = Width(tt);
                L(tw < fw ? $"{r} = trunc {ft} {v} to {tt}" : $"{r} = {(IsSigned(from) ? "sext" : "zext")} {ft} {v} to {tt}");
                if (c.Checked)
                {
                    // The value survives exactly when both sides agree after widening past either type.
                    var original = Tmp();
                    L($"{original} = {(IsSigned(from) ? "sext" : "zext")} {ft} {v} to i128");
                    var converted = Tmp();
                    L($"{converted} = {(IsSigned(to) ? "sext" : "zext")} {tt} {r} to i128");
                    var differs = Tmp();
                    L($"{differs} = icmp ne i128 {original}, {converted}");
                    OverflowPanicIf(differs);
                }
                return (r, tt);
            }

            private (string, string) RefCast(RefCastRv c)
            {
                var (v, t) = Val(c.Value);
                var to = Closed(c.To);
                if (!c.Checked && !c.IsAs) return (v, t);
                if (t != "ptr") return (v, t);
                var test = Tmp();
                L($"{test} = call i8 {_g.IsInstFnName(to)}(ptr {v})");
                var ok = Truthy(test);
                var isNull = Tmp();
                L($"{isNull} = icmp eq ptr {v}, null");
                var pass = Tmp();
                L($"{pass} = or i1 {ok}, {isNull}");
                string good = NewLabel("cast"), bad = NewLabel("badcast");
                L($"br i1 {pass}, label %{good}, label %{bad}");
                Label(bad);
                if (c.IsAs)
                {
                    // `as` consumes its operand: on failure the value is dropped and the result is null.
                    L($"call void @__dropobj(ptr {v})");
                    L($"br label %{good}");
                    Label(good);
                    var r = Tmp();
                    L($"{r} = select i1 {pass}, ptr {v}, ptr null");
                    return (r, "ptr");
                }
                // The cast consumed its operand, and no one else owns it once the exception is raised.
                L($"call void @__dropobj(ptr {v})");
                Raise("Cast", "cast");
                Label(good);
                return (v, "ptr");
            }

            private (string, string) IsInst(IsInstRv i)
            {
                var target = Closed(i.Target);
                var type = PlaceType(i.Place);
                if (!IsHandle(type.Type) && !type.Contents)
                    return (s_cmp.Equals(type.Type, target) ? "1" : "0", "i8");
                var (addr, _) = Addr(i.Place);
                var v = Tmp();
                L($"{v} = load ptr, ptr {addr}");
                var r = Tmp();
                L($"{r} = call i8 {_g.IsInstFnName(target)}(ptr {v})");
                return (r, "i8");
            }

            private (string, string) NewArray(NewArrayRv n)
            {
                var arrayType = (ArrayTypeSymbol)Closed(n.ArrayType);
                var element = arrayType.ElementType;
                var obj = _g.Obj(ObjKind.Array, arrayType);
                var dims = new List<string>();
                string total = null;
                foreach (var length in n.Lengths)
                {
                    var (len, lt) = Val(length);
                    var wide = ToI64(len, lt, length);
                    var neg = Tmp();
                    L($"{neg} = icmp slt i64 {wide}, 0");
                    string good = NewLabel("len"), bad = NewLabel("neglen");
                    L($"br i1 {neg}, label %{bad}, label %{good}");
                    Label(bad);
                    Raise("Overflow", "size");
                    Label(good);
                    dims.Add(wide);
                    if (total is null)
                    {
                        total = wide;
                    }
                    else
                    {
                        var product = Tmp();
                        L($"{product} = mul i64 {total}, {wide}");
                        total = product;
                    }
                }

                int offset = ArrayDataOffset(arrayType.Rank);
                var size = SizeOf(_g.Ty(element));
                var bytes = Tmp();
                L($"{bytes} = mul i64 {size}, {total}");
                var all = Tmp();
                L($"{all} = add i64 {bytes}, {offset}");
                var p = Tmp();
                L($"{p} = call ptr @__alloc(i64 {all})");
                L($"store i64 {obj.Id}, ptr {p}");
                var lenp = Tmp();
                L($"{lenp} = getelementptr i8, ptr {p}, i64 8");
                L($"store i64 {total}, ptr {lenp}");
                if (!arrayType.IsSZArray)
                {
                    for (int d = 0; d < dims.Count; d++)
                    {
                        var dimp = Tmp();
                        L($"{dimp} = getelementptr i8, ptr {p}, i64 {16 + 8 * d}");
                        L($"store i64 {dims[d]}, ptr {dimp}");
                    }
                }
                return (p, "ptr");
            }

            private (string, string) ArrayDim(ArrayDimRv a)
            {
                var (addr, t) = Addr(a.Array);
                int rank = ((ArrayTypeSymbol)t.Type).Rank;
                var (dim, dt) = Val(a.Dimension);
                var index = ToI64(dim, dt, a.Dimension);
                var ok = Tmp();
                L($"{ok} = icmp ult i64 {index}, {rank}");
                string good = NewLabel("dim"), bad = NewLabel("baddim");
                L($"br i1 {ok}, label %{good}, label %{bad}");
                Label(bad);
                Raise("Bounds", "bounds");
                Label(good);
                var first = Tmp();
                L($"{first} = getelementptr i8, ptr {addr}, i64 16");
                var slot = Tmp();
                L($"{slot} = getelementptr i64, ptr {first}, i64 {index}");
                var v = Tmp();
                L($"{v} = load i64, ptr {slot}");
                var r = Tmp();
                L($"{r} = trunc i64 {v} to i32");
                return (r, "i32");
            }

            private (string, string) StackAlloc(StackAllocRv a)
            {
                var (bytes, bt) = Val(a.Bytes);
                string n = bytes;
                if (bt != "i64")
                {
                    n = Tmp();
                    L($"{n} = zext {bt} {bytes} to i64");
                }
                var p = Tmp();
                L($"{p} = alloca i8, i64 {n}, align 16");
                _g.Declare("llvm.memset.p0.i64", "declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)");
                L($"call void @llvm.memset.p0.i64(ptr {p}, i8 0, i64 {n}, i1 false)");
                if (a.Init != null)
                {
                    string ty = _g.Ty(Closed(a.Element));
                    for (int i = 0; i < a.Init.Count; i++)
                    {
                        var (v, _) = Val(a.Init[i]);
                        var e = Tmp();
                        L($"{e} = getelementptr {ty}, ptr {p}, i64 {i}");
                        L($"store {ty} {v}, ptr {e}");
                    }
                }
                return (p, "ptr");
            }

            private (string, string) Box(BoxRv b)
            {
                var type = Closed(b.Type);
                var (v, t) = Val(b.Value);
                if (IsHandle(type)) return (v, "ptr");
                var obj = _g.Obj(ObjKind.Box, type);
                string ty = _g.Ty(type);
                var size = SizeOf(ty);
                var total = Tmp();
                L($"{total} = add i64 {size}, 8");
                var p = Tmp();
                L($"{p} = call ptr @__alloc(i64 {total})");
                L($"store i64 {obj.Id}, ptr {p}");
                var payload = Tmp();
                L($"{payload} = getelementptr i8, ptr {p}, i64 8");
                L($"store {ty} {v}, ptr {payload}");
                return (p, "ptr");
            }

            private (string, string) Unbox(UnboxRv u)
            {
                var type = Closed(u.Type);
                var (v, _) = Val(u.Value);
                if (IsHandle(type)) return (v, "ptr");
                var obj = _g.Obj(ObjKind.Box, type);
                NullCheck(v);
                var id = Tmp();
                L($"{id} = load i64, ptr {v}");
                var ok = Tmp();
                L($"{ok} = icmp eq i64 {id}, {obj.Id}");
                string good = NewLabel("unbox"), bad = NewLabel("badunbox");
                L($"br i1 {ok}, label %{good}, label %{bad}");
                Label(bad);
                L($"call void @__dropobj(ptr {v})");
                Raise("Cast", "cast");
                Label(good);
                string ty = _g.Ty(type);
                var payload = Tmp();
                L($"{payload} = getelementptr i8, ptr {v}, i64 8");
                var r = Tmp();
                L($"{r} = load {ty}, ptr {payload}");
                L($"call void @free(ptr {v})");
                return (r, ty);
            }

            private (string, string) NewDelegate(NewDelegateRv d)
            {
                var type = (NamedTypeSymbol)Closed(d.Type);
                if (OwnershipFacts.HasAttribute(type, "ScopedSendAttribute"))
                {
                    // Runs on another thread while the borrowed data stays put: `&T` needs T: Sync, `&mut T` needs T: Send.
                    foreach (var (t, mode) in d.BorrowedTypes ?? new List<(TypeSymbol, RefMode)>())
                    {
                        var closed = Closed(t);
                        bool ok = mode == RefMode.Mut ? OwnershipFacts.IsSend(closed) : OwnershipFacts.IsSync(closed);
                        if (!ok)
                            _g.Report(mode == RefMode.Mut ? ErrorCode.ERR_OwnNotSend : ErrorCode.ERR_OwnNotSync,
                                $"`{closed.ToDisplayString()}` cannot be {(mode == RefMode.Mut ? "sent" : "shared")} between threads safely", d.Syntax, "borrowed by a closure that runs on another thread");
                    }
                }
                if (OwnershipFacts.HasAttribute(type, "SendAttribute"))
                {
                    if (d.Borrowed != null && d.Target is null)
                        _g.Report(ErrorCode.ERR_OwnNotSend, "a closure that borrows cannot be sent to another thread", d.Syntax, "use a `move` lambda");
                    foreach (var t in d.CapturedTypes ?? new List<TypeSymbol>())
                    {
                        var closed = Closed(t);
                        if (!OwnershipFacts.IsSend(closed))
                            _g.Report(ErrorCode.ERR_OwnNotSend, $"`{closed.ToDisplayString()}` cannot be sent between threads safely", d.Syntax, "captured by a closure that runs on another thread");
                    }
                }

                var obj = _g.ObjOfClass(type);
                var layout = _g.LayoutOf(type);
                string owner = "null", self = "null";
                if (d.Borrowed != null)
                {
                    var (slot, _) = Addr(d.Borrowed);
                    self = Tmp();
                    L($"{self} = load ptr, ptr {slot}");
                    if (d.Target != null) (owner, _) = Val(d.Target);
                }
                else
                {
                    (owner, _) = Val(d.Target);
                    self = owner;
                }

                var method = Close(d.Method, _map);
                string fn;
                if (d.Target is ConstOp && !method.IsStatic) fn = _g.ReceiverlessThunk(method);
                else fn = (method.IsVirtual || method.IsOverride || method.IsAbstract) && !method.IsStatic ? _g.DispatchStub(method) : _g.Fn(method);
                var size = SizeOf(layout.LlvmType);
                var p = Tmp();
                L($"{p} = call ptr @__alloc(i64 {size})");
                L($"store i64 {obj.Id}, ptr {p}");
                var op = Tmp();
                L($"{op} = getelementptr i8, ptr {p}, i64 8");
                L($"store ptr {owner}, ptr {op}");
                var sp = Tmp();
                L($"{sp} = getelementptr i8, ptr {p}, i64 16");
                L($"store ptr {self}, ptr {sp}");
                var fp = Tmp();
                L($"{fp} = getelementptr i8, ptr {p}, i64 24");
                L($"store ptr {fn}, ptr {fp}");
                return (p, "ptr");
            }

            // ---- terminators

            private void Term(Terminator t)
            {
                switch (t)
                {
                    case GotoTerm g:
                        L($"br label %bb{g.Target.Index}");
                        break;
                    case FaultEdgeTerm f:
                        L($"br label %bb{f.Target.Index}");
                        break;
                    case BranchTerm b:
                    {
                        var (v, _) = Val(b.Cond);
                        L($"br i1 {Truthy(v)}, label %bb{b.IfTrue.Index}, label %bb{b.IfFalse.Index}");
                        break;
                    }
                    case SwitchTerm s:
                    {
                        var (v, _) = Val(s.Value);
                        string ty = _g.Ty(Closed(s.Type));
                        var sb = new StringBuilder($"switch {ty} {v}, label %bb{s.Default.Index} [ ");
                        foreach (var (value, target) in s.Cases)
                        {
                            string text = value.Discriminator == ConstantValueTypeDiscriminator.Char ? ((int)value.CharValue).ToString() : Integer(value);
                            sb.Append($"{ty} {text}, label %bb{target.Index} ");
                        }
                        L(sb.Append(']').ToString());
                        break;
                    }
                    case SuspendTerm x:
                    {
                        if (x.IsYield)
                        {
                            var slot = _localTypes[_b.YieldSlot];
                            string ty = _g.Ty(slot);
                            var v = Tmp();
                            L($"{v} = load {ty}, ptr %l{_b.YieldSlot}");
                            L($"store {ty} {v}, ptr %out");
                            if (OwnershipFacts.NeedsDrop(slot.Type)) L($"store {ty} zeroinitializer, ptr %l{_b.YieldSlot}");
                        }
                        L($"store i32 {_suspendStates[x]}, ptr %frame");
                        L($"ret i32 {(x.IsYield && _m.IsAsync ? 2 : 0)}");
                        break;
                    }
                    case ReturnTerm when _coroutine:
                        ReturnFromCoroutine();
                        break;
                    case ResumeTerm when _coroutine:
                    {
                        var v = Tmp();
                        L($"{v} = load ptr, ptr %l{_b.ExceptionSlot}");
                        L($"store ptr {v}, ptr @__pending");
                        L($"store ptr null, ptr %l{_b.ExceptionSlot}");
                        L("store i32 -1, ptr %frame");
                        L("ret i32 1");
                        break;
                    }
                    case ReturnTerm:
                    {
                        string ret = _g.ReturnTy(_m);
                        if (ret == "void")
                        {
                            L("ret void");
                        }
                        else
                        {
                            var v = Tmp();
                            L($"{v} = load {ret}, ptr %l0");
                            L($"ret {ret} {v}");
                        }
                        break;
                    }
                    case ResumeTerm:
                    {
                        var v = Tmp();
                        L($"{v} = load ptr, ptr %l{_b.ExceptionSlot}");
                        L($"store ptr {v}, ptr @__pending");
                        string ret = _g.ReturnTy(_m);
                        L(ret == "void" ? "ret void" : ret == "ptr" ? "ret ptr null" : $"ret {ret} zeroinitializer");
                        break;
                    }
                    case UnreachableTerm:
                        L("unreachable");
                        break;
                    case ThrowTerm x:
                    {
                        var (v, _) = Val(x.Value);
                        var onThrow = _g._compilation.GetTypeByMetadataName("System.Startup").GetMembers("OnThrow").OfType<MethodSymbol>().First();
                        L($"call void {_g.Fn(onThrow)}(ptr {v})");
                        L($"store ptr {v}, ptr %l{_b.ExceptionSlot}");
                        L($"br label %bb{x.Unwind.Index}");
                        break;
                    }
                    case CallTerm c:
                        Call(c);
                        break;
                    default:
                        throw ExceptionUtilities.UnexpectedValue(t);
                }
            }

            private void AfterCall(CallTerm c)
            {
                if (c.Unwind is null)
                {
                    L($"br label %bb{c.Target.Index}");
                    return;
                }
                var p = Tmp();
                L($"{p} = load ptr, ptr @__pending");
                var has = Tmp();
                L($"{has} = icmp ne ptr {p}, null");
                string land = NewLabel("land");
                L($"br i1 {has}, label %{land}, label %bb{c.Target.Index}, !prof !0");
                Label(land);
                L($"store ptr {p}, ptr %l{_b.ExceptionSlot}");
                L("store ptr null, ptr @__pending");
                L($"br label %bb{c.Unwind.Index}");
            }

            private void Finish(CallTerm c, string ret, string call)
            {
                if (ret == "void" || c.Dest is null)
                {
                    L(call);
                }
                else
                {
                    var v = Tmp();
                    L($"{v} = {call}");
                    Store(c.Dest, v, ret);
                }
                AfterCall(c);
            }

            private void Call(CallTerm c)
            {
                _g._currentSite = c.Syntax;
                _site = c.Syntax ?? _site;
                Located(c.Syntax);
                if (c.FnPtr != null)
                {
                    var (fp, _) = Val(c.FnPtr);
                    var sig = c.FnSignature;
                    string fret = sig.ReturnsVoid ? "void" : _g.Ty(Closed(sig.ReturnType));
                    var fargs = c.Args.Select(Val).Select(a => $"{a.Type} {a.Value}");
                    Finish(c, fret, $"call {fret} {fp}({string.Join(", ", fargs)})");
                    return;
                }

                var m = Close(c.Method, _map);
                if (m.MethodKind == MethodKind.DelegateInvoke)
                {
                    DelegateInvoke(c, m);
                    return;
                }
                if (m.IsExtern && m.Name == "StaticStr" && c.Args.Count == 1 && c.Args[0] is ConstOp { Value.IsString: true } text)
                {
                    var template = _g.StringLiteral(text.Value.StringValue);
                    var dp = Tmp();
                    L($"{dp} = getelementptr i8, ptr {template}, i64 16");
                    var data = Tmp();
                    L($"{data} = load ptr, ptr {dp}");
                    string ty = _g.Ty(new MirType(Closed(m.ReturnType)));
                    var v0 = Tmp();
                    L($"{v0} = insertvalue {ty} undef, ptr {data}, 0");
                    var v1 = Tmp();
                    L($"{v1} = insertvalue {ty} {v0}, i32 {System.Text.Encoding.UTF8.GetByteCount(text.Value.StringValue)}, 1");
                    if (c.Dest is not null) Store(c.Dest, v1, ty);
                    L($"br label %bb{c.Target.Index}");
                    return;
                }
                if (m.IsExtern && IsIntrinsic(m))
                {
                    Intrinsic(c, m);
                    return;
                }
                if (m.IsExtern && m.ContainingType.Name == "Activator")
                {
                    CreateInstance(c, m.TypeArgumentsWithAnnotations[0].Type);
                    return;
                }

                var values = c.Args.Select(Val).ToList();
                string ret = _g.ReturnTy(m);
                string callee;

                if (m.IsExtern)
                {
                    callee = ExternCallee(m);
                }
                else if (c.ConstrainedTo is not null && m.IsStatic)
                {
                    var concrete = Closed(c.ConstrainedTo);
                    var impl = _g.FindImplementation(concrete, m);
                    if (impl is null)
                    {
                        _g._errors.Add($"`{concrete.ToDisplayString()}` has no implementation of {m.ToDisplayString()}");
                        impl = m;
                    }
                    callee = _g.Fn(impl);
                }
                else if (c.ReceiverIsSlot)
                {
                    var slotType = OperandMir(c.Args[0]).Type;
                    if (IsHandle(slotType))
                    {
                        var h = Tmp();
                        L($"{h} = load ptr, ptr {values[0].Value}");
                        values[0] = (h, "ptr");
                        callee = (m.IsVirtual || m.IsAbstract || m.IsOverride) ? _g.DispatchStub(m) : _g.Fn(m);
                    }
                    else
                    {
                        var impl = FindImpl(slotType, m);
                        if (impl is null || !impl.ContainingType.IsValueType)
                        {
                            _g._errors.Add($"`{slotType.ToDisplayString()}` has no implementation of {m.ToDisplayString()}");
                            impl = m;
                        }
                        callee = _g.Fn(impl);
                    }
                }
                else if (c.Virtual && (m.IsVirtual || m.IsAbstract || m.IsOverride))
                {
                    callee = _g.DispatchStub(m);
                }
                else if (!m.IsStatic && c.Args.Count > 0 && (m.IsVirtual || m.IsAbstract || m.IsOverride || m.ContainingType.IsInterface)
                    && Closed(OperandMir(c.Args[0]).Type) is { IsValueType: true } receiverType
                    && !s_cmp.Equals(receiverType, m.ContainingType) && FindImpl(receiverType, m) is { ContainingType.IsValueType: true } impl)
                {
                    // A struct receiver of an object or interface method, as in `point + "!"`: a struct has no
                    // object header to dispatch on, but its type is exact, so its own override is the target.
                    callee = _g.Fn(impl);
                }
                else
                {
                    callee = _g.Fn(m);
                }

                var tys = _g.ParamTys(m);
                var args = values.Select((a, i) => $"{(i < tys.Count ? tys[i] : a.Type)} {a.Value}");
                Finish(c, ret, $"call {ret} {callee}({string.Join(", ", args)})");
            }

            private MirType OperandMir(Operand op) => op switch
            {
                CopyOp c => PlaceType(c.Place),
                MoveOp m => PlaceType(m.Place),
                _ => throw ExceptionUtilities.UnexpectedValue(op)
            };

            private string ExternCallee(MethodSymbol m)
            {
                var data = m.GetDllImportData();
                string name = data?.EntryPointName ?? m.Name;
                string ret = _g.ReturnTy(m);
                _g.Declare(name, $"declare {ret} @{name}({string.Join(", ", _g.ParamTys(m))})");
                return "@" + name;
            }

            private void DelegateInvoke(CallTerm c, MethodSymbol m)
            {
                var values = c.Args.Select(Val).ToList();
                string self = values[0].Value;
                var tp = Tmp();
                L($"{tp} = getelementptr i8, ptr {self}, i64 16");
                var target = Tmp();
                L($"{target} = load ptr, ptr {tp}");
                var fp = Tmp();
                L($"{fp} = getelementptr i8, ptr {self}, i64 24");
                var fn = Tmp();
                L($"{fn} = load ptr, ptr {fp}");

                string ret = _g.ReturnTy(m);
                var tys = _g.ParamTys(m).Skip(1).ToList();
                var rest = values.Skip(1).Select((a, i) => $"{tys[i]} {a.Value}").ToList();
                var isStatic = Tmp();
                L($"{isStatic} = icmp eq ptr {target}, null");
                string st = NewLabel("dstatic"), inst = NewLabel("dinst"), done = NewLabel("ddone");
                L($"br i1 {isStatic}, label %{st}, label %{inst}");

                string withThis = string.Join(", ", new[] { "ptr " + target }.Concat(rest));
                string noThis = string.Join(", ", rest);
                string r1 = null, r2 = null;
                Label(st);
                if (ret == "void") L($"call void {fn}({noThis})");
                else { r1 = Tmp(); L($"{r1} = call {ret} {fn}({noThis})"); }
                L($"br label %{done}");
                Label(inst);
                if (ret == "void") L($"call void {fn}({withThis})");
                else { r2 = Tmp(); L($"{r2} = call {ret} {fn}({withThis})"); }
                L($"br label %{done}");
                Label(done);
                if (ret != "void" && c.Dest != null)
                {
                    var v = Tmp();
                    L($"{v} = phi {ret} [ {r1}, %{st} ], [ {r2}, %{inst} ]");
                    Store(c.Dest, v, ret);
                }

                // A [Once] delegate that started a coroutine: the coroutine keeps using the closure's
                // environment, so ownership moves into the task, as captures move into a Rust future.
                if (OwnershipFacts.IsOnceDelegate(m.ContainingType) && OwnershipFacts.IsCoroutineType(m.ReturnType) && c.Dest != null)
                {
                    var (slot, _) = Addr(c.Dest);
                    var task = Tmp();
                    L($"{task} = load ptr, ptr {slot}");
                    var taskType = _g._compilation.GetTypeByMetadataName("System.Threading.Tasks.Task");
                    var adopt = taskType.GetMembers("AdoptOwner").OfType<MethodSymbol>().First();
                    L($"call void {_g.Fn(adopt)}(ptr {task}, ptr {self})");
                }
                else if (OwnershipFacts.IsOnceDelegate(m.ContainingType))
                {
                    // Consumed by this call. Its drop must not see a pending exception.
                    var pending = Tmp();
                    L($"{pending} = load ptr, ptr @__pending");
                    L("store ptr null, ptr @__pending");
                    L($"call void @__dropobj(ptr {self})");
                    L($"store ptr {pending}, ptr @__pending");
                }
                AfterCall(c);
            }

            /// <summary><c>new T()</c>: closed at this point, so the constructor is known statically.</summary>
            private void CreateInstance(CallTerm c, TypeSymbol type)
            {
                var ctor = type is NamedTypeSymbol n ? n.InstanceConstructors.FirstOrDefault(x => x.ParameterCount == 0) : null;
                if (type.IsValueType)
                {
                    bool alive = _g.LayoutOf(type).AliveIndex >= 0;
                    var (value, ty) = Rvalue(new DefaultRv { Type = type, Alive = alive }, c.Dest);
                    Store(c.Dest, value, ty);
                    if (ctor is null || ctor.IsDefaultValueTypeConstructor())
                    {
                        L($"br label %bb{c.Target.Index}");
                        return;
                    }
                    var (slot, _) = Addr(c.Dest);
                    L($"call void {_g.Fn(ctor)}(ptr {slot})");
                    AfterCall(c);
                    return;
                }

                if (ctor is null)
                {
                    _g._errors.Add($"`{type.ToDisplayString()}` has no parameterless constructor");
                    ctor = ((NamedTypeSymbol)type).InstanceConstructors.First();
                }
                var obj = _g.ObjOfClass(type);
                var size = SizeOf(_g.LayoutOf(type).LlvmType);
                var p = Tmp();
                L($"{p} = call ptr @__alloc(i64 {size})");
                L($"store i64 {obj.Id}, ptr {p}");
                Store(c.Dest, p, "ptr");
                L($"call void {_g.Fn(ctor)}(ptr {p})");
                AfterCall(c);
            }

            private static bool IsIntrinsic(MethodSymbol m) => m.ContainingType.Name is "Mem" or "Atomic" && m.GetDllImportData() is null;

            private void AtomicOperation(CallTerm c, MethodSymbol m, List<(string Value, string Type)> values)
            {
                string ty = _g.Ty(m.TypeArgumentsWithAnnotations[0].Type);
                string p = values[0].Value;
                string align = ty == "i64" ? "8" : "4";
                var r = Tmp();
                switch (m.Name)
                {
                    case "Load":
                        L($"{r} = load atomic {ty}, ptr {p} seq_cst, align {align}");
                        Store(c.Dest, r, ty);
                        break;
                    case "Store":
                        L($"store atomic {ty} {values[1].Value}, ptr {p} seq_cst, align {align}");
                        break;
                    case "Add":
                        L($"{r} = atomicrmw add ptr {p}, {ty} {values[1].Value} seq_cst");
                        Store(c.Dest, r, ty);
                        break;
                    case "Exchange":
                        L($"{r} = atomicrmw xchg ptr {p}, {ty} {values[1].Value} seq_cst");
                        Store(c.Dest, r, ty);
                        break;
                    case "CompareExchange":
                    {
                        L($"{r} = cmpxchg ptr {p}, {ty} {values[1].Value}, {ty} {values[2].Value} seq_cst seq_cst");
                        var v = Tmp();
                        L($"{v} = extractvalue {{ {ty}, i1 }} {r}, 0");
                        Store(c.Dest, v, ty);
                        break;
                    }
                    default:
                        _g._errors.Add("unknown intrinsic Atomic." + m.Name);
                        break;
                }
                L($"br label %bb{c.Target.Index}");
            }

            private void Intrinsic(CallTerm c, MethodSymbol m)
            {
                TypeSymbol T(int i = 0) => m.TypeArgumentsWithAnnotations[i].Type;
                var values = c.Args.Select(Val).ToList();
                if (m.ContainingType.Name == "Atomic")
                {
                    AtomicOperation(c, m, values);
                    return;
                }
                switch (m.Name)
                {
                    case "Read":
                    {
                        string ty = _g.Ty(T());
                        var v = Tmp();
                        L($"{v} = load {ty}, ptr {values[0].Value}");
                        Store(c.Dest, v, ty);
                        break;
                    }
                    case "Write":
                        L($"store {_g.Ty(T())} {values[1].Value}, ptr {values[0].Value}");
                        break;
                    case "DropInPlace":
                        if (OwnershipFacts.NeedsDrop(T())) L($"call void {_g.DropFn(T())}(ptr {values[0].Value})");
                        break;
                    case "Forget":
                        break;
                    case "NeedsDrop":
                        Store(c.Dest, OwnershipFacts.NeedsDrop(T()) ? "1" : "0", "i8");
                        break;
                    case "Unwind":
                    {
                        // Panic.Raise: remember where, then leave through the unwind edge like any panic.
                        var onThrow = _g._compilation.GetTypeByMetadataName("System.Startup").GetMembers("OnThrow").OfType<MethodSymbol>().First();
                        L($"call void {_g.Fn(onThrow)}(ptr {values[0].Value})");
                        L($"store ptr {values[0].Value}, ptr @__pending");
                        AfterCall(c);
                        return;
                    }
                    case "PanicLocation":
                    {
                        var r = Tmp();
                        L($"{r} = load ptr, ptr @__panic_loc");
                        Store(c.Dest, r, "ptr");
                        break;
                    }
                    case "SizeOf":
                    {
                        var s = SizeOf(_g.Ty(T()));
                        var r = Tmp();
                        L($"{r} = trunc i64 {s} to i32");
                        Store(c.Dest, r, "i32");
                        break;
                    }
                    case "Transmute":
                    {
                        string from = _g.Ty(T(0)), to = _g.Ty(T(1));
                        if (from == to)
                        {
                            Store(c.Dest, values[0].Value, to);
                        }
                        else
                        {
                            var slot = Tmp();
                            L($"{slot} = alloca {to}");
                            L($"store {from} {values[0].Value}, ptr {slot}");
                            var r = Tmp();
                            L($"{r} = load {to}, ptr {slot}");
                            Store(c.Dest, r, to);
                        }
                        break;
                    }
                    case "TypeNameOf":
                    {
                        _g._needTypeName = true;
                        var v = Tmp();
                        L($"{v} = load ptr, ptr {values[0].Value}");
                        var r = Tmp();
                        L($"{r} = call ptr @__typename(ptr {v})");
                        Store(c.Dest, r, "ptr");
                        break;
                    }
                    case "HashOf":
                    {
                        var r = Tmp();
                        L($"{r} = call i32 {_g.HashFn(T())}(ptr {values[0].Value})");
                        Store(c.Dest, r, "i32");
                        break;
                    }
                    case "EqualOf":
                    {
                        var r = Tmp();
                        L($"{r} = call i8 {_g.EqFn(T())}(ptr {values[0].Value}, ptr {values[1].Value})");
                        Store(c.Dest, r, "i8");
                        break;
                    }
                    case "CompareOf":
                    {
                        var r = Tmp();
                        L($"{r} = call i32 {_g.CompareFn(T())}(ptr {values[0].Value}, ptr {values[1].Value})");
                        Store(c.Dest, r, "i32");
                        break;
                    }
                    case "RequireCopy":
                        if (!OwnershipFacts.IsCopy(T()))
                            _g.Report(ErrorCode.ERR_OwnNotClone, $"`{T().ToDisplayString()}` is not Copy", c.Syntax, "Copied needs a Copy type; use Cloned");
                        break;
                    case "RequireSend":
                        if (!OwnershipFacts.IsSend(T()))
                            _g.Report(ErrorCode.ERR_OwnNotSend, $"`{T().ToDisplayString()}` cannot be sent between threads safely", c.Syntax, "this value crosses a thread boundary");
                        break;
                    case "CloneOf":
                    {
                        if (!OwnershipFacts.IsClone(T()))
                        {
                            _g.Report(ErrorCode.ERR_OwnNotClone, $"`{T().ToDisplayString()}` does not implement Clone", c.Syntax, "add [Clone], or implement IClone<T>");
                            break;
                        }
                        string ty = _g.Ty(T());
                        var r = Tmp();
                        L($"{r} = call {ty} {_g.CloneFn(T())}(ptr {values[0].Value})");
                        Store(c.Dest, r, ty);
                        break;
                    }
                    case "AllocateUninit":
                        break;
                    case "AddressOf":
                    case "AsRef":
                        Store(c.Dest, values[0].Value, "ptr");
                        break;
                    default:
                        _g._errors.Add("unknown intrinsic Mem." + m.Name);
                        break;
                }
                L($"br label %bb{c.Target.Index}");
            }
        }
    }
}
