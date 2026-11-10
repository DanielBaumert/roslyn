// RustSharp: the ownership and borrow checker. Three stages over MIR:
//   1. static rules: where a move may come from, and what may be written through a shared reference
//   2. move analysis: forward "maybe moved" dataflow over move paths
//   3. non-lexical lifetimes: liveness-based region inference, then loan conflict detection
// Every borrow-carrying local has one region, and a reference to a ref struct has a second one for
// the data behind it: `&'x mut View<'y>`. Two levels are enough because C# only allows `ref` and ref
// structs to hold borrows, and those cannot nest arbitrarily the way Rust's reference types can.

using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis.CSharp.Symbols;

namespace Microsoft.CodeAnalysis.CSharp.Ownership
{
    internal sealed class Bits
    {
        private readonly ulong[] _w;
        public Bits(int n) => _w = new ulong[(n + 63) / 64];
        private Bits(ulong[] w) => _w = w;
        public Bits Clone() => new Bits((ulong[])_w.Clone());
        public bool this[int i]
        {
            get => (_w[i >> 6] & (1UL << (i & 63))) != 0;
            set { if (value) _w[i >> 6] |= 1UL << (i & 63); else _w[i >> 6] &= ~(1UL << (i & 63)); }
        }

        public bool UnionWith(Bits o)
        {
            bool changed = false;
            for (int i = 0; i < _w.Length; i++)
            {
                var v = _w[i] | o._w[i];
                if (v != _w[i]) { _w[i] = v; changed = true; }
            }
            return changed;
        }

        public IEnumerable<int> Ones()
        {
            for (int i = 0; i < _w.Length; i++)
            {
                var v = _w[i];
                while (v != 0)
                {
                    int b = System.Numerics.BitOperations.TrailingZeroCount(v);
                    yield return i * 64 + b;
                    v &= v - 1;
                }
            }
        }
    }

    internal sealed class BorrowChecker
    {
        private enum Access { Copy, Move, Assign, Drop, StorageDead, BorrowShared, BorrowMut }

        private sealed class Loan
        {
            public int Index, Point, Region;
            public Place Place;
            public RefMode Mode;
            public SyntaxNode Syntax;
        }

        private readonly MirBody _b;
        private readonly List<OwnershipDiagnostic> _out;
        private readonly HashSet<(ErrorCode, Location)> _seen = new HashSet<(ErrorCode, Location)>();
        private readonly List<BasicBlock> _blocks;
        private readonly Dictionary<BasicBlock, int> _start = new Dictionary<BasicBlock, int>();
        private readonly Dictionary<BasicBlock, List<BasicBlock>> _preds = new Dictionary<BasicBlock, List<BasicBlock>>();
        private readonly int _points;

        private BorrowChecker(MirBody body, List<OwnershipDiagnostic> diagnostics)
        {
            _b = body;
            _out = diagnostics;
            _blocks = body.Reachable();
            int p = 0;
            foreach (var b in _blocks)
            {
                _start[b] = p;
                p += b.Statements.Count + 1;
                _preds[b] = new List<BasicBlock>();
            }
            _points = p;
            foreach (var b in _blocks)
                foreach (var s in b.Term.Successors.Distinct())
                    _preds[s].Add(b);
        }

        public static void Check(MirBody body, List<OwnershipDiagnostic> diagnostics)
        {
            // Never called: readers of an owned auto-property use the backing field directly.
            if (OwnershipFacts.OwnedAutoPropertyField(body.Method) is not null) return;

            var c = new BorrowChecker(body, diagnostics);
            c.CheckSignature();
            c.StaticRules();
            c.MoveAnalysis();
            c.Nll();
        }

        private void Report(ErrorCode code, string message, SyntaxNode syntax, string label, Action<OwnershipDiagnostic> extra = null)
        {
            var location = (syntax ?? _b.Syntax).Location;
            if (!_seen.Add((code, location))) return;
            var d = new OwnershipDiagnostic { Code = code, Message = message, Location = location, Label = label };
            extra?.Invoke(d);
            _out.Add(d);
        }

        private void CheckSignature()
        {
            var m = _b.Method;
            if (OwnershipFacts.GetLifetimeSig(m).MissingSpecifier)
                Report(ErrorCode.ERR_OwnMissingLifetimeSpecifier,
                    "missing lifetime specifier: the result could borrow from several inputs",
                    m.GetNonNullSyntaxNode(), "name the source with a lifetime such as `ref 'a`, or mark the other inputs `scoped`");

            if (m.IsOverride && m.OverriddenMethod is { } baseMethod)
            {
                CheckReceiverContract(m, baseMethod);
                CheckLifetimeContract(m, baseMethod);
            }

            if (!m.IsStatic && m.MethodKind is MethodKind.Ordinary or MethodKind.PropertyGet or MethodKind.PropertySet or MethodKind.ExplicitInterfaceImplementation)
            {
                foreach (var iface in m.ContainingType.AllInterfacesNoUseSiteDiagnostics)
                {
                    foreach (var slot in iface.GetMembers().OfType<MethodSymbol>())
                    {
                        if (Equals(m.ContainingType.FindImplementationForInterfaceMember(slot)?.OriginalDefinition, m.OriginalDefinition))
                        {
                            CheckReceiverContract(m, slot);
                            CheckLifetimeContract(m, slot);
                        }
                    }
                }
            }
        }

        /// <summary>
        /// Callers tie the result to the inputs the declaration names. An implementation may borrow from
        /// fewer of them, never from others.
        /// </summary>
        private void CheckLifetimeContract(MethodSymbol m, MethodSymbol declared)
        {
            var mine = OwnershipFacts.GetLifetimeSig(m);
            var theirs = OwnershipFacts.GetLifetimeSig(declared);
            if (mine.Output is null && !mine.OutputFromAll) return;
            if (theirs.OutputFromAll || mine.Inputs.Length != theirs.Inputs.Length) return;
            if (theirs.Output is null && !OwnershipFacts.IsBorrowHolder(declared.ReturnType) && declared.RefKind == RefKind.None) return;

            for (int i = 0; i < mine.Inputs.Length; i++)
            {
                bool usesInput = mine.OutputFromAll ? mine.Inputs[i] != null : mine.Inputs[i] == mine.Output;
                bool allowed = theirs.Inputs[i] == theirs.Output;
                if (usesInput && !allowed)
                {
                    Report(ErrorCode.ERR_OwnLifetimeMismatch, $"lifetime of `{m.Name}` does not match `{declared.ContainingType.Name}.{declared.Name}`",
                        m.GetNonNullSyntaxNode(), "the result borrows from an input the declaration does not name");
                    return;
                }
            }
        }

        /// <summary>
        /// A method converted to a delegate type that declares lifetimes: callers of Invoke rely on that
        /// signature, so the method's result may only come from the inputs Invoke names for it. A static
        /// method has no `this`, so its inputs sit one place later in Invoke's.
        /// </summary>
        private void CheckDelegateContract(MethodSymbol m, MethodSymbol invoke, SyntaxNode syntax)
        {
            var mine = OwnershipFacts.GetLifetimeSig(m);
            var theirs = OwnershipFacts.GetLifetimeSig(invoke);
            if (mine.Output is null && !mine.OutputFromAll) return;
            if (mine.Output == "'static" || theirs.OutputFromAll) return;
            int offset = m.IsStatic ? 1 : 0;
            for (int i = 0; i < mine.Inputs.Length; i++)
            {
                bool usesInput = mine.OutputFromAll ? mine.Inputs[i] != null
                    : mine.Inputs[i] == mine.Output || (mine.InputSlots?[i] is { } ms && System.Array.IndexOf(ms, mine.Output) >= 0);
                int j = i + offset;
                bool allowed = j < theirs.Inputs.Length && theirs.Output != null
                    && (theirs.Inputs[j] == theirs.Output || (theirs.InputSlots?[j] is { } ts && System.Array.IndexOf(ts, theirs.Output) >= 0));
                if (usesInput && !allowed)
                {
                    Report(ErrorCode.ERR_OwnLifetimeMismatch, $"lifetime of `{m.Name}` does not match `{invoke.ContainingType.Name}`",
                        syntax, "the result borrows from an input the delegate type does not name for it");
                    return;
                }
            }
        }

        /// <summary>
        /// Callers rely on the declared receiver mode. An implementation may promise more (`readonly`
        /// where mutation was allowed) but never less, and whether `this` is consumed must agree:
        /// otherwise a caller keeps a value the callee already freed.
        /// </summary>
        private void CheckReceiverContract(MethodSymbol m, MethodSymbol declared)
        {
            var mine = OwnershipFacts.GetThisMode(m);
            var theirs = OwnershipFacts.GetThisMode(declared);
            bool ok = theirs switch
            {
                ThisMode.Shared => mine == ThisMode.Shared,
                ThisMode.Mut => mine is ThisMode.Mut or ThisMode.Shared,
                ThisMode.Value => mine == ThisMode.Value,
                _ => true
            };
            if (ok) return;

            string required = theirs == ThisMode.Shared ? "`readonly`" : theirs == ThisMode.Value ? "`move`" : "a borrowing method, not `move`";
            Report(ErrorCode.ERR_OwnReadonlyOverrideMismatch, $"`{m.Name}` must be {required} to match `{declared.ContainingType.Name}.{declared.Name}`",
                m.GetNonNullSyntaxNode(), "receiver does not match the declaration");
        }

        // ---- operand walking

        internal static IEnumerable<Operand> Operands(Rvalue r)
        {
            switch (r)
            {
                case UseRv u: yield return u.Op; break;
                case BinaryRv b: yield return b.Left; yield return b.Right; break;
                case UnaryRv u: yield return u.Value; break;
                case ConvertRv c: yield return c.Value; break;
                case RefCastRv c: yield return c.Value; break;
                case NewArrayRv n: foreach (var l in n.Lengths) yield return l; break;
                case ArrayDimRv a: yield return a.Dimension; break;
                case StackAllocRv a:
                    yield return a.Bytes;
                    if (a.Init != null) foreach (var i in a.Init) yield return i;
                    break;
                case BoxRv b: yield return b.Value; break;
                case UnboxRv b: yield return b.Value; break;
                case NewDelegateRv d:
                    if (d.Target != null) yield return d.Target;
                    if (d.Captures != null) foreach (var c in d.Captures) yield return c;
                    break;
            }
        }

        private static IEnumerable<(Place Place, Access Access, bool Shallow)> Reads(Rvalue r)
        {
            foreach (var op in Operands(r))
            {
                if (op is CopyOp c) yield return (c.Place, Access.Copy, false);
                else if (op is MoveOp m) yield return (m.Place, Access.Move, false);
            }
            switch (r)
            {
                case RefRv x: yield return (x.Place, x.Mode == RefMode.Mut ? Access.BorrowMut : Access.BorrowShared, false); break;
                case ArrayLenRv a: yield return (a.Array, Access.Copy, true); break;
                case ArrayDimRv a: yield return (a.Array, Access.Copy, true); break;
                case IsInstRv i: yield return (i.Place, Access.Copy, true); break;
                case IsNullRv i: yield return (i.Place, Access.Copy, true); break;
                case PeekBoxRv i: yield return (i.Place, Access.Copy, true); break;
                case RetainRv x: yield return (x.Place, Access.Copy, false); break;
                case StructEqRv e:
                    yield return (e.Left, Access.Copy, false);
                    yield return (e.Right, Access.Copy, false);
                    break;
            }
        }

        internal static IEnumerable<Operand> TermOperands(Terminator t)
        {
            switch (t)
            {
                case BranchTerm b: yield return b.Cond; break;
                case SwitchTerm s: yield return s.Value; break;
                case ThrowTerm x: yield return x.Value; break;
                case CallTerm c:
                    if (c.FnPtr != null) yield return c.FnPtr;
                    foreach (var a in c.Args) yield return a;
                    break;
            }
        }

        private static IEnumerable<Place> IndexPlaces(Place p)
        {
            foreach (var proj in p.Projs)
                if (proj is IndexProj i)
                    foreach (var op in i.Indices)
                        if (op is CopyOp c) yield return c.Place;
        }

        // ---- stage 1

        private void StaticRules()
        {
            foreach (var b in _blocks)
            {
                foreach (var s in b.Statements)
                {
                    if (s is not AssignStmt a) continue;
                    CheckNotThroughShared(a.Dest, a.Syntax, assign: true);
                    if (a.Value is RefRv { Mode: RefMode.Mut } r) CheckNotThroughShared(r.Place, a.Syntax, assign: false);
                    CheckStatic(a.Dest, a.Syntax);
                    foreach (var (place, _, _) in Reads(a.Value)) CheckStatic(place, a.Syntax);
                    foreach (var op in Operands(a.Value))
                        if (op is MoveOp m) CheckMoveSource(m.Place, a.Syntax);
                }
                foreach (var op in TermOperands(b.Term))
                {
                    if (op is MoveOp m) CheckMoveSource(m.Place, b.Term.Syntax);
                    if (op is CopyOp { Place: var cp }) CheckStatic(cp, b.Term.Syntax);
                }

                if (b.Term is CallTerm { Method: { Name: "Transmute", ContainingType.Name: "Mem" } } call && !InUnsafeContext(call.Syntax))
                    Report(ErrorCode.ERR_OwnRequiresUnsafe, "`Mem.Transmute` requires an `unsafe` context", call.Syntax, "reinterprets the bits of a value");
            }
        }

        /// <summary>A mutable static is `static mut`: every access is a possible data race.</summary>
        private void CheckStatic(Place p, SyntaxNode syntax)
        {
            if (p.Static is not { } field || field.IsReadOnly || InOwnStaticConstructor(field) || InUnsafeContext(syntax)) return;
            if (field.ContainingType.OriginalDefinition is SynthesizedClosureEnvironment) return;
            Report(ErrorCode.ERR_OwnRequiresUnsafe, $"access to mutable static `{field.Name}` requires an `unsafe` context", syntax, "use of a mutable static",
                d => d.Note = "any code on any thread can change it; make it `readonly`, or use an atomic or a Mutex");
        }

        private bool InOwnStaticConstructor(FieldSymbol field)
            => _b.Method.MethodKind == MethodKind.StaticConstructor && Equals(_b.Method.ContainingType.OriginalDefinition, field.ContainingType.OriginalDefinition);

        private bool InUnsafeContext(SyntaxNode syntax)
        {
            for (var n = syntax; n != null; n = n.Parent)
            {
                switch (n)
                {
                    case Syntax.UnsafeStatementSyntax:
                        return true;
                    case Syntax.BaseMethodDeclarationSyntax { } m when m.Modifiers.Any(SyntaxKind.UnsafeKeyword):
                    case Syntax.BasePropertyDeclarationSyntax { } q when q.Modifiers.Any(SyntaxKind.UnsafeKeyword):
                    case Syntax.BaseTypeDeclarationSyntax { } t when t.Modifiers.Any(SyntaxKind.UnsafeKeyword):
                        return true;
                }
            }
            return false;
        }

        private MirType BaseType(Place p) => p.Static is null ? _b.Locals[p.Local].Type : new MirType(p.Static.Type);

        private void CheckNotThroughShared(Place p, SyntaxNode syntax, bool assign)
        {
            if (p.Static is { IsReadOnly: true } shared && !InOwnStaticConstructor(shared))
            {
                string what = _b.Describe(p);
                if (assign) Report(ErrorCode.ERR_OwnAssignThroughShared, $"cannot assign to `{what}`, which is part of a readonly static", syntax, "readonly statics are shared by all threads");
                else Report(ErrorCode.ERR_OwnMutBorrowThroughShared, $"cannot borrow `{what}` as mutable, because it is part of a readonly static", syntax, "readonly statics are shared by all threads");
                return;
            }

            var t = BaseType(p);
            foreach (var proj in p.Projs)
            {
                if (proj is DerefProj)
                {
                    if (t.Type is PointerTypeSymbol && !t.IsRef) return;
                    if (t.Ref == RefMode.Shared)
                    {
                        string name = _b.Describe(p);
                        if (assign) Report(ErrorCode.ERR_OwnAssignThroughShared, $"cannot assign to `{name}`, which is behind a shared reference", syntax, "cannot be written through a shared reference");
                        else Report(ErrorCode.ERR_OwnMutBorrowThroughShared, $"cannot borrow `{name}` as mutable, because it is behind a shared reference", syntax, "cannot be borrowed as mutable");
                        return;
                    }
                }
                t = MirBody.Project(t, proj);
            }
        }

        /// <summary>Inside a closure, `this` is its own environment, which the creation site has checked.</summary>
        private bool IsClosureEnvironmentPlace(Place p)
            => OwnershipFacts.IsClosureBody(_b.Method) && p.Static is null && p.Local == 1 && MirBody.IsClosureEnvironment(_b.Method.ContainingType)
               && p.Projs.Length >= 2 && p.Projs[0] is DerefProj && p.Projs[1] is FieldProj;

        private void CheckMoveSource(Place p, SyntaxNode syntax)
        {
            if (IsClosureEnvironmentPlace(p)) return;

            string name = _b.Describe(p);
            if (p.Static is not null)
            {
                Report(ErrorCode.ERR_OwnMoveOutOfStatic, $"cannot move out of static field `{name}`", syntax, "move occurs here");
                return;
            }

            var t = BaseType(p);
            if (p.Projs.IsEmpty && t.IsRef && t.Contents && _b.Locals[p.Local].Kind == LocalKind.Arg)
            {
                Report(ErrorCode.ERR_OwnMoveOutOfBorrow, "cannot move out of `this`, which is behind a borrow", syntax, "move occurs here",
                    d => d.Note = "declare the method with the `move` modifier to consume `this`");
                return;
            }

            if (p.Projs.IsEmpty && t.IsRef && t.Contents && _b.Locals[p.Local].Kind == LocalKind.User)
            {
                Report(ErrorCode.ERR_OwnMoveOutOfBorrow, $"cannot move out of `{name}`, which is a pattern variable", syntax, "move occurs here",
                    d => d.Note = "pattern variables borrow from the matched value; use a cast to move it");
                return;
            }

            foreach (var proj in p.Projs)
            {
                switch (proj)
                {
                    case DerefProj when t.IsRef:
                    {
                        string kind = t.Ref == RefMode.Mut ? "mutable reference" : "shared reference";
                        Report(ErrorCode.ERR_OwnMoveOutOfBorrow, $"cannot move out of `{name}`, which is behind a {kind}", syntax, "move occurs here",
                            d => d.Note = "use `Mem.Take` or `Mem.Replace` to take the value and leave another in its place, or borrow it with `ref`");
                        return;
                    }
                    case DerefProj when t.Type is PointerTypeSymbol:
                        Report(ErrorCode.ERR_OwnMoveOutOfBorrow, $"cannot move out of `{name}`, which is behind a raw pointer", syntax, "move occurs here",
                            d => d.Note = "use `Mem.Read`");
                        return;
                    case IndexProj:
                        Report(ErrorCode.ERR_OwnMoveOutOfIndex, $"cannot move out of array element `{name}`", syntax, "move occurs here",
                            d => d.Note = "use `Mem.Take(ref a[i])`, or iterate with `ref`");
                        return;
                    case FieldProj when OwnershipFacts.FindDestructor(t.Type) is not null:
                        Report(ErrorCode.ERR_OwnMoveOutOfDropType, $"cannot move out of `{name}`, because its type `{t.Type.ToDisplayString()}` has a destructor", syntax, "move occurs here");
                        return;
                }
                t = MirBody.Project(t, proj);
            }
        }

        // ---- stage 2

        private sealed class MoveData
        {
            public readonly Dictionary<string, int> Paths = new Dictionary<string, int>();
            public readonly List<List<int>> Children = new List<List<int>>();
            public readonly List<List<(int Point, SyntaxNode Syntax)>> Sites = new List<List<(int, SyntaxNode)>>();

            public int Intern(string key, int parent)
            {
                if (Paths.TryGetValue(key, out int id)) return id;
                id = Paths.Count;
                Paths[key] = id;
                Children.Add(new List<int>());
                Sites.Add(new List<(int, SyntaxNode)>());
                if (parent >= 0) Children[parent].Add(id);
                return id;
            }
        }

        /// <summary>Path keys from the root to the place, stopping where moves can no longer reach.</summary>
        private List<string> PathKeys(Place p, out bool complete)
        {
            var keys = new List<string>();
            complete = false;
            if (p.Static is not null) return keys;
            string key = "_" + p.Local;
            keys.Add(key);
            var t = BaseType(p);
            bool environment = IsClosureEnvironmentPlace(p);
            foreach (var proj in p.Projs)
            {
                if (proj is IndexProj) return keys;
                if (proj is DerefProj)
                {
                    if ((t.IsRef && !(environment && key == "_1")) || (!t.IsRef && t.Type is PointerTypeSymbol)) return keys;
                    key += ".*";
                }
                else if (proj is FieldProj f)
                {
                    key += "." + f.Field.Name;
                }
                keys.Add(key);
                t = MirBody.Project(t, proj);
            }
            complete = true;
            return keys;
        }

        private void MoveAnalysis()
        {
            var data = new MoveData();

            void Register(Place p, int point, SyntaxNode syntax)
            {
                // The exception slot is refilled by the unwinder, which MIR does not show.
                if (p.Local == _b.ExceptionSlot) return;
                var keys = PathKeys(p, out bool complete);
                if (!complete) return;
                int parent = -1;
                foreach (var k in keys) parent = data.Intern(k, parent);
                data.Sites[parent].Add((point, syntax));
            }

            foreach (var b in _blocks)
            {
                int point = _start[b];
                foreach (var s in b.Statements)
                {
                    if (s is AssignStmt a)
                        foreach (var op in Operands(a.Value))
                            if (op is MoveOp m) Register(m.Place, point, s.Syntax);
                    point++;
                }
                foreach (var op in TermOperands(b.Term))
                    if (op is MoveOp m) Register(m.Place, point, b.Term.Syntax);
            }

            int n = data.Paths.Count;
            if (n == 0) return;

            void SetTree(Bits state, int path, bool value)
            {
                state[path] = value;
                foreach (var c in data.Children[path]) SetTree(state, c, value);
            }

            int? Lookup(Place p)
            {
                var keys = PathKeys(p, out bool complete);
                return complete && keys.Count > 0 && data.Paths.TryGetValue(keys[^1], out int id) ? id : null;
            }

            void ApplyMove(Bits state, Operand op)
            {
                if (op is MoveOp m && Lookup(m.Place) is int id) SetTree(state, id, true);
            }

            void ApplyInit(Bits state, Place dest)
            {
                if (Lookup(dest) is int id) SetTree(state, id, false);
            }

            void Transfer(Bits state, Statement s)
            {
                switch (s)
                {
                    case AssignStmt a:
                        foreach (var op in Operands(a.Value)) ApplyMove(state, op);
                        ApplyInit(state, a.Dest);
                        break;
                    case StorageDeadStmt d:
                        if (data.Paths.TryGetValue("_" + d.Local, out int id)) SetTree(state, id, false);
                        break;
                }
            }

            void TransferTerm(Bits state, Terminator t)
            {
                foreach (var op in TermOperands(t)) ApplyMove(state, op);
                if (t is CallTerm { Dest: { } dest }) ApplyInit(state, dest);
            }

            var entry = _blocks.ToDictionary(b => b, _ => new Bits(n));
            var work = new Queue<BasicBlock>(_blocks);
            var queued = new HashSet<BasicBlock>(_blocks);
            while (work.Count > 0)
            {
                var b = work.Dequeue();
                queued.Remove(b);
                var state = entry[b].Clone();
                foreach (var s in b.Statements) Transfer(state, s);
                TransferTerm(state, b.Term);
                foreach (var succ in b.Term.Successors)
                    if (entry[succ].UnionWith(state) && queued.Add(succ)) work.Enqueue(succ);
            }

            bool HasMovedChild(Bits state, int path)
                => data.Children[path].Any(c => state[c] || HasMovedChild(state, c));

            int FirstMovedChild(Bits state, int path)
            {
                foreach (var c in data.Children[path])
                {
                    if (state[c]) return c;
                    int r = FirstMovedChild(state, c);
                    if (r >= 0) return r;
                }
                return -1;
            }

            void CheckUse(Bits state, Place place, bool borrow, bool assignDest, int point, SyntaxNode syntax)
            {
                var keys = PathKeys(place, out bool complete);
                for (int i = 0; i < keys.Count; i++)
                {
                    if (!data.Paths.TryGetValue(keys[i], out int id)) continue;
                    bool isLast = complete && i == keys.Count - 1;
                    if (assignDest && isLast) return;
                    if (state[id])
                    {
                        ReportMoved(place, id, data, borrow, point, syntax, partial: false);
                        return;
                    }
                    if (isLast && !assignDest && FirstMovedChild(state, id) is var child and >= 0)
                    {
                        ReportMoved(place, child, data, borrow, point, syntax, partial: true);
                        return;
                    }
                }
            }

            foreach (var b in _blocks)
            {
                var state = entry[b].Clone();
                int point = _start[b];
                foreach (var s in b.Statements)
                {
                    if (s is AssignStmt a)
                    {
                        foreach (var (place, access, shallow) in Reads(a.Value))
                        {
                            CheckUse(state, place, access is Access.BorrowMut or Access.BorrowShared, false, point, a.Syntax);
                            foreach (var ip in IndexPlaces(place)) CheckUse(state, ip, false, false, point, a.Syntax);
                        }
                        if (!a.Dest.IsLocal) CheckUse(state, a.Dest, false, true, point, a.Syntax);
                    }
                    Transfer(state, s);
                    point++;
                }
                foreach (var op in TermOperands(b.Term))
                {
                    if (op is CopyOp c) CheckUse(state, c.Place, false, false, point, b.Term.Syntax);
                    else if (op is MoveOp m) CheckUse(state, m.Place, false, false, point, b.Term.Syntax);
                }
            }
        }

        private void ReportMoved(Place place, int movedPath, MoveData data, bool borrow, int point, SyntaxNode syntax, bool partial)
        {
            string name = _b.Describe(place);
            var site = data.Sites[movedPath].OrderBy(s => s.Point < point ? 0 : 1).ThenByDescending(s => s.Point).FirstOrDefault();
            string prefix = partial ? "partially moved value" : "moved value";
            var code = borrow ? ErrorCode.ERR_OwnBorrowOfMovedValue : ErrorCode.ERR_OwnUseOfMovedValue;
            string message = (borrow ? "borrow of " : "use of ") + prefix + $": `{name}`";
            Report(code, message, syntax, borrow ? "value borrowed here after move" : "value used here after move", d =>
            {
                if (site.Syntax != null)
                {
                    bool sameOrLater = site.Point >= point;
                    d.Secondary.Add((site.Syntax.Location, sameOrLater ? "value moved here, in the previous iteration of the loop" : "value moved here"));
                }
                var type = _b.TypeOf(place);
                if (place.Static is null && MirBody.IsClosureEnvironment(_b.Locals[place.Local].Type.Type))
                    d.Note = "a capturing lambda owns the variables it captures, together with all other captured variables of this scope";
                else if (!type.IsRef)
                    d.Note = $"move occurs because the value has type `{type.Type.ToDisplayString()}`, which is not Copy";
            });
        }

        // ---- stage 3

        private readonly List<Bits> _regions = new List<Bits>();
        private readonly List<(int Sup, int Sub, SyntaxNode Syntax)> _edges = new List<(int, int, SyntaxNode)>();
        private readonly Dictionary<string, int> _universal = new Dictionary<string, int>();
        private readonly List<int> _universalRegions = new List<int>();
        private readonly List<Loan> _loans = new List<Loan>();
        private readonly Dictionary<Statement, Loan> _loanAt = new Dictionary<Statement, Loan>();
        private readonly HashSet<(int Sup, int Sub)> _implied = new HashSet<(int, int)>();
        private int[] _localRegion;
        private int[] _localInner;
        /// <summary>
        /// Lifetime parameters: for a local whose type (or, for a reference, whose referent) declares
        /// lifetimes, one region per slot, such as 'a and 'b of Pair&lt;'a, 'b&gt;; null for any other local.
        /// The local's own region (or inner region) stays the whole value: every slot outlives it, so a
        /// live value keeps all its lifetimes alive, as in Rust. Only a field access picks a single slot.
        /// </summary>
        private int[][] _localSlots;

        /// <summary>The slots of the value at a whole local, or behind a reference local; null otherwise.</summary>
        private int[] SlotsOf(Place p)
        {
            if (p is null || p.Static is not null || _localSlots[p.Local] is not { } slots) return null;
            if (p.Projs.IsEmpty) return slots;
            if (p.Projs.Length == 1 && p.Projs[0] is DerefProj && IsIndirect(p.Local)) return slots;
            // `ref Stack<T> s`: through the reference, then the class's handle.
            if (p.Projs.Length == 2 && p.Projs[0] is DerefProj && p.Projs[1] is DerefProj && IsRefToHandle(p.Local)) return slots;
            return FieldObjectSlots(p, slots);
        }

        /// <summary>
        /// The slots of the object a field holds (`this._inner` for a `Stack&lt;T&gt; _inner` in an `Outer&lt;T&gt;`), in
        /// terms of the container's slots: Stack's T slot is Outer's. A lifetime the container does not
        /// have is 'static, as for any place no region tracks.
        /// </summary>
        private int[] FieldObjectSlots(Place p, int[] container)
        {
            int i = IsIndirect(p.Local) ? 1 : 0;
            if (i == 1 && (p.Projs.Length == 0 || p.Projs[0] is not DerefProj)) return null;
            if (i == 1 && IsRefToHandle(p.Local) && p.Projs.Length > 1 && p.Projs[1] is DerefProj) i = 2;
            if (i >= p.Projs.Length || p.Projs[i] is not FieldProj f) return null;
            int rest = p.Projs.Length - i - 1;
            if (rest > 1 || (rest == 1 && (p.Projs[^1] is not DerefProj || f.Field.Type.TypeKind is not (TypeKind.Class or TypeKind.Interface)))) return null;
            var names = Lifetimes.Slots(f.Field.OriginalDefinition.Type, Lifetimes.FieldTypeSyntax(f.Field), "field");
            // The field's type as this container has it: what its type parameters stand for unfolds the same way.
            names = Lifetimes.Expand(f.Field.OriginalDefinition.Type, f.Field.Type, names);
            if (names is null) return null;
            var containerNames = Lifetimes.Layout(_b.Locals[p.Local].Type.Type).Select(e => e.Name).ToList();
            var result = new int[names.Length];
            for (int k = 0; k < names.Length; k++)
            {
                if (names[k] == "'static") { result[k] = Universal("'static"); continue; }
                int at = containerNames.IndexOf(names[k]);
                // A lifetime the container does not name: no mapping, as before.
                if (at < 0 || at >= container.Length) return null;
                result[k] = container[at];
            }
            return result;
        }

        private int[] SlotsOf(Operand op) => SlotsOf(op is CopyOp c ? c.Place : op is MoveOp m ? m.Place : null);

        /// <summary>Whether a place is reached by dereferencing a raw pointer, which unsafe code answers for.</summary>
        private bool ThroughRawPointer(Place p)
        {
            if (p.Static is not null) return false;
            var t = BaseType(p);
            foreach (var proj in p.Projs)
            {
                if (proj is DerefProj && !t.IsRef && t.Type is PointerTypeSymbol) return true;
                t = MirBody.Project(t, proj);
            }
            return false;
        }

        /// <summary>Whether a type parameter belongs to the method being checked or to a type around it.</summary>
        private bool OwnsTypeParameter(TypeParameterSymbol tp)
        {
            for (Symbol s = _b.Method.OriginalDefinition; s is not null; s = s.ContainingSymbol)
                if (ReferenceEquals(tp.ContainingSymbol.OriginalDefinition, s.OriginalDefinition)) return true;
            return false;
        }

        /// <summary>Whether a local reaches its value through a dereference: a reference, or a class's handle.</summary>
        private bool IsIndirect(int local) => _b.Locals[local].Type.IsRef || _b.Locals[local].Type.Type.TypeKind == TypeKind.Class;

        /// <summary>A reference to a class's handle, such as `ref Stack&lt;T&gt; s` (not `&amp;contents`, which points at the object).</summary>
        private bool IsRefToHandle(int local) => _b.Locals[local].Type is { IsRef: true, Contents: false } t && t.Type.TypeKind is TypeKind.Class or TypeKind.Interface;

        /// <summary>The field of a lifetime-parameterized value that a place goes through, with its slot; -1 if none.</summary>
        private int SlotField(Place p, out FieldSymbol field)
        {
            field = null;
            if (p.Static is not null || _localSlots[p.Local] is null) return -1;
            int i = IsIndirect(p.Local) ? 1 : 0;
            if (i == 1 && (p.Projs.Length == 0 || p.Projs[0] is not DerefProj)) return -1;
            if (i == 1 && IsRefToHandle(p.Local) && p.Projs.Length > 1 && p.Projs[1] is DerefProj) i = 2;
            if (i >= p.Projs.Length || p.Projs[i] is not FieldProj f) return -1;
            field = f.Field;
            // The declared slot, found among the value's slots; one that unfolds into several (a T that
            // stands for a Pair<'a, 'b>) is no single region: the value's own, shorter than each, is used.
            int declared = Lifetimes.FieldSlot(f.Field);
            var layout = Lifetimes.Layout(_b.Locals[p.Local].Type.Type);
            // A container's field that holds its T (a tuple's Item1): the slots T unfolds into, as Rust's `t.0`.
            if (declared < 0)
                return f.Field.OriginalDefinition.Type is TypeParameterSymbol && !layout.IsEmpty
                    && OwnershipFacts.HasAttribute(f.Field.ContainingType, "CarriesBorrowsAttribute") ? -2 : -1;
            for (int k = 0; k < layout.Length; k++)
                if (layout[k].DefSlot == declared) return layout[k].Sub < 0 ? k : -2;
            return -1;
        }

        private readonly Dictionary<string, int> _unfoldedRegions = new();

        /// <summary>
        /// A field whose slot unfolds (`T V` in a Box&lt;Pair&lt;'a, 'b&gt;&gt;): its value has the slots of what T
        /// stands for, so `box.V.B` lives for 'b alone. The field as a whole lives no longer than any of them.
        /// </summary>
        private int UnfoldedFieldRegion(Place p)
        {
            int i = IsIndirect(p.Local) ? 1 : 0;
            if (i == 1 && IsRefToHandle(p.Local) && p.Projs.Length > 1 && p.Projs[1] is DerefProj) i = 2;
            if (i >= p.Projs.Length || p.Projs[i] is not FieldProj f) return -1;
            var fieldPlace = new Place(p.Local, System.Collections.Immutable.ImmutableArray.CreateRange(p.Projs.Take(i + 1)));
            if (SlotsOf(fieldPlace) is not { } slots || slots.Length == 0) return -1;
            int next = i + 1;
            if (next < p.Projs.Length && p.Projs[next] is DerefProj && f.Field.Type.TypeKind is TypeKind.Class) next++;
            if (next < p.Projs.Length && p.Projs[next] is FieldProj g && Lifetimes.FieldSlot(g.Field) is int declared and >= 0)
            {
                var layout = Lifetimes.Layout(f.Field.Type);
                for (int k = 0; k < layout.Length && k < slots.Length; k++)
                    if (layout[k].DefSlot == declared && layout[k].Sub < 0) return slots[k];
            }
            var key = p.Local + ":" + i + ":" + f.Field.Name;
            if (!_unfoldedRegions.TryGetValue(key, out int all))
            {
                _unfoldedRegions[key] = all = NewRegion();
                foreach (var s in slots) Outlives(s, all, _b.Syntax);
            }
            return all;
        }

        private int NewRegion()
        {
            _regions.Add(new Bits(_points + 64));
            return _regions.Count - 1;
        }

        /// <summary>
        /// A value moves from slot <paramref name="from"/> to slot <paramref name="to"/>: as Rust's variance has it,
        /// covariant may shorten, contravariant may lengthen, invariant must stay the same.
        /// </summary>
        private void Relate(int from, int to, Variance v, SyntaxNode syntax)
        {
            if (v is Variance.Covariant or Variance.Invariant) Outlives(from, to, syntax);
            if (v is Variance.Contravariant or Variance.Invariant) Outlives(to, from, syntax);
        }

        private void Outlives(int sup, int sub, SyntaxNode syntax)
        {
            if (sup >= 0 && sub >= 0 && sup != sub) _edges.Add((sup, sub, syntax));
        }

        private int Universal(string name)
        {
            if (_universal.TryGetValue(name, out int r)) return r;
            r = NewRegion();
            _universal[name] = r;
            _universalRegions.Add(r);
            for (int i = 0; i < _points; i++) _regions[r][i] = true;
            if (_universalRegions.Count <= 64) _regions[r][_points + _universalRegions.Count - 1] = true;
            return r;
        }

        private int RegionOf(Operand op) => op switch
        {
            CopyOp c => RegionOf(c.Place),
            MoveOp m => RegionOf(m.Place),
            _ => -1
        };

        /// <summary>The region of the data a place holds: behind a reference, that is the inner region.</summary>
        private int RegionOf(Place p)
        {
            if (p.Static is not null) return -1;

            // A field that names a lifetime parameter, `ref readonly 'a int X` or `Ref<'a, int> R`, borrows for
            // that slot only, also in a heap object that declares the lifetime.
            int slot = SlotField(p, out _);
            if (slot >= 0) return _localSlots[p.Local][slot];
            if (slot == -2 && UnfoldedFieldRegion(p) is int unfolded and >= 0) return unfolded;

            // Nothing else in a heap object can hold a borrow: its fields live as long as the program may.
            // Tasks are the exception, because a task is a borrow holder itself.
            var t = BaseType(p);
            foreach (var proj in p.Projs)
            {
                if (t.Contents && !OwnershipFacts.IsCoroutineType(t.Type) && !OwnershipFacts.AnonymousHoldsBorrows(t.Type)) return -1;
                t = MirBody.Project(t, proj);
            }

            if (_localInner[p.Local] >= 0 && p.Projs.Length > 0 && p.Projs[0] is DerefProj) return _localInner[p.Local];
            return _localRegion[p.Local];
        }

        private void Flow(Operand op, Place dest, SyntaxNode syntax)
        {
            Place src = op is CopyOp c ? c.Place : op is MoveOp m ? m.Place : null;
            if (src is null) return;
            Outlives(RegionOf(src), RegionOf(dest), syntax);
            if (src.IsLocal && dest.IsLocal) Outlives(_localInner[src.Local], _localInner[dest.Local], syntax);
            // Slot by slot: a value may move to where its lifetimes are shorter (covariance).
            if (SlotsOf(src) is { } from && SlotsOf(dest) is { } to && from.Length == to.Length)
                for (int k = 0; k < from.Length; k++) Relate(from[k], to[k], Lifetimes.VarianceOf(_b.TypeOf(src).Type, k), syntax);
        }

        /// <summary>
        /// Whether a reborrow reaches its data through a shared reference field with a lifetime parameter.
        /// Like Rust's supporting prefixes, the borrow then depends on that field's lifetime alone, not on
        /// the reference that led to the value: <c>ref pair.X</c> through <c>in Pair&lt;'a, 'b&gt; pair</c> lives for 'a.
        /// </summary>
        /// <summary>
        /// Whether a place, rooted at a reference to a borrow holder, dereferences a reference stored in one of
        /// its fields: <c>*((*t).P)</c> for <c>ref View t</c>. What that reaches lives for the holder's data.
        /// </summary>
        private bool DerefsReferenceFieldBehindReference(Place p)
        {
            if (_localInner[p.Local] < 0 || p.Projs.Length < 3 || p.Projs[0] is not DerefProj) return false;
            for (int i = 1; i + 1 < p.Projs.Length; i++)
                if (p.Projs[i] is FieldProj { Field.RefKind: not RefKind.None } && p.Projs[i + 1] is DerefProj) return true;
            return false;
        }

        /// <summary>Whether a place ends at a field, or at the object a class-typed field points to.</summary>
        private static bool EndsAtField(Place p)
            => p.Projs[^1] is FieldProj || (p.Projs.Length >= 2 && p.Projs[^1] is DerefProj && p.Projs[^2] is FieldProj { Field.Type.TypeKind: TypeKind.Class });

        private bool ThroughSharedSlotField(Place p)
            => SlotField(p, out var field) >= 0 && field.RefKind == RefKind.RefReadOnly;

        /// <summary>A loan is pointless behind a shared reference or a raw pointer.</summary>
        private bool NeedsLoan(Place p)
        {
            if (p.Static is not null) return false;
            if (_b.Locals[p.Local].IsStaticString) return false;
            var t = BaseType(p);
            foreach (var proj in p.Projs)
            {
                if (proj is DerefProj && (t.Ref == RefMode.Shared || (!t.IsRef && t.Type is PointerTypeSymbol))) return false;
                t = MirBody.Project(t, proj);
            }
            return true;
        }

        private bool PassesRefDeref(Place p)
        {
            var t = BaseType(p);
            foreach (var proj in p.Projs)
            {
                if (proj is DerefProj && t.IsRef) return true;
                t = MirBody.Project(t, proj);
            }
            return false;
        }

        private void Nll()
        {
            _localRegion = new int[_b.Locals.Count];
            _localInner = new int[_b.Locals.Count];
            var sig = OwnershipFacts.GetLifetimeSig(_b.Method);
            for (int i = 0; i < _localRegion.Length; i++)
            {
                var type = _b.Locals[i].Type;
                _localRegion[i] = OwnershipFacts.CarriesBorrow(type) ? NewRegion() : -1;
                _localInner[i] = type.IsRef && !type.Contents && OwnershipFacts.IsBorrowHolder(type.Type) ? NewRegion() : -1;
            }

            _localSlots = new int[_b.Locals.Count][];
            for (int i = 0; i < _localSlots.Length; i++)
            {
                var type = _b.Locals[i].Type;
                int n = Lifetimes.Layout(type.Type).Length;
                int whole = type.Contents ? -1 : type.IsRef ? _localInner[i] : _localRegion[i];
                // A reference into a heap object (`&contents Index`) has no region for the object as a whole,
                // only its slots; the object's owner keeps them alive.
                if (n == 0 || (whole < 0 && !type.Contents)) continue;
                _localSlots[i] = new int[n];
                for (int k = 0; k < n; k++)
                {
                    _localSlots[i][k] = NewRegion();
                    if (whole >= 0) Outlives(_localSlots[i][k], whole, _b.Syntax);
                }
            }

            int returnRegion = -1;
            for (int i = 0; i < sig.Inputs.Length && i < _b.ArgCount; i++)
            {
                int local = i + 1;
                if (_localRegion[local] < 0) continue;
                string name = sig.Inputs[i] ?? "'#anon" + i;
                if (_localInner[local] >= 0 && sig.NamesBorrow?[i] == true)
                {
                    // `ref 'a T t`: as in Rust, 'a is the borrow; what it points at lives for T's own lifetime.
                    int outer = Universal(name);
                    int inner = Universal(sig.Held?[i] ?? "'#inner" + local);
                    _localInner[local] = inner;
                    _localRegion[local] = outer;
                    _implied.Add((inner, outer));
                    Outlives(inner, outer, _b.Syntax);
                }
                else if (_localInner[local] >= 0)
                {
                    // `&'outer mut View<'name>`: the name is the data, and the data outlives the reference.
                    int inner = Universal(name);
                    int outer = Universal("'#outer" + local);
                    _localInner[local] = inner;
                    _localRegion[local] = outer;
                    _implied.Add((inner, outer));
                    Outlives(inner, outer, _b.Syntax);
                    if (name == sig.Output && name.StartsWith("'#", StringComparison.Ordinal)) returnRegion = outer;
                }
                else
                {
                    _localRegion[local] = Universal(name);
                }
            }
            // Borrow-carrying inputs the signature does not name still outlive the call.
            for (int local = 1; local <= _b.ArgCount; local++)
                if (_localRegion[local] >= 0 && !_universalRegions.Contains(_localRegion[local]))
                    _localRegion[local] = Universal("'#anon" + local);

            // Lifetime parameters of the inputs: each slot is the universal region its name stands for, and
            // outlives the value as a whole (a Pair<'a, 'b> is valid only while 'a and 'b are).
            // An input's lifetimes are unknown to the body, so every slot of an argument is a universal
            // region, named or not: a free region would satisfy any constraint.
            for (int local = 1; local <= _b.ArgCount; local++)
            {
                if (_localSlots[local] is not { } slots) continue;
                int i = local - 1;
                var names = i < sig.Inputs.Length ? sig.InputSlots?[i] : null;
                if (names is not null && names.Length != slots.Length) names = null;
                int whole = _localInner[local] >= 0 ? _localInner[local] : _localRegion[local];
                for (int k = 0; k < slots.Length; k++)
                {
                    slots[k] = Universal(names?[k] ?? "'#unnamed" + local + "." + k);
                    if (whole >= 0) DeclareOutlives(slots[k], whole);
                }
            }

            // '#data: what a ref struct or reference returns lives as long as what it points at.
            if (sig.Output == "'#data" && _b.ArgCount > 0 && _localInner[1] >= 0) returnRegion = _localInner[1];
            // '#data+: as long as that and the other borrowed inputs, but not the borrow of `this`.
            if (sig.Output == "'#data+")
            {
                int shortest = Universal("'#data+");
                if (_b.ArgCount > 0 && _localInner[1] >= 0) DeclareOutlives(_localInner[1], shortest);
                for (int local = 2; local <= _b.ArgCount; local++)
                {
                    int u = _localInner[local] >= 0 ? _localInner[local] : _localRegion[local];
                    if (u >= 0) DeclareOutlives(u, shortest);
                }
                returnRegion = shortest;
            }

            if (_localRegion[0] >= 0)
            {
                if (returnRegion >= 0) _localRegion[0] = returnRegion;
                else if (sig.Output != null) _localRegion[0] = Universal(sig.Output);
                else if (sig.OutputFromAll)
                    foreach (var u in _universalRegions.ToList()) Outlives(u, _localRegion[0], _b.Syntax);
            }

            // The result's slots: a named one is the caller's lifetime; one that is the whole result's
            // lifetime (elided where nothing names it) is just that region.
            if (sig.OutputSlots is { } outNames && _localSlots[0] is { } outSlots && outSlots.Length == outNames.Length)
                for (int k = 0; k < outSlots.Length; k++)
                    outSlots[k] = outNames[k] == OwnershipFacts.WholeResult ? (_b.Locals[0].Type.IsRef ? _localInner[0] : _localRegion[0]) : Universal(outNames[k]);

            foreach (var (longer, shorter) in sig.Bounds) DeclareOutlives(Universal(longer), Universal(shorter));
            CloseImplied();

            BuildConstraints();
            AddLiveness();
            Propagate();
            CheckUniversal();
            CheckLoans();
        }

        private void DeclareOutlives(int longer, int shorter)
        {
            _implied.Add((longer, shorter));
            Outlives(longer, shorter, _b.Syntax);
        }

        /// <summary>Declared relations are transitive: `'a : 'b` and `'b : 'c` give `'a : 'c`.</summary>
        private void CloseImplied()
        {
            bool changed = true;
            while (changed)
            {
                changed = false;
                foreach (var (a, b) in _implied.ToList())
                    foreach (var (c, d) in _implied.ToList())
                        if (b == c && a != d && _implied.Add((a, d))) changed = true;
            }
        }

        private void BuildConstraints()
        {
            foreach (var b in _blocks)
            {
                int point = _start[b];
                foreach (var s in b.Statements)
                {
                    if (s is AssignStmt a)
                    {
                        if (a.Value is NewDelegateRv nd && !OwnershipFacts.IsClosureBody(nd.Method) && _b.TypeOf(a.Dest).Type is NamedTypeSymbol { DelegateInvokeMethod: { } invoke } dt
                            && Lifetimes.DelegateDeclaresLifetimes(dt))
                            CheckDelegateContract(nd.Method, invoke, a.Syntax);
                        int dest = RegionOf(a.Dest);
                        if (a.Value is RefRv r)
                        {
                            int data = RegionOf(r.Place);
                            int destInner = a.Dest.IsLocal ? _localInner[a.Dest.Local] : -1;
                            if (OwnershipFacts.CarriesBorrow(_b.TypeOf(r.Place)))
                            {
                                // &mut to a borrow holder is invariant in the data's region.
                                Outlives(data, destInner >= 0 ? destInner : dest, a.Syntax);
                                if (destInner >= 0 && r.Mode == RefMode.Mut) Outlives(destInner, data, a.Syntax);
                            }
                            if (r.Place.Static is null && PassesRefDeref(r.Place) && !ThroughSharedSlotField(r.Place)) Outlives(_localRegion[r.Place.Local], dest, a.Syntax);
                            // Rust's supporting prefixes: a reborrow through a reference field lives no longer
                            // than that field's lifetime; through a shared one, that is all it depends on.
                            if (r.Place.Static is null && PassesRefDeref(r.Place) && SlotField(r.Place, out _) is int fieldSlot and >= 0)
                                Outlives(_localSlots[r.Place.Local][fieldSlot], dest, a.Syntax);
                            // Without a lifetime parameter, a reference field borrows for the struct's one implicit
                            // lifetime: through `ref View t`, `ref t.P[0]` must not outlive what v borrows either.
                            else if (r.Place.Static is null && DerefsReferenceFieldBehindReference(r.Place))
                                Outlives(_localInner[r.Place.Local], dest, a.Syntax);
                            // `&p` for a Pair<'a, 'b>: the reference sees the same slots; `&mut` may also store, so it is invariant.
                            if (SlotsOf(r.Place) is { } from && SlotsOf(a.Dest) is { } to && from.Length == to.Length)
                                for (int k = 0; k < from.Length; k++)
                                {
                                    Relate(from[k], to[k], r.Mode == RefMode.Mut ? Variance.Invariant : Lifetimes.VarianceOf(_b.TypeOf(r.Place).Type, k), a.Syntax);
                                }
                            // A value kept where no region tracks it (a captured variable in a closure's
                            // environment, a field of an object without lifetimes) had to be 'static to get
                            // there; through `&mut`, only 'static borrows may be stored into it.
                            else if (r.Mode == RefMode.Mut && SlotsOf(r.Place) is null && SlotsOf(a.Dest) is { } into)
                                foreach (var k in into) Outlives(k, Universal("'static"), a.Syntax);
                            // Remember what a receiver borrows, for the content lifetime of containers.
                            if (a.Dest.IsLocal && r.Place.Static is null && r.Place.Projs.All(x => x is DerefProj)) _refSource[a.Dest.Local] = r.Place.Local;
                            // A container in a field that names a lifetime (`List<Ref<'a, int>> Items`): its content
                            // lives for that slot.
                            if (a.Dest.IsLocal && r.Place.Static is null && SlotField(r.Place, out _) is int contentSlot and >= 0 && EndsAtField(r.Place))
                                _refSlot[a.Dest.Local] = _localSlots[r.Place.Local][contentSlot];
                            if (NeedsLoan(r.Place))
                            {
                                var loan = new Loan { Index = _loans.Count, Point = point, Region = NewRegion(), Place = r.Place, Mode = r.Mode, Syntax = a.Syntax };
                                _loans.Add(loan);
                                _loanAt[s] = loan;
                                Outlives(loan.Region, dest, a.Syntax);
                            }
                        }
                        else if (dest >= 0)
                        {
                            foreach (var op in Operands(a.Value)) Flow(op, a.Dest, a.Syntax);
                        }
                        else if (a.Value is not LinkRv && !ThroughRawPointer(a.Dest))
                        {
                            // A place without a region (a field of an object, a static) outlives any scope.
                            // Not behind a raw pointer: in unsafe code, borrows through raw pointers are not
                            // checked, as with Rust's `*cell.get() = x`; the code that wrote it answers for it.
                            foreach (var op in Operands(a.Value)) RequireStatic(op, a.Syntax);
                        }
                    }
                    point++;
                }

                if (b.Term is CallTerm { Method: { } m } c) CallConstraints(c, m);
            }
        }

        private void RequireStatic(Operand op, SyntaxNode syntax)
        {
            Place p = op is CopyOp c ? c.Place : op is MoveOp m ? m.Place : null;
            if (p is null) return;
            int region = RegionOf(p);
            var type = _b.TypeOf(p);

            // A moved `this` or pattern variable is an error of its own, reported by the move rules.
            if (region >= 0 && OwnershipFacts.CarriesBorrow(type) && !type.Contents) Outlives(region, Universal("'static"), syntax);
        }

        private readonly Dictionary<int, int> _refSource = new Dictionary<int, int>();
        /// <summary>Receivers borrowed from a container field with a lifetime parameter: the slot its content lives for.</summary>
        private readonly Dictionary<int, int> _refSlot = new Dictionary<int, int>();

        /// <summary>The region of the container a receiver borrows, or -1.</summary>
        private int ContentRegion(Operand receiver)
        {
            Place p = receiver is CopyOp c ? c.Place : receiver is MoveOp mo ? mo.Place : null;
            if (p is null || !p.IsLocal) return -1;
            if (_refSlot.TryGetValue(p.Local, out int slotContent)) return slotContent;
            int local = _refSource.TryGetValue(p.Local, out int source) ? source : p.Local;
            var t = _b.Locals[local].Type;
            return t.IsRef || !OwnershipFacts.CarriesBorrows(t.Type) ? -1 : _localRegion[local];
        }

        /// <summary>The type a method declares for its argument <paramref name="i"/> (the receiver first), with its own type parameters.</summary>
        private static TypeSymbol DeclaredType(MethodSymbol m, int i)
        {
            var def = m.OriginalDefinition;
            if (!def.IsStatic && i == 0) return def.ContainingType;
            int p = i - (def.IsStatic ? 0 : 1);
            return p >= 0 && p < def.Parameters.Length ? def.Parameters[p].Type : null;
        }

        private void CallConstraints(CallTerm c, MethodSymbol m)
        {
            // `unsafe` escape hatch: the result of a transmute has no relation to its input.
            if (m.Name == "Transmute" && m.ContainingType.Name == "Mem") return;

            var sig = OwnershipFacts.GetLifetimeSig(m);
            var fresh = new Dictionary<string, int>();
            int Fresh(string name)
            {
                if (name == "'static") return Universal(name);
                if (!fresh.TryGetValue(name, out int r))
                {
                    fresh[name] = r = NewRegion();
                    // A region inside what T stands for outlives T's lifetime, Rust's `T: 'x` for every region in T.
                    int part = name.LastIndexOf('/');
                    if (part > 0 && name.StartsWith("'#T:", StringComparison.Ordinal)) Outlives(r, Fresh(name.Substring(0, part)), c.Syntax);
                }
                return r;
            }

            int InnerOf(Operand op) => op is CopyOp { Place: { IsLocal: true } cp } ? _localInner[cp.Local]
                : op is MoveOp { Place: { IsLocal: true } mp } ? _localInner[mp.Local] : -1;

            int content = !m.IsStatic && c.Args.Count > 0 ? ContentRegion(c.Args[0]) : -1;

            for (int i = 0; i < c.Args.Count && i < sig.Inputs.Length; i++)
            {
                var name = sig.Inputs[i];
                int arg = RegionOf(c.Args[i]);
                if (name == "'#self")
                {
                    // Stored into a container: what it borrows must outlive the container, like Vec::push.
                    if (content >= 0) Outlives(arg, content, c.Syntax);
                    else RequireStatic(c.Args[i], c.Syntax);
                    continue;
                }
                if (name is null)
                {
                    // Handed to a parameter that cannot express a borrow, such as `T` in `List<T>.Add`.
                    RequireStatic(c.Args[i], c.Syntax);
                    continue;
                }
                if (arg < 0) continue;
                int f = Fresh(name);
                int inner = InnerOf(c.Args[i]);
                if (inner >= 0 && sig.NamesBorrow?[i] == true)
                {
                    // `ref 'a T t`: the name is the borrow; the data is bound through T's lifetime below.
                    Outlives(arg, f, c.Syntax);
                    if (sig.Held?[i] is { } dataName)
                    {
                        Outlives(inner, Fresh(dataName), c.Syntax);
                        if (c.Args[i] is MoveOp) Outlives(Fresh(dataName), inner, c.Syntax);
                    }
                }
                else if (inner >= 0)
                {
                    // The signature names the data behind `ref View`; the callee may store into it.
                    Outlives(inner, f, c.Syntax);
                    if (c.Args[i] is MoveOp) Outlives(f, inner, c.Syntax);
                }
                else
                {
                    Outlives(arg, f, c.Syntax);
                }
            }

            foreach (var (longer, shorter) in sig.Bounds) Outlives(Fresh(longer), Fresh(shorter), c.Syntax);

            // A value passed where the callee sees a type parameter (`T x`, `ref T x`) brings all its regions,
            // its slots too: T may stand for a Pair<'a, 'b>, and the callee only knows 'T.
            for (int i = 0; i < c.Args.Count && i < sig.Inputs.Length; i++)
            {
                if (sig.Held?[i] is not { } tname || SlotsOf(c.Args[i]) is not { } held) continue;
                var heldPlace = c.Args[i] is CopyOp hc ? hc.Place : ((MoveOp)c.Args[i]).Place;
                bool storesInto = _b.TypeOf(heldPlace).Ref == RefMode.Mut || OwnershipFacts.ContainsInvariance(_b.TypeOf(heldPlace).Type);
                foreach (var slot in held)
                {
                    Outlives(slot, Fresh(tname), c.Syntax);
                    if (storesInto) Outlives(Fresh(tname), slot, c.Syntax);
                }
            }

            // A receiver without slots of its own, such as a value of type T bound by `T : IStore<U>`: the
            // callee's slots stand for the type arguments it was called with, here U's lifetime. What
            // cannot be named is 'static, as for any place no region tracks.
            if (!m.IsStatic && c.Args.Count > 0 && sig.InputSlots?[0] is { } receiverNames && SlotsOf(c.Args[0]) is null && m.ContainingType is { } callee)
            {
                int written = Lifetimes.WrittenCount(callee);
                var args = callee.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics;
                for (int k = 0; k < receiverNames.Length; k++)
                {
                    int i = k - written;
                    int region = Universal("'static");
                    if (i >= 0 && i < args.Length)
                    {
                        var parametric = OwnershipFacts.ParametricIn(args[i].Type);
                        if (parametric.Count == 1 && OwnsTypeParameter(parametric[0])) region = Universal(OwnershipFacts.TypeParameterLifetime(parametric[0]));
                    }
                    Outlives(region, Fresh(receiverNames[k]), c.Syntax);
                    Outlives(Fresh(receiverNames[k]), region, c.Syntax);
                }
            }

            // Lifetime parameters: each slot of an argument outlives the lifetime its parameter names;
            // through `ref` (or a constructor's `this`) the callee may store into it, so the slot is invariant.
            for (int i = 0; i < c.Args.Count && i < sig.Inputs.Length; i++)
            {
                if (SlotsOf(c.Args[i]) is not { } slots) continue;
                var argPlace = c.Args[i] is CopyOp cp ? cp.Place : ((MoveOp)c.Args[i]).Place;
                // As Rust substitutes T: each place T appears in the signature names the same slots of the argument.
                var names = DeclaredType(m, i) is { } declared ? Lifetimes.Expand(declared, _b.TypeOf(argPlace).Type, sig.InputSlots?[i]) : sig.InputSlots?[i];
                if (names is null || slots.Length != names.Length) continue;
                bool invariant = _b.TypeOf(argPlace).Ref == RefMode.Mut;
                for (int k = 0; k < slots.Length; k++)
                {
                    Relate(slots[k], Fresh(names[k]), invariant ? Variance.Invariant : Lifetimes.VarianceOf(_b.TypeOf(argPlace).Type, k), c.Syntax);
                }
            }

            // `Some(var v)` through Deconstruct(out T value): what the callee writes may come from any input.
            if (sig.FilledFromInputs is { } filled)
                foreach (int i in filled)
                {
                    if (i >= c.Args.Count) continue;
                    int target = InnerOf(c.Args[i]);
                    if (target < 0) continue;
                    for (int j = 0; j < c.Args.Count; j++)
                    {
                        if (j == i) continue;
                        Outlives(RegionOf(c.Args[j]), target, c.Syntax);
                        Outlives(InnerOf(c.Args[j]), target, c.Syntax);
                    }
                }

            if (c.Dest is null) return;
            int dest = RegionOf(c.Dest);
            int destInner = c.Dest.IsLocal ? _localInner[c.Dest.Local] : -1;

            var resultNames = SlotsOf(c.Dest) is null ? null
                : m.OriginalDefinition.ReturnType is { } declaredResult ? Lifetimes.Expand(declaredResult, _b.TypeOf(c.Dest).Type, sig.OutputSlots) : sig.OutputSlots;
            if (resultNames is { } outNames && SlotsOf(c.Dest) is { } outSlots && outSlots.Length == outNames.Length)
                for (int k = 0; k < outSlots.Length; k++)
                    // Through a `ref` result the caller may store: invariant, as `&mut T`.
                    Relate(outNames[k] == OwnershipFacts.WholeResult ? (c.Dest.IsLocal && _b.Locals[c.Dest.Local].Type.IsRef ? destInner : dest) : Fresh(outNames[k]),
                        outSlots[k], m.RefKind == RefKind.Ref ? Variance.Invariant : Lifetimes.VarianceOf(_b.TypeOf(c.Dest).Type, k), c.Syntax);

            // A result the callee sees as a type parameter brings no region of its own beyond 'T.
            // Bound slot by slot above, through what T stands for: as Rust, the result has exactly those lifetimes.
            bool pointwise = resultNames is { } rn && rn.Length > 0 && rn.All(x => x.StartsWith("'#T:", StringComparison.Ordinal) && x.Contains('/'));
            if (!pointwise && (sig.OutputHeld ?? sig.Output) is { } outT && outT.StartsWith("'#T:", StringComparison.Ordinal) && SlotsOf(c.Dest) is { } resultSlots)
            {
                bool exact = OwnershipFacts.ContainsInvariance(_b.TypeOf(c.Dest).Type);
                foreach (var slot in resultSlots)
                {
                    Outlives(Fresh(outT), slot, c.Syntax);
                    if (exact) Outlives(slot, Fresh(outT), c.Syntax);
                }
            }

            // A result named after an input's slot (`ref readonly 'a int First(in Pair<'a, 'b> p)`) lives for that slot.
            if (sig.IsSlotName(sig.Output))
            {
                Outlives(Fresh(sig.Output), dest, c.Syntax);
                Outlives(Fresh(sig.Output), destInner, c.Syntax);
            }

            // What comes out of a container (an element, an enumerator, a reference to an element)
            // is usable only while its content lives.
            if (content >= 0)
            {
                Outlives(content, dest, c.Syntax);
                Outlives(content, destInner, c.Syntax);
                if (sig.Output == "'#self") return;
            }

            if (sig.Output == "'#data+")
            {
                int data = c.Args.Count > 0 ? InnerOf(c.Args[0]) : -1;
                if (data < 0 && c.Args.Count > 0) data = RegionOf(c.Args[0]);
                Outlives(data, dest, c.Syntax);
                Outlives(data, destInner, c.Syntax);
                for (int i = 1; i < c.Args.Count && i < sig.Inputs.Length; i++)
                {
                    if (sig.Inputs[i] is null) continue;
                    Outlives(RegionOf(c.Args[i]), dest, c.Syntax);
                    Outlives(InnerOf(c.Args[i]), dest, c.Syntax);
                }
                return;
            }

            if (sig.Output == "'#data")
            {
                int data = c.Args.Count > 0 ? InnerOf(c.Args[0]) : -1;
                if (data < 0 && c.Args.Count > 0) data = RegionOf(c.Args[0]);
                Outlives(data, dest, c.Syntax);
                Outlives(data, destInner, c.Syntax);
                return;
            }

            // A returned reference points at data that lives no longer than the data behind the input.
            if (destInner >= 0 && sig.Output != null)
                for (int i = 0; i < c.Args.Count && i < sig.Inputs.Length; i++)
                    if (sig.Inputs[i] == sig.Output) Outlives(InnerOf(c.Args[i]), destInner, c.Syntax);

            if (dest < 0) return;
            if (sig.Output != null)
            {
                if (sig.Inputs.Contains(sig.Output)) Outlives(Fresh(sig.Output), dest, c.Syntax);
                // An elided result borrows through the reference as well as from the data behind it.
                for (int i = 0; i < c.Args.Count && i < sig.Inputs.Length; i++)
                    if (sig.Inputs[i] == sig.Output && InnerOf(c.Args[i]) >= 0) Outlives(RegionOf(c.Args[i]), dest, c.Syntax);
            }
            else
            {
                foreach (var a in c.Args)
                {
                    Outlives(RegionOf(a), dest, c.Syntax);
                    Outlives(InnerOf(a), dest, c.Syntax);
                }
            }
        }

        private IEnumerable<int> UsedLocals(Statement s)
        {
            switch (s)
            {
                case AssignStmt a:
                    foreach (var (place, _, _) in Reads(a.Value))
                    {
                        if (place.Static is null) yield return place.Local;
                        foreach (var ip in IndexPlaces(place)) if (ip.Static is null) yield return ip.Local;
                    }
                    if (!a.Dest.IsLocal && a.Dest.Static is null) yield return a.Dest.Local;
                    break;
                case DropStmt d:
                    if (d.Place.Static is null && OwnershipFacts.DropUsesBorrows(_b.TypeOf(d.Place).Type)) yield return d.Place.Local;
                    break;
            }
        }

        private static IEnumerable<int> UsedLocals(Terminator t)
        {
            foreach (var op in TermOperands(t))
            {
                if (op is CopyOp c && c.Place.Static is null) yield return c.Place.Local;
                else if (op is MoveOp m && m.Place.Static is null) yield return m.Place.Local;
            }
            if (t is ReturnTerm) yield return 0;
            if (t is CallTerm { Dest: { IsLocal: false, Static: null } d }) yield return d.Local;
        }

        private static int DefinedLocal(Statement s) => s switch
        {
            AssignStmt { Dest: { IsLocal: true } d } => d.Local,
            StorageDeadStmt d => d.Local,
            _ => -1
        };

        private void AddLiveness()
        {
            int n = _b.Locals.Count;
            var liveIn = _blocks.ToDictionary(b => b, _ => new Bits(n));
            bool changed = true;

            void Step(Bits live, Statement s)
            {
                int def = DefinedLocal(s);
                if (def >= 0) live[def] = false;
                foreach (var u in UsedLocals(s)) live[u] = true;
            }

            void StepTerm(Bits live, Terminator t)
            {
                if (t is CallTerm { Dest: { IsLocal: true } d }) live[d.Local] = false;
                foreach (var u in UsedLocals(t)) live[u] = true;
            }

            while (changed)
            {
                changed = false;
                for (int i = _blocks.Count - 1; i >= 0; i--)
                {
                    var b = _blocks[i];
                    var live = new Bits(n);
                    foreach (var s in b.Term.Successors) live.UnionWith(liveIn[s]);
                    StepTerm(live, b.Term);
                    for (int k = b.Statements.Count - 1; k >= 0; k--) Step(live, b.Statements[k]);
                    if (liveIn[b].UnionWith(live)) changed = true;
                }
            }

            // Rust's #[must_not_suspend]: a lock held across an `await` blocks every task that needs it
            // for as long as this one sleeps.
            Dictionary<BasicBlock, Bits> holding = null;
            foreach (var b in _blocks)
            {
                if (b.Term is not SuspendTerm { IsYield: false, Resume: var resume } suspend) continue;
                foreach (int l in liveIn[resume].Ones())
                {
                    var type = _b.Locals[l].Type.Type;
                    if (!OwnershipFacts.HasAttribute(type, "MustNotSuspendAttribute")) continue;

                    // Cleanup paths keep a local "live" before it has a value; it must actually hold one.
                    holding ??= MaybeHolding();
                    if (holding[b][l])
                        Report(ErrorCode.ERR_OwnMustNotSuspend, $"`{type.ToDisplayString()}` must not be held across an `await`", _b.Locals[l].Syntax, "this value lives across a suspension",
                            d =>
                            {
                                d.Secondary.Add((suspend.Syntax.Location, "the task suspends here"));
                                d.Note = "end its scope before the await, or drop it with Mem.Drop";
                            });
                }
            }

            foreach (var b in _blocks)
            {
                var live = new Bits(n);
                foreach (var s in b.Term.Successors) live.UnionWith(liveIn[s]);
                int point = _start[b] + b.Statements.Count;
                // Liveness holds *on entry* to the following point: a point belongs to a region when
                // the local is live just before it runs.
                StepTerm(live, b.Term);
                MarkLive(live, point);
                for (int k = b.Statements.Count - 1; k >= 0; k--)
                {
                    Step(live, b.Statements[k]);
                    MarkLive(live, --point);
                }
            }
        }

        /// <summary>For each block end, the locals that may hold a value there.</summary>
        private Dictionary<BasicBlock, Bits> MaybeHolding()
        {
            int n = _b.Locals.Count;
            var atEnd = _blocks.ToDictionary(b => b, _ => new Bits(n));
            var entry = _blocks.ToDictionary(b => b, _ => new Bits(n));
            var work = new Queue<BasicBlock>(_blocks);
            var queued = new HashSet<BasicBlock>(_blocks);
            while (work.Count > 0)
            {
                var b = work.Dequeue();
                queued.Remove(b);
                var state = entry[b].Clone();
                foreach (var s in b.Statements)
                {
                    if (s is AssignStmt a)
                    {
                        foreach (var op in Operands(a.Value))
                            if (op is MoveOp { Place: { IsLocal: true } m }) state[m.Local] = false;
                        if (a.Dest.IsLocal) state[a.Dest.Local] = true;
                    }
                    else if (s is StorageDeadStmt dead)
                    {
                        state[dead.Local] = false;
                    }
                }
                foreach (var op in TermOperands(b.Term))
                    if (op is MoveOp { Place: { IsLocal: true } m }) state[m.Local] = false;
                atEnd[b] = state.Clone();
                if (b.Term is CallTerm { Dest: { IsLocal: true } d }) state[d.Local] = true;
                foreach (var succ in b.Term.Successors)
                    if (entry[succ].UnionWith(state) && queued.Add(succ)) work.Enqueue(succ);
            }
            return atEnd;
        }

        private void MarkLive(Bits live, int point)
        {
            foreach (int l in live.Ones())
            {
                if (_localRegion[l] >= 0) _regions[_localRegion[l]][point] = true;
                if (_localInner[l] >= 0) _regions[_localInner[l]][point] = true;
            }
        }

        private void Propagate()
        {
            bool changed = true;
            while (changed)
            {
                changed = false;
                foreach (var (sup, sub, _) in _edges)
                    if (_regions[sup].UnionWith(_regions[sub])) changed = true;
            }
        }

        private void CheckUniversal()
        {
            foreach (var (name, region) in _universal)
            {
                foreach (var (otherName, other) in _universal)
                {
                    // 'static outlives every lifetime.
                    if (region == other || _implied.Contains((region, other)) || name == "'static") continue;
                    int bit = _universalRegions.IndexOf(other);
                    if (bit >= 64 || !_regions[region][_points + bit]) continue;
                    var syntax = Blame(region, other) ?? _b.Syntax;
                    string a = Pretty(name), c = Pretty(otherName);
                    Report(ErrorCode.ERR_OwnLifetimeMismatch, $"lifetime may not live long enough: {a} must outlive {c}", syntax,
                        "data flows between these lifetimes here",
                        d => d.Note = "give both references the same named lifetime, for example `ref 'a int`");
                }
            }
        }

        private string Pretty(string lifetime)
        {
            if (!lifetime.StartsWith("'#", StringComparison.Ordinal)) return "`" + lifetime + "`";
            var rest = lifetime.Substring(2);
            if (rest == "this") return "the lifetime of `this`";
            if (rest.StartsWith("T:", StringComparison.Ordinal)) return $"the lifetime of `{rest.Substring(2)}`";
            if (int.TryParse(rest, out int i) && i < _b.Method.ParameterCount)
                return $"the lifetime of `{_b.Method.Parameters[i].Name}`";
            return "an anonymous lifetime";
        }

        private SyntaxNode Blame(int sup, int sub)
        {
            var seen = new HashSet<int> { sub };
            var work = new Queue<int>();
            work.Enqueue(sub);
            while (work.Count > 0)
            {
                int r = work.Dequeue();
                foreach (var (s, t, syntax) in _edges)
                {
                    if (t != r || !seen.Add(s)) continue;
                    if (s == sup) return syntax;
                    work.Enqueue(s);
                }
            }
            return null;
        }

        private void CheckLoans()
        {
            if (_loans.Count == 0) return;
            int n = _loans.Count;
            var entry = _blocks.ToDictionary(b => b, _ => new Bits(n));

            void Prune(Bits state, int point)
            {
                foreach (int l in state.Ones().ToList())
                    if (!_regions[_loans[l].Region][point]) state[l] = false;
            }

            void KillDerefLoans(Bits state, int local)
            {
                foreach (int l in state.Ones().ToList())
                {
                    var p = _loans[l].Place;
                    if (p.Static is null && p.Local == local && p.Projs.Length > 0 && p.Projs[0] is DerefProj && _b.Locals[local].Type.IsRef)
                        state[l] = false;
                }
            }

            void Apply(Bits state, Statement s)
            {
                if (_loanAt.TryGetValue(s, out var loan)) state[loan.Index] = true;
                if (s is AssignStmt { Dest: { IsLocal: true } d }) KillDerefLoans(state, d.Local);
                if (s is StorageDeadStmt dead) KillDerefLoans(state, dead.Local);
            }

            var work = new Queue<BasicBlock>(_blocks);
            var queued = new HashSet<BasicBlock>(_blocks);
            while (work.Count > 0)
            {
                var b = work.Dequeue();
                queued.Remove(b);
                var state = entry[b].Clone();
                int point = _start[b];
                foreach (var s in b.Statements)
                {
                    Prune(state, point);
                    Apply(state, s);
                    point++;
                }
                Prune(state, point);
                foreach (var succ in b.Term.Successors)
                    if (entry[succ].UnionWith(state) && queued.Add(succ)) work.Enqueue(succ);
            }

            foreach (var b in _blocks)
            {
                var state = entry[b].Clone();
                int point = _start[b];
                foreach (var s in b.Statements)
                {
                    Prune(state, point);
                    CheckStatement(state, s, point);
                    Apply(state, s);
                    point++;
                }
                Prune(state, point);
                foreach (var op in TermOperands(b.Term))
                {
                    if (op is CopyOp c) CheckAccess(state, c.Place, Access.Copy, false, point, b.Term.Syntax);
                    else if (op is MoveOp m) CheckAccess(state, m.Place, Access.Move, false, point, b.Term.Syntax);
                }
                if (b.Term is CallTerm { Dest: { } dest }) CheckAccess(state, dest, Access.Assign, true, point, b.Term.Syntax);
            }
        }

        private void CheckStatement(Bits state, Statement s, int point)
        {
            switch (s)
            {
                case AssignStmt a:
                    foreach (var (place, access, shallow) in Reads(a.Value))
                        CheckAccess(state, place, access, shallow, point, a.Syntax);
                    CheckAccess(state, a.Dest, Access.Assign, true, point, a.Syntax);
                    break;
                case DropStmt { ForAssign: false } d:
                    CheckAccess(state, d.Place, Access.Drop, false, point, d.Syntax);
                    break;
                case StorageDeadStmt d:
                    CheckAccess(state, new Place(d.Local), Access.StorageDead, true, point, d.Syntax);
                    break;
            }
        }

        private bool Conflicts(Loan loan, Place access, bool shallow)
        {
            var lp = loan.Place;
            if (access.Static is not null || lp.Local != access.Local) return false;

            var t = BaseType(lp);
            int common = Math.Min(lp.Projs.Length, access.Projs.Length);
            for (int i = 0; i < common; i++)
            {
                var a = lp.Projs[i];
                var c = access.Projs[i];
                if (a is FieldProj fa && c is FieldProj fc && !Equals(fa.Field.OriginalDefinition, fc.Field.OriginalDefinition))
                    return false;
                if (a.GetType() != c.GetType()) return true;
                t = MirBody.Project(t, a);
            }

            // The access reaches a prefix of the loan: what lies behind a reference is unaffected by
            // writing the reference itself, and shared data stays valid even if its reference goes away.
            for (int i = common; i < lp.Projs.Length; i++)
            {
                var proj = lp.Projs[i];
                if (proj is DerefProj)
                {
                    if (t.Ref == RefMode.Shared) return false;
                    if (t.IsRef && shallow) return false;
                    if (!t.IsRef && t.Type is PointerTypeSymbol) return false;
                }
                t = MirBody.Project(t, proj);
            }
            return true;
        }

        private void CheckAccess(Bits state, Place place, Access access, bool shallow, int point, SyntaxNode syntax)
        {
            bool isRead = access is Access.Copy or Access.BorrowShared;
            foreach (int l in state.Ones())
            {
                var loan = _loans[l];
                if (isRead && loan.Mode == RefMode.Shared) continue;
                if (!Conflicts(loan, place, shallow)) continue;
                ReportConflict(loan, place, access, point, syntax);
            }
        }

        private void ReportConflict(Loan loan, Place place, Access access, int point, SyntaxNode syntax)
        {
            string name = _b.Describe(place);
            string borrowed = _b.Describe(loan.Place);
            void Common(OwnershipDiagnostic d, string first)
            {
                d.Secondary.Add((loan.Syntax.Location, first));
                if (LaterUse(loan, point) is { } use) d.Secondary.Add((use.Location, "borrow later used here"));
            }

            string kindLabel = loan.Mode == RefMode.Mut ? "mutable borrow occurs here" : "immutable borrow occurs here";
            switch (access)
            {
                case Access.Copy:
                    Report(ErrorCode.ERR_OwnUseWhileMutBorrowed, $"cannot use `{name}` because it is mutably borrowed", syntax, "use of borrowed value", d => Common(d, $"`{borrowed}` is borrowed here"));
                    break;
                case Access.Move:
                    Report(ErrorCode.ERR_OwnMoveWhileBorrowed, $"cannot move out of `{name}` because it is borrowed", syntax, "move out of borrowed value", d => Common(d, $"`{borrowed}` is borrowed here"));
                    break;
                case Access.Assign:
                    Report(ErrorCode.ERR_OwnAssignToBorrowed, $"cannot assign to `{name}` because it is borrowed", syntax, "assignment to borrowed value", d => Common(d, $"`{borrowed}` is borrowed here"));
                    break;
                case Access.BorrowShared:
                    Report(ErrorCode.ERR_OwnSharedBorrowWhileMut, $"cannot borrow `{name}` as immutable because it is also borrowed as mutable", syntax, "immutable borrow occurs here", d => Common(d, kindLabel));
                    break;
                case Access.BorrowMut when loan.Mode == RefMode.Shared:
                    Report(ErrorCode.ERR_OwnMutBorrowWhileShared, $"cannot borrow `{name}` as mutable because it is also borrowed as immutable", syntax, "mutable borrow occurs here", d => Common(d, kindLabel));
                    break;
                case Access.BorrowMut:
                    Report(ErrorCode.ERR_OwnDoubleMutBorrow, $"cannot borrow `{name}` as mutable more than once at a time", syntax, "second mutable borrow occurs here", d => Common(d, "first mutable borrow occurs here"));
                    break;
                default:
                {
                    var local = place.Static is null ? _b.Locals[place.Local] : null;
                    if (local != null && MirBody.IsClosureEnvironment(local.Type.Type))
                    {
                        Report(ErrorCode.ERR_OwnClosureOutlives, $"closure may outlive the current function, but it borrows `{borrowed}`", loan.Syntax, "this closure borrows its environment",
                            d => d.Note = "use a `move` lambda to give the closure ownership of what it captures");
                        break;
                    }

                    bool escapes = _universalRegions.Any(u => _regions[loan.Region][_points + Math.Min(_universalRegions.IndexOf(u), 63)]);
                    if (escapes)
                    {
                        Report(ErrorCode.ERR_OwnReturnRefToLocal, $"cannot return a reference to local `{name}`", loan.Syntax, "this borrow outlives the function", d => d.Note = $"`{name}` is dropped when the function returns");
                    }
                    else if (local?.Kind == LocalKind.Temp)
                    {
                        Report(ErrorCode.ERR_OwnTemporaryDropped, "temporary value dropped while borrowed", loan.Syntax, "this temporary is freed at the end of the statement", d =>
                        {
                            if (LaterUse(loan, point) is { } use) d.Secondary.Add((use.Location, "borrow later used here"));
                        });
                    }
                    else
                    {
                        Report(ErrorCode.ERR_OwnDoesNotLiveLongEnough, $"`{name}` does not live long enough", loan.Syntax, "borrowed value does not live long enough", d =>
                        {
                            d.Secondary.Add((syntax.Location, $"`{name}` is dropped here while still borrowed"));
                            if (LaterUse(loan, point) is { } use) d.Secondary.Add((use.Location, "borrow later used here"));
                        });
                    }
                    break;
                }
            }
        }

        /// <summary>Finds a use of a local fed by the loan, walking forward inside the loan's region.</summary>
        private SyntaxNode LaterUse(Loan loan, int fromPoint)
        {
            var carriers = new HashSet<int> { loan.Region };
            var work = new Queue<int>();
            work.Enqueue(loan.Region);
            while (work.Count > 0)
            {
                int r = work.Dequeue();
                foreach (var (sup, sub, _) in _edges)
                    if (sup == r && carriers.Add(sub)) work.Enqueue(sub);
            }

            bool Carries(int local) => local >= 0 && _localRegion[local] >= 0 && carriers.Contains(_localRegion[local]) && _b.Locals[local].Kind != LocalKind.Temp;

            var seen = new HashSet<BasicBlock>();
            var queue = new Queue<(BasicBlock Block, int Index)>();
            foreach (var b in _blocks)
            {
                int start = _start[b];
                if (fromPoint >= start && fromPoint <= start + b.Statements.Count)
                {
                    queue.Enqueue((b, fromPoint - start + 1));
                    break;
                }
            }

            while (queue.Count > 0)
            {
                var (b, index) = queue.Dequeue();
                for (int i = index; i < b.Statements.Count; i++)
                {
                    var s = b.Statements[i];
                    if (s is not (AssignStmt or DropStmt)) continue;
                    if (UsedLocals(s).Any(Carries)) return s.Syntax;
                }
                if (index <= b.Statements.Count && UsedLocals(b.Term).Any(Carries)) return b.Term.Syntax;
                foreach (var succ in b.Term.Successors)
                    if (seen.Add(succ)) queue.Enqueue((succ, 0));
            }

            // Temporaries carry the use when no named local does, as in `F(ref a, ref a)`.
            foreach (var b in _blocks)
                if (b.Term is CallTerm c && c.Args.Any(a => RegionOf(a) is var r and >= 0 && carriers.Contains(r)) && _start[b] + b.Statements.Count >= fromPoint)
                    return c.Syntax;
            return null;
        }
    }
}
