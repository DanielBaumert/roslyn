// RustSharp: lowers Roslyn's fully rewritten bound tree into MIR. Decides, for every read, whether it is
// a copy, a move or a borrow, and schedules drops per scope, including the cleanup path of every call.

using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.CodeAnalysis.CSharp.Symbols;

namespace Microsoft.CodeAnalysis.CSharp.Ownership
{
    internal sealed class OwnershipDiagnostic
    {
        public ErrorCode Code;
        public string Message;
        public Location Location;
        public string Label;
        public List<(Location Location, string Text)> Secondary = new List<(Location, string)>();
        public string Note;
    }

    internal sealed class MirBuilder
    {
        private sealed class Scope
        {
            public BoundNode Owner;
            public List<int> Locals = new List<int>();
            public BoundBlock Finally;
            public BasicBlock CatchEntry;

            public BasicBlock CachedUnwind;
            public BasicBlock CachedNext;
            public int CachedCount = -1;
        }

        private sealed class LabelOwnerWalker : BoundTreeWalkerWithStackGuard
        {
            public readonly Dictionary<LabelSymbol, BoundNode> Owners = new Dictionary<LabelSymbol, BoundNode>();
            private BoundNode _owner;

            public LabelOwnerWalker(BoundNode root) => _owner = root;

            public override BoundNode VisitBlock(BoundBlock node)
            {
                var saved = _owner;
                _owner = node;
                base.VisitBlock(node);
                _owner = saved;
                return null;
            }

            public override BoundNode VisitScope(BoundScope node)
            {
                var saved = _owner;
                _owner = node;
                base.VisitScope(node);
                _owner = saved;
                return null;
            }

            public override BoundNode VisitLabelStatement(BoundLabelStatement node)
            {
                Owners[node.Label] = _owner;
                return base.VisitLabelStatement(node);
            }
        }

        private readonly MethodSymbol _method;
        private readonly BoundStatement _root;
        private readonly CSharpCompilation _compilation;
        private readonly List<OwnershipDiagnostic> _diagnostics;
        private readonly MirBody _b = new MirBody();
        private readonly Dictionary<Symbol, int> _vars = new Dictionary<Symbol, int>();
        private readonly HashSet<int> _aliases = new HashSet<int>();
        private readonly Dictionary<LabelSymbol, BasicBlock> _labels = new Dictionary<LabelSymbol, BasicBlock>();
        private readonly Dictionary<int, Place> _conditionalReceivers = new Dictionary<int, Place>();
        private readonly Stack<Place> _caught = new Stack<Place>();
        private Dictionary<LabelSymbol, BoundNode> _labelOwners;
        private List<Scope> _scopes = new List<Scope>();
        private BasicBlock _cur, _returnBlock, _resumeBlock;
        private int _this = -1;

        private readonly System.Func<MethodSymbol, MirBody> _lookup;
        private readonly Dictionary<FieldSymbol, Place> _links = new Dictionary<FieldSymbol, Place>(Symbols.SymbolEqualityComparer.AllIgnoreOptions);

        private MirBuilder(MethodSymbol method, BoundStatement body, CSharpCompilation compilation, List<OwnershipDiagnostic> diagnostics, System.Func<MethodSymbol, MirBody> lookup)
        {
            _lookup = lookup;
            _method = method;
            _root = body;
            _compilation = compilation;
            _diagnostics = diagnostics;
        }

        public static MirBody Build(MethodSymbol method, BoundStatement body, CSharpCompilation compilation, List<OwnershipDiagnostic> diagnostics, System.Func<MethodSymbol, MirBody> lookup)
            => new MirBuilder(method, body, compilation, diagnostics, lookup).Run();

        private MirBody Run()
        {
            _b.Method = _method;
            _b.Syntax = _root.Syntax;
            var walker = new LabelOwnerWalker(_root);
            walker.Visit(_root);
            _labelOwners = walker.Owners;

            bool coroutine = OwnershipFacts.IsCoroutine(_method);
            AddLocal(coroutine ? new MirType(OwnershipFacts.CoroutineResult(_method, _compilation)) : new MirType(_method.ReturnType, OwnershipFacts.ReturnMode(_method)),
                LocalKind.Return, "<return>", _root.Syntax);

            _cur = NewBlock();
            _returnBlock = NewBlock();
            _returnBlock.Term = new ReturnTerm { Syntax = _root.Syntax };
            _resumeBlock = NewBlock();
            _resumeBlock.IsCleanup = true;
            _resumeBlock.Term = new ResumeTerm { Syntax = _root.Syntax };

            _scopes.Add(new Scope { Owner = _root });
            var rootScope = _scopes[0];

            if (!_method.IsStatic)
            {
                var mode = OwnershipFacts.GetThisMode(_method);
                var type = _method.ContainingType;
                var refMode = mode == ThisMode.Shared ? RefMode.Shared : mode == ThisMode.Mut ? RefMode.Mut : RefMode.None;
                _this = AddLocal(new MirType(type, refMode, contents: refMode != RefMode.None && !type.IsValueType), LocalKind.Arg, "this", _root.Syntax);
                rootScope.Locals.Add(_this);
            }

            foreach (var p in _method.Parameters)
            {
                int l = AddLocal(new MirType(p.Type, OwnershipFacts.ParamMode(p)), LocalKind.Arg, p.Name, _root.Syntax);
                if (p.GetNonNullSyntaxNode() is Syntax.ParameterSyntax parameter) MarkMutability(l, parameter);
                _vars[p] = l;
                rootScope.Locals.Add(l);
            }
            _b.ArgCount = _b.Locals.Count - 1;

            _b.ExceptionSlot = AddLocal(new MirType(_compilation.GetSpecialType(SpecialType.System_Object)), LocalKind.ExceptionSlot, "<exception>", _root.Syntax);
            if (_method.IsIterator)
                _b.YieldSlot = AddLocal(new MirType(_method.IteratorElementTypeWithAnnotations.Type), LocalKind.Temp, "<yield>", _root.Syntax);

            Stmt(_root);
            ExitTo(0, _root.Syntax);
            Terminate(new GotoTerm { Target = _returnBlock, Syntax = _root.Syntax });
            foreach (var b in _b.Blocks)
            {
                b.Term ??= new UnreachableTerm { Syntax = _root.Syntax };

                // Cleanup blocks can predate a temporary turning into a borrow; a borrow is never dropped.
                b.Statements.RemoveAll(s => s is DropStmt { Place: { IsLocal: true } p } && _b.Locals[p.Local].Type.IsRef);
            }
            return _b;
        }

        // ---- infrastructure

        private int AddLocal(MirType type, LocalKind kind, string name, SyntaxNode syntax)
        {
            var l = new MirLocal { Index = _b.Locals.Count, Type = type, Kind = kind, Name = name, Syntax = syntax };
            _b.Locals.Add(l);
            return l.Index;
        }

        private BasicBlock NewBlock()
        {
            var b = new BasicBlock { Index = _b.Blocks.Count };
            _b.Blocks.Add(b);
            return b;
        }

        private void Terminate(Terminator t)
        {
            _cur.Term ??= t;
            _cur = NewBlock();
        }

        private void Goto(BasicBlock target, SyntaxNode syntax)
        {
            _cur.Term ??= new GotoTerm { Target = target, Syntax = syntax };
            _cur = target;
        }

        private void Emit(Statement s)
        {
            _cur.Statements.Add(s);
            if (_cur.IsCleanup || !CanFault(s)) return;

            // A faulting statement ends its block, so its unwind path is a real CFG edge.
            var unwind = Unwind();
            var next = NewBlock();
            _cur.Term = new FaultEdgeTerm { Target = next, Unwind = unwind, Syntax = s.Syntax };
            _cur = next;
        }

        private bool PlaceFaults(Place p)
        {
            var t = p.Static is null ? _b.Locals[p.Local].Type : new MirType(p.Static.Type);
            foreach (var proj in p.Projs)
            {
                if (proj is IndexProj) return true;
                if (proj is DerefProj && !t.IsRef && t.Type is not PointerTypeSymbol) return true;
                t = MirBody.Project(t, proj);
            }
            return false;
        }

        private bool OperandFaults(Operand op) => op switch
        {
            CopyOp c => PlaceFaults(c.Place),
            MoveOp m => PlaceFaults(m.Place),
            _ => false
        };

        private bool CanFault(Statement statement)
        {
            switch (statement)
            {
                case DropStmt d:
                    return PlaceFaults(d.Place);
                case AssignStmt a when PlaceFaults(a.Dest):
                    return true;
                case AssignStmt { Value: var v }:
                    switch (v)
                    {
                        case UseRv u: return OperandFaults(u.Op);
                        case RefRv { CastTo: null } r: return PlaceFaults(r.Place);
                        case AddrOfRv r: return PlaceFaults(r.Place);
                        case RetainRv r: return PlaceFaults(r.Place);
                        case ArrayLenRv r: return PlaceFaults(r.Array);
                        case ArrayDimRv r: return PlaceFaults(r.Array);
                        case IsInstRv r: return PlaceFaults(r.Place);
                        case IsNullRv r: return PlaceFaults(r.Place);
                        case NewArrayRv or UnboxRv or PeekBoxRv: return true;
                        case RefCastRv c: return c.Checked || OperandFaults(c.Value);
                        case ConvertRv c: return c.Checked || OperandFaults(c.Value);
                        case UnaryRv u: return (u.Op & UnaryOperatorKind.Checked) != 0 || OperandFaults(u.Value);
                        case BinaryRv b:
                            return (b.Op & BinaryOperatorKind.Checked) != 0
                                || b.Op.Operator() is BinaryOperatorKind.Division or BinaryOperatorKind.Remainder
                                || OperandFaults(b.Left) || OperandFaults(b.Right);
                        default: return false;
                    }
                default:
                    return false;
            }
        }

        private void Assign(Place dest, Rvalue value, SyntaxNode syntax)
            => Emit(new AssignStmt { Dest = dest, Value = value, Syntax = syntax });

        private Place Temp(MirType type, SyntaxNode syntax)
        {
            int l = AddLocal(type, LocalKind.Temp, null, syntax);
            _scopes[^1].Locals.Add(l);
            return new Place(l);
        }

        private Place Temp(TypeSymbol type, SyntaxNode syntax) => Temp(new MirType(type), syntax);

        private Operand ToTemp(Operand op, TypeSymbol type, SyntaxNode syntax)
        {
            if (op is ConstOp) return op;
            var t = Temp(type, syntax);
            Assign(t, new UseRv { Op = op }, syntax);
            return Read(t);
        }

        private Operand Unsupported(SyntaxNode syntax, string what)
        {
            _diagnostics.Add(new OwnershipDiagnostic
            {
                Code = ErrorCode.ERR_OwnOwnershipUnsupported,
                Message = "not supported in ownership mode: " + what,
                Location = (syntax ?? _root.Syntax).Location,
                Label = "unsupported here"
            });
            return new ConstOp { Value = ConstantValue.Null };
        }

        /// <summary>Reading a place yields a copy, a retained string, or a move, depending on the type.</summary>
        private Operand Read(Place p)
        {
            var t = _b.TypeOf(p);
            if (t.Ref == RefMode.Shared && !t.Contents) return new CopyOp { Place = p };
            if (t.IsRef) return new MoveOp { Place = p };
            if (OwnershipFacts.IsCopy(t.Type)) return new CopyOp { Place = p };
            return new MoveOp { Place = p };
        }

        /// <summary>
        /// Rust's String: in user code a string moves like any owned value; the corelib still shares
        /// strings by reference count inside. Reading one without moving it is <see cref="Share"/>.
        /// </summary>
        private bool StrictStrings => _strictStrings ??= _root.Syntax?.SyntaxTree is { } tree && IsUserTree?.Invoke(tree) == true;
        private bool? _strictStrings;

        private Operand Share(Place p, SyntaxNode syntax)
        {
            int l = AddLocal(new MirType(_b.TypeOf(p).Type), LocalKind.Temp, null, syntax);
            _scopes[^1].Locals.Add(l);
            Assign(new Place(l), new RetainRv { Place = p }, syntax);
            return new MoveOp { Place = new Place(l) };
        }

        private Operand ReadValue(Place p, SyntaxNode syntax)
        {
            var t = _b.TypeOf(p);
            if ((!t.IsRef || t.Contents) && OwnershipFacts.IsString(t.Type) && StrictStrings && !t.IsRef && p.Projs.Length == 0 && _b.Locals[p.Local].Kind != LocalKind.Temp)
                return Read(p);
            if ((!t.IsRef || t.Contents) && OwnershipFacts.IsString(t.Type))
            {
                int l = AddLocal(new MirType(t.Type), LocalKind.Temp, null, syntax);
                _scopes[^1].Locals.Add(l);
                Assign(new Place(l), new RetainRv { Place = p }, syntax);
                return new MoveOp { Place = new Place(l) };
            }
            return Read(p);
        }

        // ---- scopes

        private Scope PushScope(BoundNode owner = null)
        {
            var s = new Scope { Owner = owner };
            _scopes.Add(s);
            return s;
        }

        private void EmitScopeExit(Scope s, SyntaxNode syntax)
        {
            for (int i = s.Locals.Count - 1; i >= 0; i--)
            {
                int l = s.Locals[i];
                var type = _b.Locals[l].Type;
                if (!type.IsRef && OwnershipFacts.NeedsDrop(type.Type))
                    Emit(new DropStmt { Place = new Place(l), Syntax = syntax });
                Emit(new StorageDeadStmt { Local = l, Syntax = syntax });
            }
        }

        private void PopScope(SyntaxNode syntax)
        {
            var s = _scopes[^1];
            EmitScopeExit(s, syntax);
            _scopes.RemoveAt(_scopes.Count - 1);
        }

        /// <summary>Leaves every scope at index >= depth, running drops and inlining finally blocks.</summary>
        private void ExitTo(int depth, SyntaxNode syntax)
        {
            var saved = _scopes;
            for (int i = saved.Count - 1; i >= depth; i--)
            {
                _scopes = saved.GetRange(0, i + 1);
                var s = saved[i];
                EmitScopeExit(s, syntax);
                if (s.Finally != null)
                {
                    _scopes = saved.GetRange(0, i);
                    BuildFinally(s.Finally);
                }
            }
            _scopes = saved;
        }

        private void BuildFinally(BoundBlock block)
        {
            ForgetLabels(block);
            Stmt(block);
        }

        private void ForgetLabels(BoundNode node)
        {
            var w = new LabelOwnerWalker(node);
            w.Visit(node);
            foreach (var l in w.Owners.Keys) _labels.Remove(l);
        }

        private BasicBlock UnwindFrom(int index)
        {
            if (index < 0) return _resumeBlock;
            var s = _scopes[index];
            var next = UnwindFrom(index - 1);
            if (s.CachedUnwind != null && s.CachedNext == next && s.CachedCount == s.Locals.Count)
                return s.CachedUnwind;

            var target = next;
            if (s.CatchEntry != null) target = s.CatchEntry;
            else if (s.Finally != null) target = BuildCleanupFinally(s, index, next);

            for (int i = 0; i < s.Locals.Count; i++)
            {
                int l = s.Locals[i];
                var type = _b.Locals[l].Type;
                if (type.IsRef || !OwnershipFacts.NeedsDrop(type.Type)) continue;
                var block = NewBlock();
                block.IsCleanup = true;
                block.Statements.Add(new DropStmt { Place = new Place(l), Syntax = _b.Locals[l].Syntax });
                block.Term = new GotoTerm { Target = target, Syntax = _b.Locals[l].Syntax };
                target = block;
            }

            s.CachedUnwind = target;
            s.CachedNext = next;
            s.CachedCount = s.Locals.Count;
            return target;
        }

        /// <summary>The finally body on the exceptional path; the in-flight exception is parked around it.</summary>
        private BasicBlock BuildCleanupFinally(Scope s, int index, BasicBlock next)
        {
            var savedCur = _cur;
            var savedScopes = _scopes;
            _scopes = savedScopes.GetRange(0, index);
            var entry = NewBlock();
            entry.IsCleanup = true;
            _cur = entry;

            var syntax = s.Finally.Syntax;
            var slot = new Place(_b.ExceptionSlot);
            int parked = AddLocal(_b.Locals[_b.ExceptionSlot].Type, LocalKind.Temp, null, syntax);
            Assign(new Place(parked), new UseRv { Op = new MoveOp { Place = slot } }, syntax);
            BuildFinally(s.Finally);
            Assign(slot, new UseRv { Op = new MoveOp { Place = new Place(parked) } }, syntax);
            _cur.Term ??= new GotoTerm { Target = next, Syntax = syntax };

            _cur = savedCur;
            _scopes = savedScopes;
            return entry;
        }

        private BasicBlock Unwind() => UnwindFrom(_scopes.Count - 1);

        // ---- statements

        private void Stmt(BoundStatement s)
        {
            switch (s)
            {
                case null:
                case BoundNoOpStatement:
                case BoundSavePreviousSequencePoint:
                case BoundRestorePreviousSequencePoint:
                case BoundStepThroughSequencePoint:
                case BoundSequencePoint { StatementOpt: null }:
                    break;
                case BoundSequencePoint sp:
                    Stmt(sp.StatementOpt);
                    break;
                case BoundSequencePointWithSpan sp:
                    Stmt(sp.StatementOpt);
                    break;
                case BoundBlock b:
                    PushScope(b);
                    Declare(b.Locals, b.Syntax);
                    foreach (var x in b.Statements) Stmt(x);
                    PopScope(b.Syntax);
                    break;
                case BoundScope b:
                    PushScope(b);
                    Declare(b.Locals, b.Syntax);
                    foreach (var x in b.Statements) Stmt(x);
                    PopScope(b.Syntax);
                    break;
                case BoundStatementList l:
                    foreach (var x in l.Statements) Stmt(x);
                    break;
                case BoundExpressionStatement e:
                    PushScope();
                    Effect(e.Expression);
                    PopScope(e.Syntax);
                    break;
                case BoundReturnStatement r:
                    Return(r);
                    break;
                case BoundGotoStatement g:
                    ExitTo(LabelDepth(g.Label), g.Syntax);
                    Terminate(new GotoTerm { Target = LabelBlock(g.Label), Syntax = g.Syntax });
                    break;
                case BoundLabelStatement l:
                    Goto(LabelBlock(l.Label), l.Syntax);
                    break;
                case BoundConditionalGoto g:
                    ConditionalGoto(g);
                    break;
                case BoundSwitchDispatch d:
                    SwitchDispatch(d);
                    break;
                case BoundThrowStatement t:
                    Throw(t.ExpressionOpt, t.Syntax);
                    break;
                case BoundTryStatement t:
                    Try(t);
                    break;
                case BoundYieldReturnStatement y:
                {
                    PushScope();
                    Assign(new Place(_b.YieldSlot), new UseRv { Op = Rv(y.Expression) }, y.Syntax);
                    PopScope(y.Syntax);
                    var resume = NewBlock();
                    _cur.Term ??= new SuspendTerm { Resume = resume, IsYield = true, Syntax = y.Syntax };
                    _cur = resume;
                    break;
                }
                case BoundYieldBreakStatement y:
                    ExitTo(0, y.Syntax);
                    Terminate(new GotoTerm { Target = _returnBlock, Syntax = y.Syntax });
                    break;
                default:
                    Unsupported(s.Syntax, "statement " + s.Kind);
                    break;
            }
        }

        private void Declare(ImmutableArray<LocalSymbol> locals, SyntaxNode syntax)
        {
            foreach (var l in locals)
            {
                if (_vars.TryGetValue(l, out int existing))
                {
                    _scopes[^1].Locals.Add(existing);
                    continue;
                }
                var mode = l.RefKind == RefKind.None ? RefMode.None : l.RefKind == RefKind.RefReadOnly ? RefMode.Shared : RefMode.Mut;
                bool named = !string.IsNullOrEmpty(l.Name) && !l.IsCompilerGenerated;
                int index = AddLocal(new MirType(l.Type, mode), named ? LocalKind.User : LocalKind.Temp, named ? l.Name : null, named ? l.GetDeclaratorSyntax() : syntax);
                _vars[l] = index;
                _scopes[^1].Locals.Add(index);
                if (named) MarkMutability(index, l.GetDeclaratorSyntax());
            }
        }

        private void MarkMutability(int index, SyntaxNode declarator)
        {
            if (declarator is null) return;
            var local = _b.Locals[index];
            local.Immutable = !MutabilityChecker.HasMut(declarator, out local.MutSite) && local.MutSite != default;
        }

        private int LabelDepth(LabelSymbol label)
        {
            if (_labelOwners.TryGetValue(label, out var owner))
            {
                for (int i = _scopes.Count - 1; i >= 0; i--)
                    if (ReferenceEquals(_scopes[i].Owner, owner)) return i + 1;
            }
            return _scopes.Count;
        }

        private BasicBlock LabelBlock(LabelSymbol label)
        {
            if (!_labels.TryGetValue(label, out var b))
                _labels[label] = b = NewBlock();
            return b;
        }

        private void Return(BoundReturnStatement r)
        {
            PushScope();
            var ret = new Place(0);
            if (r.ExpressionOpt != null)
            {
                if (_method.RefKind != RefKind.None)
                    Assign(ret, new RefRv { Mode = OwnershipFacts.ReturnMode(_method), Place = Pl(r.ExpressionOpt) }, r.ExpressionOpt.Syntax);
                else
                    Assign(ret, new UseRv { Op = Rv(r.ExpressionOpt) }, r.ExpressionOpt.Syntax);
            }
            ExitTo(0, r.Syntax);
            _scopes.RemoveAt(_scopes.Count - 1);
            Terminate(new GotoTerm { Target = _returnBlock, Syntax = r.Syntax });
        }

        private void ConditionalGoto(BoundConditionalGoto g)
        {
            PushScope();
            var cond = ToTemp(Rv(g.Condition), g.Condition.Type, g.Syntax);
            PopScope(g.Syntax);

            var jump = NewBlock();
            var fall = NewBlock();
            _cur.Term ??= new BranchTerm
            {
                Cond = cond,
                IfTrue = g.JumpIfTrue ? jump : fall,
                IfFalse = g.JumpIfTrue ? fall : jump,
                Syntax = g.Syntax
            };
            _cur = jump;
            ExitTo(LabelDepth(g.Label), g.Syntax);
            _cur.Term ??= new GotoTerm { Target = LabelBlock(g.Label), Syntax = g.Syntax };
            _cur = fall;
        }

        private void SwitchDispatch(BoundSwitchDispatch d)
        {
            if (OwnershipFacts.IsString(d.Expression.Type))
            {
                StringSwitch(d);
                return;
            }
            PushScope();
            var value = ToTemp(Rv(d.Expression), d.Expression.Type, d.Syntax);
            PopScope(d.Syntax);
            var term = new SwitchTerm { Value = value, Type = d.Expression.Type, Default = LabelBlock(d.DefaultLabel), Syntax = d.Syntax };
            foreach (var (v, label) in d.Cases) term.Cases.Add((v, LabelBlock(label)));
            Terminate(term);
        }

        /// <summary>A string dispatch becomes a chain of equality tests.</summary>
        private void StringSwitch(BoundSwitchDispatch d)
        {
            var equals = (MethodSymbol)_compilation.GetSpecialTypeMember(SpecialMember.System_String__op_Equality);
            var type = d.Expression.Type;
            var boolean = _compilation.GetSpecialType(SpecialType.System_Boolean);
            var value = Pl(d.Expression);
            foreach (var (constant, label) in d.Cases)
            {
                PushScope();
                var flag = Temp(boolean, d.Syntax);
                var call = new CallTerm { Dest = flag, Method = equals, Target = NewBlock(), Unwind = Unwind(), Syntax = d.Syntax };
                call.Args.Add(Share(value, d.Syntax));
                call.Args.Add(new ConstOp { Value = constant, Type = type });
                _cur.Term ??= call;
                _cur = call.Target;
                var cond = Read(flag);
                PopScope(d.Syntax);
                var next = NewBlock();
                _cur.Term ??= new BranchTerm { Cond = cond, IfTrue = LabelBlock(label), IfFalse = next, Syntax = d.Syntax };
                _cur = next;
            }
            Terminate(new GotoTerm { Target = LabelBlock(d.DefaultLabel), Syntax = d.Syntax });
        }

        private void Throw(BoundExpression value, SyntaxNode syntax)
        {
            Operand op;
            if (value != null)
            {
                op = Rv(value);
            }
            else if (_caught.Count > 0)
            {
                op = new MoveOp { Place = _caught.Peek() };
            }
            else
            {
                op = Unsupported(syntax, "`throw;` outside a catch block");
            }
            Terminate(new ThrowTerm { Value = op, Unwind = Unwind(), Syntax = syntax });
        }

        private void Try(BoundTryStatement t)
        {
            var after = NewBlock();
            Scope finallyScope = null;
            if (t.FinallyBlockOpt != null)
            {
                finallyScope = PushScope();
                finallyScope.Finally = t.FinallyBlockOpt;
            }

            if (t.CatchBlocks.IsEmpty)
            {
                Stmt(t.TryBlock);
            }
            else
            {
                var dispatch = NewBlock();
                dispatch.IsCleanup = true;
                var catchScope = PushScope();
                catchScope.CatchEntry = dispatch;
                Stmt(t.TryBlock);
                _scopes.RemoveAt(_scopes.Count - 1);
                var afterCatch = NewBlock();
                Goto(afterCatch, t.Syntax);

                _cur = dispatch;
                var slot = new Place(_b.ExceptionSlot);
                foreach (var c in t.CatchBlocks)
                {
                    var handler = NewBlock();
                    var next = NewBlock();
                    if (c.ExceptionTypeOpt is { } type && type.SpecialType != SpecialType.System_Object)
                    {
                        var test = Temp(_compilation.GetSpecialType(SpecialType.System_Boolean), t.Syntax);
                        Assign(test, new IsInstRv { Place = slot, Target = type }, t.Syntax);
                        _cur.Term = new BranchTerm { Cond = Read(test), IfTrue = handler, IfFalse = next, Syntax = t.Syntax };
                    }
                    else
                    {
                        _cur.Term = new GotoTerm { Target = handler, Syntax = t.Syntax };
                    }

                    _cur = handler;
                    PushScope(c);
                    Declare(c.Locals, c.Syntax);
                    Place caught;
                    if (c.ExceptionSourceOpt != null)
                    {
                        caught = Pl(c.ExceptionSourceOpt);
                        Assign(caught, new RefCastRv { Value = new MoveOp { Place = slot }, To = c.ExceptionSourceOpt.Type }, c.Syntax);
                    }
                    else
                    {
                        caught = Temp(_b.Locals[_b.ExceptionSlot].Type, c.Syntax);
                        Assign(caught, new UseRv { Op = new MoveOp { Place = slot } }, c.Syntax);
                    }
                    if (c.ExceptionFilterPrologueOpt != null) Stmt(c.ExceptionFilterPrologueOpt);
                    if (c.ExceptionFilterOpt != null)
                    {
                        // The handler owns the exception while its filter runs. A rejecting filter hands
                        // it back, so a filter that consumed it fails the move check here.
                        var accepted = ToTemp(Rv(c.ExceptionFilterOpt), c.ExceptionFilterOpt.Type, c.Syntax);
                        var body = NewBlock();
                        var rejected = NewBlock();
                        _cur.Term ??= new BranchTerm { Cond = accepted, IfTrue = body, IfFalse = rejected, Syntax = c.Syntax };
                        _cur = rejected;
                        Assign(slot, new UseRv { Op = new MoveOp { Place = caught } }, c.Syntax);
                        EmitScopeExit(_scopes[^1], c.Syntax);
                        _cur.Term ??= new GotoTerm { Target = next, Syntax = c.Syntax };
                        _cur = body;
                    }

                    _caught.Push(caught);
                    Stmt(c.Body);
                    _caught.Pop();
                    PopScope(c.Syntax);
                    _cur.Term ??= new GotoTerm { Target = afterCatch, Syntax = c.Syntax };
                    _cur = next;
                }

                _cur.Term ??= new GotoTerm { Target = UnwindFrom(_scopes.Count - 1), Syntax = t.Syntax };
                _cur = afterCatch;
            }

            if (finallyScope != null)
            {
                _scopes.RemoveAt(_scopes.Count - 1);
                BuildFinally(t.FinallyBlockOpt);
            }

            Goto(after, t.Syntax);
        }

        // ---- expressions

        private void Effect(BoundExpression e)
        {
            switch (e)
            {
                case BoundAssignmentOperator a:
                    Assignment(a);
                    return;
                case BoundCall c when IsAnonymousGetter(c):
                    return;
                case BoundCall c:
                    Call(c);
                    return;
                case BoundSequence s:
                    Declare(s.Locals, s.Syntax);
                    foreach (var x in s.SideEffects) Effect(x);
                    Effect(s.Value);
                    return;
                case BoundConditionalOperator c when c.Type is null || c.Type.IsVoidType():
                    Conditional(c, null);
                    return;
                case BoundLoweredConditionalAccess a:
                    ConditionalAccess(a, wantValue: false);
                    return;
                case BoundSequencePointExpression p:
                    Effect(p.Expression);
                    return;
                case BoundSpillSequence s:
                    Declare(s.Locals, s.Syntax);
                    foreach (var x in s.SideEffects) Stmt(x);
                    Effect(s.Value);
                    return;
                case BoundLocal:
                case BoundParameter:
                case BoundLiteral:
                case BoundThisReference:
                    return; // reading without using it must not count as a move
                default:
                    var op = Rv(e);
                    if (op is MoveOp && e.Type is { } t && !t.IsVoidType())
                        Assign(Temp(t, e.Syntax), new UseRv { Op = op }, e.Syntax);
                    return;
            }
        }

        private static bool IsPlaceExpr(BoundExpression e) => e switch
        {
            BoundLocal or BoundParameter or BoundFieldAccess or BoundArrayAccess or BoundPointerIndirectionOperator => true,
            BoundThisReference or BoundBaseReference => true,
            BoundCall c => c.Method.RefKind != RefKind.None || IsAnonymousGetter(c),
            BoundSequencePointExpression p => IsPlaceExpr(p.Expression),
            BoundConversion { ConversionKind: ConversionKind.Identity or ConversionKind.ImplicitReference } c => IsPlaceExpr(c.Operand),
            _ => false
        };

        /// <summary>Set by the driver: user code follows Rust's `mut` rules, the corelib does not use `mut`.</summary>
        internal static System.Func<SyntaxTree, bool> IsUserTree;

        private bool IsImmutableRoot(Place p)
            => p.Static is null && _b.Locals[p.Local] is { Immutable: true } l && !l.Type.IsRef
                && _root.Syntax?.SyntaxTree is { } tree && IsUserTree?.Invoke(tree) == true;

        private bool IsBehindShared(Place p)
        {
            var t = p.Static is null ? _b.Locals[p.Local].Type : new MirType(p.Static.Type);
            foreach (var proj in p.Projs)
            {
                if (proj is DerefProj && t.Ref == RefMode.Shared) return true;
                t = MirBody.Project(t, proj);
            }
            return false;
        }

        private void Assignment(BoundAssignmentOperator a)
        {
            if (a.IsRef)
            {
                var dest = RawPlace(a.Left);
                var destType = _b.TypeOf(dest);
                Assign(dest, new RefRv { Mode = destType.Ref == RefMode.None ? RefMode.Mut : destType.Ref, Place = Pl(a.Right) }, a.Syntax);
                return;
            }

            // `fixed` clears its pinned temporary at the end. Nothing moves here, and when the temporary
            // is a borrow of the array the assignment would wipe the array itself.
            if (a.Left is BoundLocal { LocalSymbol: { IsPinned: true } pinned } && _vars.TryGetValue(pinned, out int pinnedIndex) && _aliases.Contains(pinnedIndex))
                return;

            if (a.Left is BoundFieldAccess { FieldSymbol: var link } && OwnershipFacts.IsLinkField(link))
            {
                var source = Pl(a.Right);
                _links[link.OriginalDefinition] = source;
                Assign(Pl(a.Left), new LinkRv { Source = source }, a.Syntax);
                return;
            }

            if (TryPatternBinding(a)) return;

            // Lowering introduces temporaries that merely name an existing place (receivers of compound
            // assignments, the array of a foreach, the input of a pattern match). A plain copy of such a
            // handle would be a move, so they become implicit borrows of that place.
            if (a.Left is BoundLocal { LocalSymbol: { } sym } && sym.RefKind == RefKind.None
                && sym.SynthesizedKind != SynthesizedLocalKind.UserDefined
                && !OwnershipFacts.IsCopy(sym.Type) && !OwnershipFacts.IsString(sym.Type) && IsPlaceExpr(a.Right))
            {
                int index = _vars[sym];
                var source = Pl(a.Right);
                var mode = IsBehindShared(source) || sym.SynthesizedKind == SynthesizedLocalKind.ForEachArray ? RefMode.Shared : RefMode.Mut;
                _b.Locals[index].Type = new MirType(sym.Type, mode);
                _aliases.Add(index);
                Assign(new Place(index), new RefRv { Mode = mode, Place = source }, a.Right.Syntax);
                return;
            }

            // `list[i] = list[i] + 1`: a ref getter on the left borrows exclusively, so the value is
            // computed first, as Rust does for `*g = *g + 1`.
            bool valueFirst = a.Left is BoundCall { Method: { MethodKind: MethodKind.PropertyGet, RefKind: RefKind.Ref } };
            Operand value = null;
            if (valueFirst) value = ToTemp(Rv(a.Right), a.Right.Type ?? a.Left.Type, a.Syntax);
            var target = Pl(a.Left);
            value ??= Rv(a.Right);
            var type = _b.TypeOf(target);
            if (!type.IsRef && OwnershipFacts.NeedsDrop(type.Type))
            {
                // The new value must exist before the old one goes away: `x = Wrap(x)`.
                value = ToTemp(value, type.Type, a.Syntax);
                Emit(new DropStmt { Place = target, ForAssign = true, Syntax = a.Syntax });
            }
            Assign(target, new UseRv { Op = value }, a.Syntax);
        }

        /// <summary>
        /// Pattern variables bind by reference, as match bindings do in Rust: <c>s is Circle c</c> borrows
        /// from <c>s</c> instead of consuming it. A failed test must leave <c>s</c> intact, so a move
        /// would be wrong here.
        /// </summary>
        private static BoundExpression StripSequencePoint(BoundExpression e)
        {
            while (e is BoundSequencePointExpression p) e = p.Expression;
            return e;
        }

        private bool TryPatternBinding(BoundAssignmentOperator a)
        {
            if (a.Left is not BoundLocal { LocalSymbol: { } sym } || sym.RefKind != RefKind.None) return false;
            bool patternLocal = sym.DeclarationKind == LocalDeclarationKind.PatternVariable || sym.SynthesizedKind != SynthesizedLocalKind.UserDefined;
            if (!patternLocal) return false;

            var right = a.Right;
            while (right is BoundConversion { ConversionKind: ConversionKind.Identity } id) right = id.Operand;

            while (right is BoundSequence { Locals.IsEmpty: true, SideEffects.IsEmpty: true } plain) right = plain.Value;
            // `fixed (char* p = s)` pins s; the string stays usable afterwards.
            if (sym.SynthesizedKind == SynthesizedLocalKind.FixedReference && OwnershipFacts.IsString(sym.Type) && IsPlaceExpr(right))
            {
                int pinned = Var(sym, a.Syntax);
                Assign(new Place(pinned), new RetainRv { Place = Pl(right) }, a.Syntax);
                return true;
            }

            // A switch statement first copies its input: `{ d = m; d }`. Look through that to m itself.
            if (sym.SynthesizedKind == SynthesizedLocalKind.SwitchCasePatternMatching
                && right is BoundSequence { Locals.Length: 1, SideEffects.Length: 1 } wrapped
                && wrapped.SideEffects[0] is BoundAssignmentOperator { Left: BoundLocal { LocalSymbol: var copy }, Right: var original }
                && StripSequencePoint(wrapped.Value) is BoundLocal { LocalSymbol: var used } && ReferenceEquals(copy, used) && ReferenceEquals(wrapped.Locals[0], copy))
                right = StripSequencePoint(original);
            // The input of a switch statement: Rust's `match m` looks at m, it does not move it.
            if (sym.SynthesizedKind is SynthesizedLocalKind.SwitchCasePatternMatching or SynthesizedLocalKind.LoweringTemp
                && !OwnershipFacts.IsCopy(sym.Type)
                && (sym.Type.IsReferenceType || !OwnershipFacts.NeedsDrop(sym.Type))
                && StripSequencePoint(right) is BoundParameter or BoundLocal { LocalSymbol.SynthesizedKind: SynthesizedLocalKind.UserDefined } && IsPlaceExpr(right))
            {
                var input = Pl(right);
                int slot = Var(sym, a.Syntax);
                if (OwnershipFacts.IsString(sym.Type))
                {
                    Assign(new Place(slot), new RetainRv { Place = input }, a.Syntax);
                }
                else if (sym.Type.IsReferenceType)
                {
                    var inputMode = IsBehindShared(input.Deref()) || IsImmutableRoot(input) ? RefMode.Shared : RefMode.Mut;
                    _b.Locals[slot].Type = new MirType(sym.Type, inputMode, contents: true);
                    Assign(new Place(slot), new RefRv { Mode = inputMode, Place = input.Deref() }, a.Syntax);
                }
                else if (!OwnershipFacts.NeedsDrop(sym.Type))
                {
                    // An enum or struct without resources: looking at a copy leaves the original in place.
                    Assign(new Place(slot), new UseRv { Op = new CopyOp { Place = input } }, a.Syntax);
                }
                else
                {
                    return false;
                }
                return true;
            }

            BoundExpression source = right switch
            {
                BoundAsOperator { Operand: var o } => o,
                BoundConversion { ConversionKind: ConversionKind.ExplicitReference or ConversionKind.Unboxing, Operand: var o } => o,
                _ => null
            };
            if (source is null || !IsPlaceExpr(source)) return false;

            var place = Pl(source);
            if (right is BoundConversion { ConversionKind: ConversionKind.Unboxing })
            {
                if (!OwnershipFacts.IsCopy(sym.Type)) return false;
                Assign(Pl(a.Left), new PeekBoxRv { Place = place, Type = sym.Type }, a.Syntax);
                return true;
            }

            if (!sym.Type.IsReferenceType) return false;
            int index = Var(sym, a.Syntax);
            // Like Rust's match ergonomics: a binding borrows mutably only through a `mut` variable.
            var mode = IsBehindShared(place.Deref()) || IsImmutableRoot(place) ? RefMode.Shared : RefMode.Mut;
            _b.Locals[index].Type = new MirType(sym.Type, mode, contents: true);
            Assign(new Place(index), new RefRv { Mode = mode, Place = place.Deref(), CastTo = sym.Type }, source.Syntax);
            return true;
        }

        /// <summary>The storage of a ref variable itself, without the implicit dereference.</summary>
        private Place RawPlace(BoundExpression e)
        {
            switch (e)
            {
                case BoundLocal l:
                    return new Place(Var(l.LocalSymbol, l.Syntax));
                case BoundParameter p:
                    return new Place(_vars[p.ParameterSymbol]);
                case BoundFieldAccess f when f.FieldSymbol.RefKind != RefKind.None:
                    var receiver = f.ReceiverOpt;
                    var basePlace = receiver.Type.IsValueType ? Pl(receiver) : Pl(receiver).Deref();
                    return basePlace.Field(f.FieldSymbol);
                default:
                    return Pl(e);
            }
        }

        private int Var(LocalSymbol l, SyntaxNode syntax)
        {
            if (!_vars.TryGetValue(l, out int index))
            {
                Declare(ImmutableArray.Create(l), syntax);
                index = _vars[l];
            }
            return index;
        }

        private Place Materialize(BoundExpression e)
        {
            var op = Rv(e);
            if (op is MoveOp { Place: { IsLocal: true } m } && _b.Locals[m.Local].Kind == LocalKind.Temp) return m;
            var t = Temp(e.Type, e.Syntax);
            Assign(t, new UseRv { Op = op }, e.Syntax);
            return t;
        }

        /// <summary>Evaluates an expression to a place, without moving out of it.</summary>
        private Place Pl(BoundExpression e)
        {
            switch (e)
            {
                case BoundLocal l:
                {
                    int index = Var(l.LocalSymbol, l.Syntax);
                    return l.LocalSymbol.RefKind != RefKind.None || _aliases.Contains(index) ? new Place(index).Deref() : new Place(index);
                }
                case BoundParameter { ParameterSymbol.IsThis: true }:
                    return new Place(_this);
                case BoundParameter p:
                {
                    var place = new Place(_vars[p.ParameterSymbol]);
                    return p.ParameterSymbol.RefKind != RefKind.None ? place.Deref() : place;
                }
                case BoundThisReference:
                case BoundBaseReference:
                {
                    var place = new Place(_this);
                    return _method.ContainingType.IsValueType && _b.Locals[_this].Type.IsRef ? place.Deref() : place;
                }
                case BoundFieldAccess f:
                {
                    Place place;
                    if (f.FieldSymbol.IsStatic)
                    {
                        place = new Place(f.FieldSymbol);
                    }
                    else
                    {
                        var r = f.ReceiverOpt;
                        place = r.Type.IsValueType ? Pl(r) : Pl(r).Deref();
                        place = place.Field(f.FieldSymbol);
                    }
                    return f.FieldSymbol.RefKind != RefKind.None ? place.Deref() : place;
                }
                case BoundArrayAccess a:
                {
                    var array = Pl(a.Expression).Deref();
                    return array.Index(a.Indices.Select(i => ToTemp(Rv(i), i.Type, a.Syntax)).ToArray());
                }
                case BoundPointerIndirectionOperator p:
                {
                    var ptr = Temp(p.Operand.Type, p.Syntax);
                    Assign(ptr, new UseRv { Op = Rv(p.Operand) }, p.Syntax);
                    return ptr.Deref();
                }
                case BoundCall c when IsAnonymousGetter(c):
                {
                    if (OwnershipFacts.OwnedAutoPropertyField(c.Method) is { } backing)
                    {
                        var owner = c.ReceiverOpt.Type.IsValueType ? Pl(c.ReceiverOpt) : Pl(c.ReceiverOpt).Deref();
                        return owner.Field(backing.AsMember(c.Method.ContainingType));
                    }
                    return Pl(c.ReceiverOpt).Deref().Field(AnonymousField(c.Method.ContainingType, c.Method.AssociatedSymbol.Name));
                }
                case BoundCall c when c.Method.RefKind != RefKind.None:
                    return Call(c).Deref();
                case BoundConversion { ConversionKind: ConversionKind.Identity or ConversionKind.ImplicitReference } c when IsPlaceExpr(c.Operand):
                    return Pl(c.Operand);
                case BoundSequence s:
                    Declare(s.Locals, s.Syntax);
                    foreach (var x in s.SideEffects) Effect(x);
                    return Pl(s.Value);
                case BoundConditionalOperator { IsRef: true } c:
                {
                    var r = Temp(new MirType(c.Type, RefMode.Mut), c.Syntax);
                    Conditional(c, r);
                    return r.Deref();
                }
                case BoundAssignmentOperator a:
                    Assignment(a);
                    return Pl(a.Left);
                case BoundConditionalReceiver r:
                    return _conditionalReceivers[r.Id];
                case BoundAwaitableValuePlaceholder p:
                    return _placeholders[p];
                case BoundSequencePointExpression p:
                    return Pl(p.Expression);
                case BoundPassByCopy p when IsPlaceExpr(p.Expression) && !OwnershipFacts.IsCopy(p.Expression.Type):
                    return Pl(p.Expression); // only Copy types can be duplicated; anything else is borrowed
                case BoundPassByCopy p:
                    return Materialize(p.Expression);
                default:
                    return Materialize(e);
            }
        }

        /// <summary>Evaluates an expression to an owned value.</summary>
        private Operand Rv(BoundExpression e)
        {
            // Decimal constants stay on their lowered form, a constructor call or a static field.
            if (e.ConstantValueOpt is { IsDecimal: false } k)
                return new ConstOp { Value = k, Type = e.Type };

            switch (e)
            {
                case BoundLocal:
                case BoundParameter:
                case BoundFieldAccess:
                case BoundArrayAccess:
                case BoundPointerIndirectionOperator:
                case BoundThisReference:
                case BoundBaseReference:
                case BoundConditionalReceiver:
                    return ReadValue(ReadPl(e), e.Syntax);
                case BoundPassByCopy p:
                    return Rv(p.Expression);
                case BoundSequencePointExpression p:
                    return Rv(p.Expression);
                case BoundAssignmentOperator a:
                    Assignment(a);
                    return ReadValue(Pl(a.Left), a.Syntax);
                case BoundCall c when IsAnonymousGetter(c):
                    return ReadValue(Pl(c), c.Syntax);
                case BoundCall c when TryArrayBound(c, out var bound):
                    return bound;
                case BoundCall c when TryStructuralEquals(c, out var equal):
                    return equal;
                case BoundCall c:
                {
                    var result = c.Method.RefKind != RefKind.None ? ReadOnly(() => Call(c)) : Call(c);
                    if (result is null) return new ConstOp { Value = ConstantValue.Null };
                    return c.Method.RefKind != RefKind.None ? ReadValue(result.Deref(), c.Syntax) : Read(result);
                }
                case BoundObjectCreationExpression o:
                    return Read(ObjectCreation(o));
                case BoundConversion c:
                    return Conversion(c);
                case BoundBinaryOperator b:
                    return Binary(b);
                case BoundUnaryOperator u:
                    return Into(new UnaryRv { Op = u.OperatorKind, Value = Rv(u.Operand), OperandType = u.Operand.Type }, u.Type, u.Syntax);
                case BoundConditionalOperator c:
                {
                    if (c.IsRef) return ReadValue(Pl(c), c.Syntax);
                    var t = Temp(c.Type, c.Syntax);
                    Conditional(c, t);
                    return Read(t);
                }
                case BoundSequence s:
                    Declare(s.Locals, s.Syntax);
                    foreach (var x in s.SideEffects) Effect(x);
                    return Rv(s.Value);
                case BoundDefaultExpression d:
                    return Into(new DefaultRv { Type = d.Type }, d.Type, d.Syntax);
                case BoundArrayCreation a:
                    return ArrayCreation(a);
                case BoundConvertedStackAllocExpression a:
                    return StackAlloc(a);
                case BoundArrayLength a:
                    return Into(new ArrayLenRv { Array = Pl(a.Expression).Deref() }, a.Type, a.Syntax);
                case BoundAddressOfOperator a:
                    return Into(new AddrOfRv { Place = Pl(a.Operand) }, a.Type, a.Syntax);
                case BoundSizeOfOperator s:
                    return Into(new SizeOfRv { Type = s.SourceType.Type }, s.Type, s.Syntax);
                case BoundIsOperator i:
                    return Into(new IsInstRv { Place = Pl(i.Operand), Target = i.TargetType.Type }, i.Type, i.Syntax);
                case BoundAsOperator a:
                    return Into(new RefCastRv { Value = Rv(a.Operand), To = a.Type, IsAs = true }, a.Type, a.Syntax);
                case BoundAwaitExpression a:
                    return Await(a);
                case BoundAwaitableValuePlaceholder:
                    return ReadValue(Pl(e), e.Syntax);
                case BoundSpillSequence s:
                    Declare(s.Locals, s.Syntax);
                    foreach (var x in s.SideEffects) Stmt(x);
                    return Rv(s.Value);
                case BoundLoweredConditionalAccess a:
                    return ConditionalAccess(a, wantValue: true);
                case BoundNullCoalescingOperator n:
                    return NullCoalescing(n);
                case BoundDelegateCreationExpression d:
                    return DelegateCreation(d);
                case BoundTypeOfOperator t:
                    return Into(new TypeOfRv { Type = t.SourceType.Type }, t.Type, t.Syntax);
                case BoundFunctionPointerLoad f:
                    return Into(new FnPtrRv { Method = f.TargetMethod }, f.Type, f.Syntax);
                case BoundFunctionPointerInvocation f:
                    return FunctionPointerCall(f);
                case BoundThrowExpression t:
                    Throw(t.Expression, t.Syntax);
                    return Into(new DefaultRv { Type = t.Type }, t.Type, t.Syntax);
                default:
                    return Unsupported(e.Syntax, "expression " + e.Kind);
            }
        }

        private Operand Into(Rvalue rv, TypeSymbol type, SyntaxNode syntax)
        {
            var t = Temp(type, syntax);
            Assign(t, rv, syntax);
            return Read(t);
        }

        private Operand Conversion(BoundConversion c)
        {
            var from = c.Operand.Type;
            switch (c.ConversionKind)
            {
                case ConversionKind.Identity:
                case ConversionKind.ImplicitThrow:
                    return Rv(c.Operand);
                case ConversionKind.ImplicitNumeric:
                case ConversionKind.ExplicitNumeric:
                case ConversionKind.ImplicitEnumeration:
                case ConversionKind.ExplicitEnumeration:
                case ConversionKind.ImplicitConstant:
                case ConversionKind.ImplicitPointerToVoid:
                case ConversionKind.ExplicitPointerToPointer:
                case ConversionKind.ExplicitPointerToInteger:
                case ConversionKind.ExplicitIntegerToPointer:
                case ConversionKind.ImplicitPointer:
                case ConversionKind.IntPtr:
                    return Into(new ConvertRv { Value = Rv(c.Operand), From = from, To = c.Type, Checked = c.Checked }, c.Type, c.Syntax);
                case ConversionKind.PinnedObjectToPointer:
                    return Into(new ConvertRv { Value = new CopyOp { Place = Pl(c.Operand) }, From = c.Type, To = c.Type }, c.Type, c.Syntax);
                case ConversionKind.ImplicitReference:
                    return Into(new RefCastRv { Value = Rv(c.Operand), To = c.Type }, c.Type, c.Syntax);
                case ConversionKind.ExplicitReference:
                    return Into(new RefCastRv { Value = Rv(c.Operand), To = c.Type, Checked = true }, c.Type, c.Syntax);
                case ConversionKind.Boxing:
                    return Into(new BoxRv { Value = Rv(c.Operand), Type = from }, c.Type, c.Syntax);
                case ConversionKind.Unboxing:
                    return Into(new UnboxRv { Value = Rv(c.Operand), Type = c.Type }, c.Type, c.Syntax);
                case ConversionKind.NullLiteral:
                case ConversionKind.DefaultLiteral:
                case ConversionKind.ImplicitNullToPointer:
                    return Into(new DefaultRv { Type = c.Type }, c.Type, c.Syntax);
                default:
                    return Unsupported(c.Syntax, "conversion " + c.ConversionKind);
            }
        }

        private static bool IsHandle(TypeSymbol t) => t is not null && (t.IsReferenceType || t.IsTypeParameter());

        private Operand Binary(BoundBinaryOperator b)
        {
            var kind = b.OperatorKind.Operator();
            if ((b.OperatorKind & BinaryOperatorKind.Logical) != 0 || kind is BinaryOperatorKind.And or BinaryOperatorKind.Or && b.OperatorKind.IsLogical())
                return ShortCircuit(b);

            bool equality = kind is BinaryOperatorKind.Equal or BinaryOperatorKind.NotEqual;
            if (equality && (IsHandle(b.Left.Type) || IsHandle(b.Right.Type) || b.Left.Type is null || b.Right.Type is null))
            {
                // Handles are compared in place: comparing must not consume them.
                var other = IsNullConst(b.Right) ? b.Left : IsNullConst(b.Left) ? b.Right : null;
                if (other != null)
                {
                    // `t == null` on a type parameter boxes in the bound tree; testing must not consume t.
                    if (other is BoundConversion { ConversionKind: ConversionKind.Boxing } boxed) other = boxed.Operand;

                    var isNull = Into(new IsNullRv { Place = Pl(other) }, b.Type, b.Syntax);
                    return kind == BinaryOperatorKind.Equal ? isNull
                        : Into(new UnaryRv { Op = UnaryOperatorKind.BoolLogicalNegation, Value = isNull, OperandType = b.Type }, b.Type, b.Syntax);
                }
                return Into(new BinaryRv
                {
                    Op = b.OperatorKind,
                    Left = new CopyOp { Place = Pl(b.Left) },
                    Right = new CopyOp { Place = Pl(b.Right) },
                    OperandType = _compilation.GetSpecialType(SpecialType.System_Object),
                    RightType = _compilation.GetSpecialType(SpecialType.System_Object)
                }, b.Type, b.Syntax);
            }

            var left = ToTemp(Rv(b.Left), b.Left.Type, b.Syntax);
            var right = Rv(b.Right);
            return Into(new BinaryRv { Op = b.OperatorKind, Left = left, Right = right, OperandType = b.Left.Type, RightType = b.Right.Type }, b.Type, b.Syntax);
        }

        private static bool IsNullConst(BoundExpression e)
            => e.ConstantValueOpt is { IsNull: true } || e is BoundConversion { ConversionKind: ConversionKind.NullLiteral or ConversionKind.DefaultLiteral } || e is BoundDefaultExpression { Type: { IsReferenceType: true } };

        private Operand ShortCircuit(BoundBinaryOperator b)
        {
            bool isAnd = b.OperatorKind.Operator() == BinaryOperatorKind.And;
            var result = Temp(b.Type, b.Syntax);
            var rhs = NewBlock();
            var shortcut = NewBlock();
            var join = NewBlock();
            var left = ToTemp(Rv(b.Left), b.Left.Type, b.Syntax);
            _cur.Term ??= new BranchTerm { Cond = left, IfTrue = isAnd ? rhs : shortcut, IfFalse = isAnd ? shortcut : rhs, Syntax = b.Syntax };
            _cur = shortcut;
            Assign(result, new UseRv { Op = new ConstOp { Value = ConstantValue.Create(!isAnd), Type = b.Type } }, b.Syntax);
            _cur.Term ??= new GotoTerm { Target = join, Syntax = b.Syntax };
            _cur = rhs;
            Assign(result, new UseRv { Op = Rv(b.Right) }, b.Syntax);
            _cur.Term ??= new GotoTerm { Target = join, Syntax = b.Syntax };
            _cur = join;
            return Read(result);
        }

        private void Conditional(BoundConditionalOperator c, Place result)
        {
            var yes = NewBlock();
            var no = NewBlock();
            var join = NewBlock();
            var cond = ToTemp(Rv(c.Condition), c.Condition.Type, c.Syntax);
            _cur.Term ??= new BranchTerm { Cond = cond, IfTrue = yes, IfFalse = no, Syntax = c.Syntax };

            void Arm(BasicBlock block, BoundExpression arm)
            {
                _cur = block;
                if (result is null) Effect(arm);
                else if (c.IsRef)
                {
                    var place = Pl(arm);
                    var mode = IsBehindShared(place) ? RefMode.Shared : RefMode.Mut;
                    if (mode == RefMode.Shared) _b.Locals[result.Local].Type = new MirType(c.Type, RefMode.Shared);
                    Assign(result, new RefRv { Mode = mode, Place = place }, arm.Syntax);
                }
                else Assign(result, new UseRv { Op = Rv(arm) }, arm.Syntax);
                _cur.Term ??= new GotoTerm { Target = join, Syntax = c.Syntax };
            }

            Arm(yes, c.Consequence);
            Arm(no, c.Alternative);
            _cur = join;
        }

        private readonly Dictionary<BoundAwaitableValuePlaceholder, Place> _placeholders = new Dictionary<BoundAwaitableValuePlaceholder, Place>();

        /// <summary>Calls a member on a value in a place, borrowing it the way the member declares.</summary>
        private Place CallOn(MethodSymbol m, Place receiver, TypeSymbol type, SyntaxNode syntax)
        {
            var term = new CallTerm { Method = m, Syntax = syntax };
            var mode = OwnershipFacts.GetThisMode(m) == ThisMode.Shared ? RefMode.Shared : RefMode.Mut;
            if (OwnershipFacts.GetThisMode(m) == ThisMode.Value)
            {
                term.Args.Add(ToTemp(ReadValue(receiver, syntax), type, syntax));
            }
            else
            {
                bool handle = type.IsReferenceType;
                var t = Temp(new MirType(type, mode, contents: handle), syntax);
                Assign(t, new RefRv { Mode = mode, Place = handle ? receiver.Deref() : receiver }, syntax);
                term.Args.Add(Read(t));
            }
            term.Virtual = (m.IsVirtual || m.IsAbstract || m.IsOverride) && !type.IsValueType;
            Place result = null;
            if (!m.ReturnsVoid)
            {
                result = Temp(new MirType(m.ReturnType, OwnershipFacts.ReturnMode(m)), syntax);
                term.Dest = result;
            }
            term.Target = NewBlock();
            term.Unwind = Unwind();
            _cur.Term ??= term;
            _cur = term.Target;
            return result;
        }

        /// <summary>
        /// `await x`: get the awaiter, then test and suspend until it is complete, as a Rust `.await`
        /// loops over poll. Everything stays visible to the borrow checker as ordinary control flow.
        /// </summary>
        private Operand Await(BoundAwaitExpression a)
        {
            var info = a.AwaitableInfo;
            if (info.GetAwaiter is null) return Unsupported(a.Syntax, "this kind of await");

            var awaitable = Temp(a.Expression.Type, a.Syntax);
            Assign(awaitable, new UseRv { Op = Rv(a.Expression) }, a.Syntax);
            if (info.AwaitableInstancePlaceholder is { } placeholder) _placeholders[placeholder] = awaitable;

            var awaiterType = info.GetAwaiter.Type;
            var awaiter = Temp(awaiterType, a.Syntax);
            Assign(awaiter, new UseRv { Op = Rv(info.GetAwaiter) }, a.Syntax);

            var head = NewBlock();
            Goto(head, a.Syntax);
            var completed = CallOn(info.IsCompleted.GetMethod, awaiter, awaiterType, a.Syntax);
            var ready = NewBlock();
            var wait = NewBlock();
            _cur.Term ??= new BranchTerm { Cond = Read(completed), IfTrue = ready, IfFalse = wait, Syntax = a.Syntax };
            _cur = wait;
            _cur.Term = new SuspendTerm { Resume = head, Syntax = a.Syntax };
            _cur = ready;

            var result = CallOn(info.GetResult, awaiter, awaiterType, a.Syntax);
            return result is null ? new ConstOp { Value = ConstantValue.Null } : Read(result);
        }

        private Operand NullCoalescing(BoundNullCoalescingOperator n)
        {
            var left = Pl(n.LeftOperand);
            var boolean = _compilation.GetSpecialType(SpecialType.System_Boolean);
            var isNull = Into(new IsNullRv { Place = left }, boolean, n.Syntax);
            var result = Temp(n.Type, n.Syntax);
            var useRight = NewBlock();
            var useLeft = NewBlock();
            var join = NewBlock();
            _cur.Term ??= new BranchTerm { Cond = isNull, IfTrue = useRight, IfFalse = useLeft, Syntax = n.Syntax };
            _cur = useLeft;
            Assign(result, new UseRv { Op = ReadValue(left, n.Syntax) }, n.Syntax);
            _cur.Term ??= new GotoTerm { Target = join, Syntax = n.Syntax };
            _cur = useRight;
            Assign(result, new UseRv { Op = Rv(n.RightOperand) }, n.Syntax);
            _cur.Term ??= new GotoTerm { Target = join, Syntax = n.Syntax };
            _cur = join;
            return Read(result);
        }

        private Operand ConditionalAccess(BoundLoweredConditionalAccess a, bool wantValue)
        {
            var receiver = Pl(a.Receiver);
            var boolean = _compilation.GetSpecialType(SpecialType.System_Boolean);
            Operand hasValue;
            if (a.HasValueMethodOpt != null)
            {
                var flag = Temp(boolean, a.Syntax);
                var borrow = Temp(new MirType(receiver is null ? boolean : a.Receiver.Type, RefMode.Shared), a.Syntax);
                Assign(borrow, new RefRv { Mode = RefMode.Shared, Place = receiver }, a.Syntax);
                var call = new CallTerm { Dest = flag, Method = a.HasValueMethodOpt, Target = NewBlock(), Unwind = Unwind(), Syntax = a.Syntax };
                call.Args.Add(Read(borrow));
                _cur.Term = call;
                _cur = call.Target;
                hasValue = Read(flag);
            }
            else
            {
                var isNull = Into(new IsNullRv { Place = receiver }, boolean, a.Syntax);
                hasValue = Into(new UnaryRv { Op = UnaryOperatorKind.BoolLogicalNegation, Value = isNull, OperandType = boolean }, boolean, a.Syntax);
            }

            _conditionalReceivers[a.Id] = receiver;
            bool produces = wantValue && a.Type is { } t && !t.IsVoidType();
            var result = produces ? Temp(a.Type, a.Syntax) : null;
            var yes = NewBlock();
            var no = NewBlock();
            var join = NewBlock();
            _cur.Term ??= new BranchTerm { Cond = hasValue, IfTrue = yes, IfFalse = no, Syntax = a.Syntax };

            _cur = yes;
            if (produces) Assign(result, new UseRv { Op = Rv(a.WhenNotNull) }, a.Syntax);
            else Effect(a.WhenNotNull);
            _cur.Term ??= new GotoTerm { Target = join, Syntax = a.Syntax };

            _cur = no;
            if (produces)
            {
                if (a.WhenNullOpt != null) Assign(result, new UseRv { Op = Rv(a.WhenNullOpt) }, a.Syntax);
                else Assign(result, new DefaultRv { Type = a.Type }, a.Syntax);
            }
            _cur.Term ??= new GotoTerm { Target = join, Syntax = a.Syntax };

            _cur = join;
            return produces ? Read(result) : new ConstOp { Value = ConstantValue.Null };
        }

        private Operand ArrayCreation(BoundArrayCreation a)
        {
            var lengths = a.Bounds.Select(b => ToTemp(Rv(b), b.Type, a.Syntax)).ToArray();
            var t = Temp(a.Type, a.Syntax);
            Assign(t, new NewArrayRv { ArrayType = a.Type, Lengths = lengths }, a.Syntax);
            if (a.InitializerOpt != null) FillArray(t, a.InitializerOpt, new List<int>());
            return Read(t);
        }

        private void FillArray(Place array, BoundArrayInitialization init, List<int> prefix)
        {
            var intType = _compilation.GetSpecialType(SpecialType.System_Int32);
            for (int i = 0; i < init.Initializers.Length; i++)
            {
                prefix.Add(i);
                if (init.Initializers[i] is BoundArrayInitialization nested)
                {
                    FillArray(array, nested, prefix);
                }
                else
                {
                    var value = Rv(init.Initializers[i]);
                    var indices = prefix.Select(x => (Operand)new ConstOp { Value = ConstantValue.Create(x), Type = intType }).ToArray();
                    Assign(array.Deref().Index(indices), new UseRv { Op = value }, init.Syntax);
                }
                prefix.RemoveAt(prefix.Count - 1);
            }
        }

        /// <summary>The bounds of a multidimensional array; only the static type knows its rank.</summary>
        private bool TryArrayBound(BoundCall c, out Operand result)
        {
            result = null;
            if (c.Method.ContainingType.SpecialType != SpecialType.System_Array) return false;
            if (c.Method.Name is not ("GetLength" or "GetLowerBound" or "GetUpperBound")) return false;

            var receiver = c.ReceiverOpt;
            while (receiver is BoundConversion { ConversionKind: ConversionKind.ImplicitReference or ConversionKind.Identity } conv) receiver = conv.Operand;
            if (receiver.Type is not ArrayTypeSymbol { IsSZArray: false }) return false;

            if (c.Method.Name == "GetLowerBound")
            {
                Effect(c.Arguments[0]);
                result = new ConstOp { Value = ConstantValue.Create(0), Type = c.Type };
                return true;
            }

            var place = Pl(receiver).Deref();
            var dimension = ToTemp(Rv(c.Arguments[0]), c.Arguments[0].Type, c.Syntax);
            var length = Into(new ArrayDimRv { Array = place, Dimension = dimension }, c.Type, c.Syntax);
            result = c.Method.Name == "GetLength" ? length : Into(new BinaryRv
            {
                Op = BinaryOperatorKind.IntSubtraction,
                Left = length,
                Right = new ConstOp { Value = ConstantValue.Create(1), Type = c.Type },
                OperandType = c.Type,
                RightType = c.Type
            }, c.Type, c.Syntax);
            return true;
        }

        private Operand StackAlloc(BoundConvertedStackAllocExpression s)
        {
            var bytes = ToTemp(Rv(s.Count), s.Count.Type, s.Syntax);
            List<Operand> init = null;
            if (s.InitializerOpt != null)
            {
                init = new List<Operand>();
                foreach (var e in s.InitializerOpt.Initializers) init.Add(ToTemp(Rv(e), e.Type, s.Syntax));
            }
            return Into(new StackAllocRv { Element = s.ElementType, Bytes = bytes, Init = init }, s.Type, s.Syntax);
        }

        private readonly struct Capture
        {
            public readonly ImmutableArray<FieldSymbol> Path;
            public readonly RefMode Mode;
            public readonly bool Consumed;
            public Capture(ImmutableArray<FieldSymbol> path, RefMode mode, bool consumed = false) { Path = path; Mode = mode; Consumed = consumed; }
        }

        /// <summary>
        /// What a closure uses of its receiver, and how: Rust's capture inference. Works on the closure's
        /// own MIR, one path per captured variable, so closures only conflict over the same variables.
        /// </summary>
        private List<Capture> CapturesOf(MethodSymbol method)
        {
            var body = _lookup(method);
            var found = new Dictionary<string, Capture>();
            if (body is null) return null;

            void See(Place p, bool write, bool consume = false)
            {
                if (p.Static is not null || p.Local != 1 || p.Projs.IsEmpty || p.Projs[0] is not DerefProj) return;
                var path = ImmutableArray.CreateBuilder<FieldSymbol>();
                for (int i = 1; i < p.Projs.Length && p.Projs[i] is FieldProj f; i += 2)
                {
                    path.Add(f.Field);
                    if (!OwnershipFacts.IsLinkField(f.Field) || i + 1 >= p.Projs.Length || p.Projs[i + 1] is not DerefProj) break;
                }

                string key = string.Join("/", path.Select(x => x.Name));
                var mode = write ? RefMode.Mut : RefMode.Shared;
                found.TryGetValue(key, out var existing);
                bool consumed = consume && p.Projs.Length == path.Count * 2 || existing.Consumed;
                found[key] = new Capture(path.ToImmutable(), existing.Mode == RefMode.Mut ? RefMode.Mut : mode, consumed);
            }

            void SeeOperand(Operand op)
            {
                if (op is CopyOp c) See(c.Place, false);
                else if (op is MoveOp m) See(m.Place, true, consume: true);
            }

            foreach (var block in body.Reachable())
            {
                foreach (var s in block.Statements)
                {
                    if (s is DropStmt drop) See(drop.Place, true);
                    if (s is not AssignStmt a) continue;
                    See(a.Dest, true);
                    switch (a.Value)
                    {
                        case RefRv r: See(r.Place, r.Mode == RefMode.Mut); break;
                        case AddrOfRv r: See(r.Place, true); break;
                        case RetainRv r: See(r.Place, false); break;
                        case ArrayLenRv r: See(r.Array, false); break;
                        case ArrayDimRv r: See(r.Array, false); break;
                        case IsInstRv r: See(r.Place, false); break;
                        case IsNullRv r: See(r.Place, false); break;
                        case PeekBoxRv r: See(r.Place, false); break;
                        case LinkRv r: See(r.Source, false); break;
                        case StructEqRv e: See(e.Left, false); See(e.Right, false); break;
                    }
                    foreach (var op in BorrowChecker.Operands(a.Value)) SeeOperand(op);
                }
                foreach (var op in BorrowChecker.TermOperands(block.Term)) SeeOperand(op);
                if (block.Term is CallTerm { Dest: { } dest }) See(dest, true);
            }
            return found.Values.ToList();
        }

        private Place CapturedPlace(Place receiver, ImmutableArray<FieldSymbol> path)
        {
            var cur = receiver;
            foreach (var f in path)
            {
                cur = cur.Field(f);
                if (!OwnershipFacts.IsLinkField(f) || f == path[^1]) continue;
                cur = _links.TryGetValue(f.OriginalDefinition, out var link) ? link.Deref() : cur.Deref();
            }
            return cur;
        }

        private static bool IsThisLink(FieldSymbol f) => OwnershipFacts.IsLinkField(f) && !MirBody.IsClosureEnvironment(f.Type);

        private void MoveCaptures(Place from, NamedTypeSymbol type, Place to, List<ImmutableArray<FieldSymbol>> paths, int depth, List<Place> environments, List<TypeSymbol> types, SyntaxNode syntax)
        {
            foreach (var group in paths.GroupBy(p => p[depth].OriginalDefinition, Symbols.SymbolEqualityComparer.AllIgnoreOptions))
            {
                var field = ((FieldSymbol)group.Key).AsMember(type);
                if (group.All(p => p.Length == depth + 1))
                {
                    types.Add(field.Type);
                    Assign(to.Deref().Field(field), new UseRv { Op = ReadValue(from.Field(field), syntax) }, syntax);
                    continue;
                }

                var outerType = (NamedTypeSymbol)field.Type;
                var outer = Temp(outerType, syntax);
                Assign(outer, new NewObjRv { Type = outerType }, syntax);
                environments.Add(outer);
                Assign(to.Deref().Field(field), new LinkRv { Source = outer }, syntax);
                var source = _links.TryGetValue(field.OriginalDefinition, out var link) ? link.Deref() : from.Field(field).Deref();
                MoveCaptures(source, outerType, outer, group.ToList(), depth + 1, environments, types, syntax);
            }
        }

        private static bool IsMoveClosure(BoundDelegateCreationExpression d)
            => d.Syntax is Syntax.AnonymousFunctionExpressionSyntax lambda && lambda.Modifiers.Any(SyntaxKind.MoveKeyword);

        private Operand DelegateCreation(BoundDelegateCreationExpression d)
        {
            var method = d.MethodOpt;
            if (method is null) return Unsupported(d.Syntax, "delegate conversion");

            // A non-capturing lambda needs no receiver; the backend gives it a thunk.
            bool noTarget = method.IsStatic || method.ContainingType.OriginalDefinition is SynthesizedClosureEnvironment env && IsSingleton(env);
            if (noTarget)
            {
                var none = new ConstOp { Value = ConstantValue.Null, Type = _compilation.GetSpecialType(SpecialType.System_Object) };
                return Into(new NewDelegateRv { Type = d.Type, Target = none, Method = method }, d.Type, d.Syntax);
            }

            bool closure = method.OriginalDefinition is SynthesizedClosureMethod;
            bool ofThis = d.Argument is BoundThisReference or BoundBaseReference;
            if (!closure && !ofThis && OwnershipFacts.GetThisMode(method) == ThisMode.Mut
                && !OwnershipFacts.IsMutDelegate(d.Type) && !OwnershipFacts.IsOnceDelegate(d.Type))
                _diagnostics.Add(new OwnershipDiagnostic
                {
                    Code = ErrorCode.ERR_OwnClosureMutates,
                    Message = $"this method changes its object, so the delegate type must be [Mut]",
                    Location = d.Syntax.Location,
                    Label = "a non-readonly method",
                    Note = "make the method `readonly`, or mark the delegate type [Mut]"
                });
            if (!closure && !ofThis)
                return Into(new NewDelegateRv { Type = d.Type, Target = Rv(d.Argument), CapturedTypes = new List<TypeSymbol> { d.Argument.Type }, Method = method, Syntax = d.Syntax }, d.Type, d.Syntax);

            var receiver = Pl(d.Argument);
            var captures = closure ? CapturesOf(method) : new List<Capture> { new Capture(ImmutableArray<FieldSymbol>.Empty, OwnershipFacts.GetThisMode(method) == ThisMode.Shared ? RefMode.Shared : RefMode.Mut) };
            captures ??= new List<Capture>();

            bool mayMutate = OwnershipFacts.IsMutDelegate(d.Type) || OwnershipFacts.IsOnceDelegate(d.Type);
            foreach (var c in captures)
            {
                if (c.Mode == RefMode.Mut && !c.Consumed && !mayMutate)
                {
                    string changed = c.Path.IsEmpty ? "this" : c.Path[^1].Name;
                    _diagnostics.Add(new OwnershipDiagnostic
                    {
                        Code = ErrorCode.ERR_OwnClosureMutates,
                        Message = $"this lambda changes `{changed}`, so its delegate type must be [Mut]",
                        Location = d.Syntax.Location,
                        Label = "changes a captured variable",
                        Note = "a [Mut] delegate is Rust's FnMut: calling it needs exclusive access"
                    });
                }
                if (!c.Consumed) continue;
                string name = c.Path[^1].Name;
                if (!IsMoveClosure(d) || !OwnershipFacts.IsOnceDelegate(d.Type))
                    _diagnostics.Add(new OwnershipDiagnostic
                    {
                        Code = ErrorCode.ERR_OwnMoveOutOfBorrow,
                        Message = $"cannot move `{name}` out of a captured variable in a lambda that can run more than once",
                        Location = d.Syntax.Location,
                        Label = "this lambda consumes its capture",
                        Note = "only a `move` lambda converted to a [Once] delegate may consume what it captures"
                    });
            }

            if (IsMoveClosure(d))
            {
                if (ofThis || captures.Any(c => c.Path.IsEmpty || c.Path.Any(IsThisLink)))
                    return Unsupported(d.Syntax, "a `move` lambda that captures `this`");

                // The closure gets its own environments, holding just what it uses. Moves happen per
                // variable, so other closures of the same scope keep working on theirs.
                var type = (NamedTypeSymbol)d.Argument.Type;
                var owned = Temp(type, d.Syntax);
                Assign(owned, new NewObjRv { Type = type }, d.Syntax);
                var environments = new List<Place> { owned };
                var types = new List<TypeSymbol>();
                MoveCaptures(receiver.Deref(), type, owned, captures.Select(c => c.Path).ToList(), 0, environments, types, d.Syntax);
                if (environments.Count == 1)
                    return Into(new NewDelegateRv { Type = d.Type, Target = Read(owned), CapturedTypes = types, Method = method, Syntax = d.Syntax }, d.Type, d.Syntax);

                // Several levels: the delegate calls the innermost one and owns them all through an array.
                var objectType = _compilation.GetSpecialType(SpecialType.System_Object);
                var intType = _compilation.GetSpecialType(SpecialType.System_Int32);
                var self = Temp(_compilation.CreatePointerTypeSymbol(_compilation.GetSpecialType(SpecialType.System_Void)), d.Syntax);
                Assign(self, new AddrOfRv { Place = owned.Deref() }, d.Syntax);
                var arrayType = _compilation.CreateArrayTypeSymbol(objectType);
                var keep = Temp(arrayType, d.Syntax);
                Assign(keep, new NewArrayRv { ArrayType = arrayType, Lengths = new Operand[] { new ConstOp { Value = ConstantValue.Create(environments.Count), Type = intType } } }, d.Syntax);
                for (int i = 0; i < environments.Count; i++)
                {
                    var asObject = Into(new RefCastRv { Value = Read(environments[i]), To = objectType }, objectType, d.Syntax);
                    Assign(keep.Deref().Index(new ConstOp { Value = ConstantValue.Create(i), Type = intType }), new UseRv { Op = asObject }, d.Syntax);
                }
                return Into(new NewDelegateRv { Type = d.Type, Target = Read(keep), Borrowed = self, CapturedTypes = types, Method = method, Syntax = d.Syntax }, d.Type, d.Syntax);
            }

            var borrows = new List<Operand>();
            var borrowed = new List<(TypeSymbol, RefMode)>();
            foreach (var c in captures)
            {
                var place = CapturedPlace(receiver.Deref(), c.Path);
                borrowed.Add((_b.TypeOf(place).Type, c.Mode));
                var t = Temp(new MirType(_b.TypeOf(place).Type, c.Mode, _b.TypeOf(place).Contents), d.Syntax);
                Assign(t, new RefRv { Mode = c.Mode, Place = place }, d.Syntax);
                borrows.Add(Read(t));
            }
            return Into(new NewDelegateRv { Type = d.Type, Borrowed = receiver, Captures = borrows, BorrowedTypes = borrowed, Method = method, Syntax = d.Syntax }, d.Type, d.Syntax);
        }

        /// <summary>Set while a place is only read, so `ref` getters on the way borrow shared.</summary>
        private bool _readOnlyPlace;

        private T ReadOnly<T>(System.Func<T> f)
        {
            bool old = _readOnlyPlace;
            _readOnlyPlace = true;
            try { return f(); }
            finally { _readOnlyPlace = old; }
        }

        private Place ReadPl(BoundExpression e) => ReadOnly(() => Pl(e));

        private Place WritePl(BoundExpression e)
        {
            bool old = _readOnlyPlace;
            _readOnlyPlace = false;
            try { return Pl(e); }
            finally { _readOnlyPlace = old; }
        }

        private void Report(ErrorCode code, string message, SyntaxNode syntax, string label)
            => _diagnostics.Add(new OwnershipDiagnostic { Code = code, Message = message, Location = syntax.Location, Label = label });

        /// <summary>A call to a static corelib helper; arguments are moved in unless they are borrows.</summary>
        private Place StaticCall(MethodSymbol m, SyntaxNode syntax, params Operand[] args)
        {
            var dest = m.ReturnsVoid ? null : Temp(m.ReturnType, syntax);
            var call = new CallTerm { Dest = dest, Method = m, Target = NewBlock(), Unwind = Unwind(), Syntax = syntax };
            call.Args.AddRange(args);
            _cur.Term = call;
            _cur = call.Target;
            return dest;
        }

        private MethodSymbol Helper(string name, int arity, ImmutableArray<TypeWithAnnotations> typeArgs)
        {
            var helper = _compilation.GetTypeByMetadataName("System.Propagation");
            var m = helper.GetMembers(name).OfType<MethodSymbol>().First(x => x.Arity == arity);
            return m.Construct(typeArgs);
        }

        /// <summary>
        /// Rust's <c>x?</c>: on Err (or None) the method returns at once, dropping its locals as a
        /// return would; otherwise the expression is the value inside. A different error type goes
        /// through an implicit conversion, which is Rust's From.
        /// </summary>
        private Place Propagate(BoundCall c)
        {
            var syntax = c.Syntax;
            var wrapper = (NamedTypeSymbol)c.Arguments[0].Type;
            bool option = wrapper.Arity == 1;
            var args = wrapper.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics;
            var boolean = _compilation.GetSpecialType(SpecialType.System_Boolean);

            var source = Temp(wrapper, syntax);
            Assign(source, new UseRv { Op = Rv(c.Arguments[0]) }, syntax);
            var borrow = Temp(new MirType(wrapper, RefMode.Shared), syntax);
            Assign(borrow, new RefRv { Mode = RefMode.Shared, Place = source }, syntax);
            var failed = StaticCall(Helper("Failed", wrapper.Arity, args), syntax, Read(borrow));

            var fail = NewBlock();
            var ok = NewBlock();
            _cur.Term ??= new BranchTerm { Cond = Read(failed), IfTrue = fail, IfFalse = ok, Syntax = syntax };

            _cur = fail;
            var target = OwnershipFacts.IsCoroutine(_method) ? OwnershipFacts.CoroutineResult(_method, _compilation) : _method.ReturnType;
            bool fits = target is NamedTypeSymbol { ContainingNamespace.Name: "System" } t && !_method.IsIterator
                && (option ? (t.Name, t.Arity) == ("Option", 1) : (t.Name, t.Arity) == ("Result", 2));
            PushScope();
            if (!fits)
            {
                Report(ErrorCode.ERR_OwnPropagateReturn, $"the `?` operator can only be used in a method that returns {(option ? "Option" : "Result")}",
                    syntax, "cannot use `?` here");
            }
            else
            {
                var returned = (NamedTypeSymbol)target;
                Place residual;
                if (option)
                {
                    residual = StaticCall(Helper("NoneOf", 2, ImmutableArray.Create(args[0], returned.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics[0])), syntax, Read(source));
                }
                else
                {
                    var from = args[1].Type;
                    var to = returned.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics[1];
                    var error = StaticCall(Helper("ErrorOf", 2, args), syntax, Read(source));
                    if (!from.Equals(to.Type, TypeCompareKind.AllIgnoreOptions))
                    {
                        var useSite = CompoundUseSiteInfo<AssemblySymbol>.Discarded;
                        var conversion = _compilation.Conversions.ClassifyImplicitConversionFromType(from, to.Type, ref useSite);
                        if (conversion.IsUserDefined && conversion.Method is { } convert)
                        {
                            error = StaticCall(convert, syntax, Read(error));
                        }
                        else if (!conversion.IsIdentity && !conversion.IsReference)
                        {
                            Report(ErrorCode.ERR_OwnPropagateReturn,
                                $"`?` cannot convert the error `{from.ToDisplayString()}` to `{to.Type.ToDisplayString()}`: add an implicit conversion, Rust's From",
                                syntax, "the error types differ");
                        }
                    }
                    var wrap = Helper("Fail", 2, ImmutableArray.Create(returned.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics[0], to));
                    residual = StaticCall(wrap, syntax, Read(error));
                }
                Assign(new Place(0), new UseRv { Op = Read(residual) }, syntax);
            }
            ExitTo(0, syntax);
            _scopes.RemoveAt(_scopes.Count - 1);
            Terminate(new GotoTerm { Target = _returnBlock, Syntax = syntax });

            _cur = ok;
            return StaticCall(Helper("ValueOf", wrapper.Arity, args), syntax, Read(source));
        }

        /// <summary>
        /// Rust's match ergonomics: destructuring a borrowed record (`Node(var l, var r)` on a pattern
        /// variable) binds its fields by reference, and copies those that are Copy, instead of moving
        /// them out of something that is only borrowed.
        /// </summary>
        private bool TryDeconstructByReference(BoundCall c)
        {
            if (c.Method.OriginalDefinition is not SynthesizedRecordDeconstruct || c.ReceiverOpt is not { } receiver || !IsPlaceExpr(receiver)) return false;
            if (OwnershipFacts.GetThisMode(c.Method) != ThisMode.Value) return false;
            var holder = Pl(receiver);
            var holderType = _b.TypeOf(holder);
            if (!holderType.IsRef) return false;

            var fields = OwnershipFacts.InstanceFields(c.Method.ContainingType).ToList();
            var targets = new List<(int Local, FieldSymbol Field)>();
            for (int i = 0; i < c.Arguments.Length; i++)
            {
                var field = fields.FirstOrDefault(f => f.Name == "<" + c.Method.Parameters[i].Name + ">k__BackingField");
                if (field is null) return false;
                switch (c.Arguments[i])
                {
                    case BoundDiscardExpression:
                        targets.Add((-1, field));
                        break;
                    case BoundLocal { LocalSymbol: var local } when _vars.TryGetValue(local, out int index):
                        targets.Add((index, field));
                        break;
                    default:
                        return false;
                }
            }

            var obj = holder.Deref();
            foreach (var (index, field) in targets)
            {
                if (index < 0) continue;
                var place = obj.Field(field);
                if (OwnershipFacts.IsCopy(field.Type))
                {
                    Assign(new Place(index), new UseRv { Op = new CopyOp { Place = place } }, c.Syntax);
                }
                else if (field.Type.IsReferenceType)
                {
                    _b.Locals[index].Type = new MirType(field.Type, holderType.Ref, contents: true);
                    Assign(new Place(index), new RefRv { Mode = holderType.Ref, Place = place.Deref() }, c.Syntax);
                }
                else
                {
                    _b.Locals[index].Type = new MirType(field.Type, holderType.Ref);
                    Assign(new Place(index), new RefRv { Mode = holderType.Ref, Place = place }, c.Syntax);
                }
            }
            return true;
        }

        /// <summary>
        /// Mem.UninitArray: Rust's Box::new_uninit_slice. The caller writes every element with Mem.Write before
        /// anything reads it, so no zeroed element is ever seen as a value.
        /// </summary>
        private Place TryUninitArray(BoundCall c)
        {
            if (c.Method is not { Name: "UninitArray", IsExtern: true, ContainingType: { Name: "Mem", ContainingNamespace.Name: "System" } } m || c.Arguments.Length != 1) return null;
            var length = ToTemp(Rv(c.Arguments[0]), c.Arguments[0].Type, c.Syntax);
            var t = Temp(m.ReturnType, c.Syntax);
            Assign(t, new NewArrayRv { ArrayType = m.ReturnType, Lengths = new[] { length } }, c.Syntax);
            return t;
        }

        /// <summary>`str s = "abc"`: Rust's &'static str, pointing at the literal's own bytes, borrowing nothing.</summary>
        private Place TryStaticStr(BoundCall c)
        {
            if (c.Method is not { Name: "op_Implicit", ContainingType: { Name: "str", ContainingNamespace.Name: "System" } } || c.Arguments.Length != 1) return null;
            var argument = c.Arguments[0];
            while (true)
            {
                if (argument is BoundSequence { SideEffects: [BoundAssignmentOperator { Left: BoundLocal l, Right: var r }], Value: BoundLocal v } seq
                    && ReferenceEquals(l.LocalSymbol, v.LocalSymbol))
                    argument = r;
                else if (argument is BoundConversion { ConversionKind: ConversionKind.Identity } id)
                    argument = id.Operand;
                else break;
            }
            if (argument is not BoundLiteral { ConstantValueOpt: { IsString: true } constant }) return null;
            var mem = _compilation.GetTypeByMetadataName("System.Mem");
            var make = mem.GetMembers("StaticStr").OfType<MethodSymbol>().First();
            var dest = Temp(c.Type, c.Syntax);
            var call = new CallTerm { Dest = dest, Method = make, Target = NewBlock(), Unwind = Unwind(), Syntax = c.Syntax };
            call.Args.Add(new ConstOp { Value = constant, Type = argument.Type });
            _cur.Term = call;
            _cur = call.Target;
            return dest;
        }

        private static bool IsSingleton(SynthesizedClosureEnvironment env) => env.SingletonCache is not null;

        private static bool IsUserMethod(MethodSymbol m)
            => m.OriginalDefinition.DeclaringSyntaxReferences.FirstOrDefault()?.SyntaxTree is { } tree && IsUserTree?.Invoke(tree) == true;

        private void AddArguments(CallTerm term, MethodSymbol m, ImmutableArray<BoundExpression> arguments, SyntaxNode syntax)
        {
            for (int i = 0; i < arguments.Length; i++)
            {
                var a = arguments[i];
                var p = i < m.ParameterCount ? m.Parameters[i] : null;
                var mode = p is null ? RefMode.None : OwnershipFacts.ParamMode(p);
                if (mode == RefMode.None && StrictStrings && p is not null && OwnershipFacts.IsString(p.OriginalDefinition.Type)
                    && !IsUserMethod(m) && IsPlaceExpr(a) && OwnershipFacts.IsString(a.Type))
                {
                    // A corelib method that takes a string reads it, like Rust's &str parameters.
                    term.Args.Add(Share(Pl(a), a.Syntax));
                }
                else if (mode == RefMode.None)
                {
                    term.Args.Add(ToTemp(Rv(a), p?.Type ?? a.Type, a.Syntax));
                }
                else
                {
                    var place = Pl(a);
                    var t = Temp(new MirType(p.Type, mode), a.Syntax);
                    Assign(t, new RefRv { Mode = mode, Place = place }, a.Syntax);
                    term.Args.Add(Read(t));
                }
            }
        }

        private Place Call(BoundCall c)
        {
            if (c.Method.Name == "Propagate" && c.Method.ContainingType is { Name: "Propagation", ContainingNamespace.Name: "System" })
                return Propagate(c);

            // `[Copy] T`: Rust's `T: Copy` bound, checked where the type argument is known.
            if (c.Method.IsGenericMethod)
            {
                var parameters = c.Method.OriginalDefinition.TypeParameters;
                var arguments = c.Method.TypeArgumentsWithAnnotations;
                for (int i = 0; i < parameters.Length && i < arguments.Length; i++)
                {
                    var t = arguments[i].Type;
                    if (t is TypeParameterSymbol || OwnershipFacts.IsCopy(t)) continue;
                    if (!parameters[i].GetAttributes().Any(a => a.AttributeClass?.Name == "CopyAttribute")) continue;
                    Report(ErrorCode.ERR_OwnNotClone, $"`{t.ToDisplayString()}` is not Copy", c.Syntax, $"`{c.Method.Name}` needs a Copy type; Cloned works for any Clone type");
                }
            }

            // A struct has no object header to read the type from; its static type is exact.
            if (c.Method.Name == "GetType" && c.Method.ContainingType.SpecialType == SpecialType.System_Object
                && c.ReceiverOpt is { Type: { IsReferenceType: false } valueType } value)
            {
                Effect(value);
                var type = Temp(c.Type, c.Syntax);
                Assign(type, new TypeOfRv { Type = valueType }, c.Syntax);
                return type;
            }

            if (TryDeconstructByReference(c)) return null;
            if (TryStaticStr(c) is { } literal) return literal;
            if (TryUninitArray(c) is { } array) return array;

            var m = c.Method;
            var term = new CallTerm { Method = m, Syntax = c.Syntax };
            var mode = OwnershipFacts.GetThisMode(m);

            // `T.Default()` on a static abstract interface member: Rust's `T::default()`, resolved per T.
            if (m.IsStatic && m.ContainingType.IsInterface && (m.IsAbstract || m.IsVirtual) && c.ReceiverOpt is BoundTypeExpression { Type: var constrained })
                term.ConstrainedTo = constrained;
            var receiver = c.ReceiverOpt;
            Place receiverPlace = null;

            if (!m.IsStatic)
            {
                if (receiver is null)
                {
                    Unsupported(c.Syntax, "call without receiver");
                    return null;
                }

                term.Virtual = (m.IsVirtual || m.IsAbstract || m.IsOverride) && receiver is not BoundBaseReference && !receiver.Type.IsValueType;

                // Reading through a `ref` getter such as `list[0]` is Rust's Index, a shared borrow;
                // only a write through it is IndexMut.
                if (mode == ThisMode.Mut && _readOnlyPlace && m.RefKind != RefKind.None && m.MethodKind == MethodKind.PropertyGet)
                    mode = ThisMode.Shared;

                // A consuming method through a reference moves the referent, which the checker rejects
                // as a move out of a borrow (Rust's E0507); it must not take the reference itself.
                if (mode == ThisMode.Value && IsPlaceExpr(receiver) && Pl(receiver) is { } owner && _b.TypeOf(owner).IsRef)
                    term.Args.Add(ToTemp(Read(owner.Deref()), receiver.Type, c.Syntax));
                else if (mode == ThisMode.Value)
                    term.Args.Add(ToTemp(Rv(receiver), receiver.Type, c.Syntax));
                else if (mode == ThisMode.Shared && receiver is BoundLiteral { ConstantValueOpt: { IsString: true } staticText })
                {
                    // `"a b".Split(' ')`: the literal is a 'static str in Rust, so nothing borrows a temporary.
                    var template = Temp(receiver.Type, c.Syntax);
                    _b.Locals[template.Local].IsStaticString = true;
                    Assign(template, new StaticStringRv { Value = staticText.StringValue }, c.Syntax);
                    receiverPlace = template;
                }
                else if (mode == ThisMode.Shared)
                    receiverPlace = ReadPl(receiver);
                else
                    receiverPlace = WritePl(receiver);
            }

            // Arguments first, then the receiver borrow, so `list.Add(list.Count)` type-checks the way
            // two-phase borrows do in Rust.
            var args = new CallTerm();
            bool wasReadOnly = _readOnlyPlace;
            _readOnlyPlace = false;
            AddArguments(args, m, c.Arguments, c.Syntax);
            _readOnlyPlace = wasReadOnly;

            if (receiverPlace != null)
            {
                var type = receiver.Type;
                var refMode = mode == ThisMode.Shared ? RefMode.Shared : RefMode.Mut;
                Place borrowed;
                MirType borrowType;
                if (type.IsReferenceType)
                {
                    borrowed = receiverPlace.Deref();
                    borrowType = new MirType(type, refMode, contents: true);
                }
                else
                {
                    borrowed = receiverPlace;
                    borrowType = new MirType(type, refMode);
                    term.ReceiverIsSlot = type.IsTypeParameter();
                }
                var t = Temp(borrowType, c.Syntax);
                Assign(t, new RefRv { Mode = refMode, Place = borrowed }, c.Syntax);
                term.Args.Add(Read(t));
            }

            term.Args.AddRange(args.Args);

            Place result = null;
            if (!m.ReturnsVoid)
            {
                result = Temp(new MirType(m.ReturnType, OwnershipFacts.ReturnMode(m)), c.Syntax);
                term.Dest = result;
            }

            term.Target = NewBlock();
            term.Unwind = m.IsExtern ? null : Unwind();
            _cur.Term ??= term;
            _cur = term.Target;
            return result;
        }

        private Operand FunctionPointerCall(BoundFunctionPointerInvocation f)
        {
            var sig = f.FunctionPointer.Signature;
            var term = new CallTerm { FnPtr = ToTemp(Rv(f.InvokedExpression), f.InvokedExpression.Type, f.Syntax), FnSignature = sig, Syntax = f.Syntax };
            AddArguments(term, sig, f.Arguments, f.Syntax);
            Place result = null;
            if (!sig.ReturnsVoid)
            {
                result = Temp(sig.ReturnType, f.Syntax);
                term.Dest = result;
            }
            term.Target = NewBlock();
            term.Unwind = Unwind();
            _cur.Term ??= term;
            _cur = term.Target;
            return result is null ? new ConstOp { Value = ConstantValue.Null } : Read(result);
        }

        private static bool IsAnonymousGetter(BoundCall c)
            => c.Method.MethodKind == MethodKind.PropertyGet && (c.Method.ContainingType.IsAnonymousType || OwnershipFacts.OwnedAutoPropertyField(c.Method) is not null);

        /// <summary>`==` on records borrows its operands: comparing must not consume them.</summary>
        private bool TryStructuralEquals(BoundCall c, out Operand result)
        {
            result = null;
            var m = c.Method.OriginalDefinition;
            BoundExpression left, right;
            bool negate = false;
            if (m is SynthesizedRecordEqualityOperatorBase)
            {
                left = c.Arguments[0];
                right = c.Arguments[1];
                negate = m.Name == WellKnownMemberNames.InequalityOperatorName;
            }
            else if (m is SynthesizedRecordEquals)
            {
                left = c.ReceiverOpt;
                right = c.Arguments[0];
            }
            else if (m.Name == nameof(object.Equals) && c.ReceiverOpt is { Type.IsAnonymousType: true } && c.Arguments.Length == 1)
            {
                left = c.ReceiverOpt;
                right = c.Arguments[0];
                while (right is BoundConversion { ConversionKind: ConversionKind.ImplicitReference } conv) right = conv.Operand;
            }
            else
            {
                return false;
            }

            var a = Pl(left);
            var b = Pl(right);
            var eq = Into(new StructEqRv { Left = a, Right = b, Type = left.Type }, c.Type, c.Syntax);
            result = negate ? Into(new UnaryRv { Op = UnaryOperatorKind.BoolLogicalNegation, Value = eq, OperandType = c.Type }, c.Type, c.Syntax) : eq;
            return true;
        }

        /// <summary>
        /// Anonymous types are read through their fields instead of Roslyn's generated getters: a getter
        /// borrows `this`, and could not hand out an owned member. Reading a field follows the normal
        /// rules, so a string is cloned and an object moves out of the anonymous value.
        /// </summary>
        private static FieldSymbol AnonymousField(NamedTypeSymbol type, string property)
        {
            var anonymous = (AnonymousTypeManager.AnonymousTypePublicSymbol)type;
            int index = anonymous.Properties.IndexOf(anonymous.Properties.First(p => p.Name == property));
            return OwnershipFacts.InstanceFields(AnonymousTypeManager.TranslateAnonymousTypeSymbol(type)).ElementAt(index);
        }

        private Place AnonymousCreation(BoundObjectCreationExpression o)
        {
            var type = (NamedTypeSymbol)o.Type;
            var args = new CallTerm();
            AddArguments(args, o.Constructor, o.Arguments, o.Syntax);
            var t = Temp(type, o.Syntax);
            Assign(t, new NewObjRv { Type = type }, o.Syntax);
            var properties = ((AnonymousTypeManager.AnonymousTypePublicSymbol)type).Properties;
            for (int i = 0; i < args.Args.Count; i++)
                Assign(t.Deref().Field(AnonymousField(type, properties[i].Name)), new UseRv { Op = args.Args[i] }, o.Syntax);
            return t;
        }

        private Place ObjectCreation(BoundObjectCreationExpression o)
        {
            var type = o.Type;
            if (type.IsAnonymousType) return AnonymousCreation(o);
            var t = Temp(type, o.Syntax);
            var ctor = o.Constructor;
            var term = new CallTerm { Method = ctor, Syntax = o.Syntax };
            var args = new CallTerm();

            if (type.IsReferenceType)
            {
                // Arguments are evaluated first: an object must not be observable before they ran.
                AddArguments(args, ctor, o.Arguments, o.Syntax);
                Assign(t, new NewObjRv { Type = type }, o.Syntax);
                var self = Temp(new MirType(type, RefMode.Mut, contents: true), o.Syntax);
                Assign(self, new RefRv { Mode = RefMode.Mut, Place = t.Deref() }, o.Syntax);
                term.Args.Add(Read(self));
            }
            else
            {
                AddArguments(args, ctor, o.Arguments, o.Syntax);
                Assign(t, new DefaultRv { Type = type, Alive = true }, o.Syntax);
                if (ctor.IsDefaultValueTypeConstructor()) return t;
                var self = Temp(new MirType(type, RefMode.Mut), o.Syntax);
                Assign(self, new RefRv { Mode = RefMode.Mut, Place = t }, o.Syntax);
                term.Args.Add(Read(self));
            }

            term.Args.AddRange(args.Args);
            term.Target = NewBlock();
            term.Unwind = Unwind();
            _cur.Term ??= term;
            _cur = term.Target;
            return t;
        }
    }
}
