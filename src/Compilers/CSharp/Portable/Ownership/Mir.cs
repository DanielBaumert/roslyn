// RustSharp: mid-level IR. A control-flow graph over places, modelled on rustc's MIR. Both the borrow
// checker and the LLVM backend consume it. Bodies stay generic; the backend monomorphizes them.

using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Text;
using Microsoft.CodeAnalysis.CSharp.Symbols;

namespace Microsoft.CodeAnalysis.CSharp.Ownership
{
    internal enum RefMode { None, Shared, Mut }

    /// <summary>
    /// A MIR-level type. A class-typed value is an owning handle; <see cref="Contents"/> is the object
    /// body behind that handle, so <c>this</c> in a class is a reference to Contents(C).
    /// </summary>
    internal sealed class MirType
    {
        public readonly TypeSymbol Type;
        public readonly RefMode Ref;
        public readonly bool Contents;

        public MirType(TypeSymbol type, RefMode refMode = RefMode.None, bool contents = false)
        {
            Type = type;
            Ref = refMode;
            Contents = contents;
        }

        public bool IsRef => Ref != RefMode.None;
        public MirType Pointee => new MirType(Type, RefMode.None, Contents);
        public override string ToString()
            => (Ref == RefMode.Mut ? "&mut " : Ref == RefMode.Shared ? "&" : "") + (Contents ? "contents " : "") + Type.ToDisplayString();
    }

    internal enum LocalKind { Return, Arg, User, Temp, ExceptionSlot }

    internal sealed class MirLocal
    {
        public int Index;
        public MirType Type;
        public LocalKind Kind;
        public string Name;
        public SyntaxNode Syntax;
        /// <summary>A user variable declared without `mut`.</summary>
        public bool Immutable;
        /// <summary>Holds a literal's template: borrowing it needs no loan, it lives forever.</summary>
        public bool IsStaticString;
        /// <summary>Where `mut` would go.</summary>
        public SyntaxToken MutSite;
        public override string ToString() => Name ?? "_" + Index;
    }

    internal abstract class Proj { }
    internal sealed class DerefProj : Proj { public static readonly DerefProj Instance = new DerefProj(); }
    internal sealed class FieldProj : Proj { public FieldSymbol Field; }
    internal sealed class IndexProj : Proj { public Operand[] Indices; }

    /// <summary>A memory location: a local or static plus a projection path.</summary>
    internal sealed class Place
    {
        public readonly int Local;
        public readonly FieldSymbol Static;
        public readonly ImmutableArray<Proj> Projs;

        public Place(int local, ImmutableArray<Proj> projs = default)
        {
            Local = local;
            Projs = projs.IsDefault ? ImmutableArray<Proj>.Empty : projs;
        }

        public Place(FieldSymbol staticField, ImmutableArray<Proj> projs = default)
        {
            Local = -1;
            Static = staticField;
            Projs = projs.IsDefault ? ImmutableArray<Proj>.Empty : projs;
        }

        private Place With(Proj p)
            => Static is null ? new Place(Local, Projs.Add(p)) : new Place(Static, Projs.Add(p));

        public Place Deref() => With(DerefProj.Instance);
        public Place Field(FieldSymbol f) => With(new FieldProj { Field = f });
        public Place Index(params Operand[] indices) => With(new IndexProj { Indices = indices });
        public bool IsLocal => Static is null && Projs.IsEmpty;
    }

    internal abstract class Operand { }
    internal sealed class CopyOp : Operand { public Place Place; }
    internal sealed class MoveOp : Operand { public Place Place; }
    internal sealed class ConstOp : Operand { public ConstantValue Value; public TypeSymbol Type; }

    internal abstract class Rvalue { }
    internal sealed class UseRv : Rvalue { public Operand Op; }
    /// <summary>A borrow. Creates a loan in the borrow checker.</summary>
    internal sealed class RefRv : Rvalue
    {
        public RefMode Mode;
        public Place Place;
        /// <summary>Downcast borrow for pattern variables: null unless the object is a <c>CastTo</c>.</summary>
        public TypeSymbol CastTo;
    }
    /// <summary>Unchecked <c>&amp;x</c>; the result is a raw pointer and carries no loan.</summary>
    internal sealed class AddrOfRv : Rvalue { public Place Place; }
    internal sealed class BinaryRv : Rvalue { public BinaryOperatorKind Op; public Operand Left, Right; public TypeSymbol OperandType; public TypeSymbol RightType; }
    internal sealed class UnaryRv : Rvalue { public UnaryOperatorKind Op; public Operand Value; public TypeSymbol OperandType; }
    internal sealed class ConvertRv : Rvalue { public Operand Value; public TypeSymbol From, To; public bool Checked; }
    /// <summary>Reference conversion. Upcasts are free, downcasts test the dynamic type.</summary>
    internal sealed class RefCastRv : Rvalue { public Operand Value; public TypeSymbol To; public bool Checked; public bool IsAs; }
    /// <summary>Non-consuming dynamic type test.</summary>
    internal sealed class IsInstRv : Rvalue { public Place Place; public TypeSymbol Target; }
    /// <summary>Compares a handle against null without consuming it.</summary>
    internal sealed class IsNullRv : Rvalue { public Place Place; }
    internal sealed class NewObjRv : Rvalue { public TypeSymbol Type; }
    /// <summary>The never-freed template of a string literal: Rust's &'static str as a receiver.</summary>
    internal sealed class StaticStringRv : Rvalue { public string Value; }
    /// <summary>typeof: a new System.Type naming the closed type.</summary>
    internal sealed class TypeOfRv : Rvalue { public TypeSymbol Type; }
    internal sealed class DefaultRv : Rvalue { public TypeSymbol Type; public bool Alive; }
    internal sealed class NewArrayRv : Rvalue { public TypeSymbol ArrayType; public Operand[] Lengths; }
    /// <summary>The length of one dimension of a multidimensional array.</summary>
    internal sealed class ArrayDimRv : Rvalue { public Place Array; public Operand Dimension; }
    /// <summary>A block of the current stack frame, zeroed or filled from <c>Init</c>; the result is a raw pointer.</summary>
    internal sealed class StackAllocRv : Rvalue { public TypeSymbol Element; public Operand Bytes; public List<Operand> Init; }
    internal sealed class ArrayLenRv : Rvalue { public Place Array; }
    internal sealed class BoxRv : Rvalue { public Operand Value; public TypeSymbol Type; }
    internal sealed class UnboxRv : Rvalue { public Operand Value; public TypeSymbol Type; }
    /// <summary>Reads the payload of a box without consuming the box. Only for Copy payloads.</summary>
    internal sealed class PeekBoxRv : Rvalue { public Place Place; public TypeSymbol Type; }
    /// <summary>Implicit clone of a string handle: read without moving, bump the refcount.</summary>
    internal sealed class RetainRv : Rvalue { public Place Place; }
    /// <summary>Structural equality; compares in place, like <c>PartialEq::eq(&amp;a, &amp;b)</c>.</summary>
    internal sealed class StructEqRv : Rvalue { public Place Left, Right; public TypeSymbol Type; }
    internal sealed class SizeOfRv : Rvalue { public TypeSymbol Type; }
    internal sealed class FnPtrRv : Rvalue { public MethodSymbol Method; }
    /// <summary>
    /// A delegate. <c>Target</c> is an owned receiver, <c>Borrowed</c> a receiver it merely points at. The
    /// borrows of what the closure uses arrive as <c>Captures</c>, so they flow into the delegate's region.
    /// </summary>
    internal sealed class NewDelegateRv : Rvalue
    {
        public TypeSymbol Type;
        public Operand Target;
        public Place Borrowed;
        public List<Operand> Captures;
        public List<TypeSymbol> CapturedTypes;
        public List<(TypeSymbol Type, RefMode Mode)> BorrowedTypes;
        public MethodSymbol Method;
        public SyntaxNode Syntax;
    }
    /// <summary>Stores a non-owning pointer, such as the link from a closure to its outer environment.</summary>
    internal sealed class LinkRv : Rvalue { public Place Source; }

    internal abstract class Statement { public SyntaxNode Syntax; }
    internal sealed class AssignStmt : Statement { public Place Dest; public Rvalue Value; }
    /// <summary>
    /// Runs drop glue on a place. Moved-from storage is zeroed, so dropping it is a runtime no-op.
    /// <see cref="ForAssign"/> marks the implicit drop of an assignment target, which the assignment
    /// itself already checks.
    /// </summary>
    internal sealed class DropStmt : Statement { public Place Place; public bool ForAssign; }
    internal sealed class StorageDeadStmt : Statement { public int Local; }

    internal abstract class Terminator
    {
        public SyntaxNode Syntax;
        public virtual IEnumerable<BasicBlock> Successors => Enumerable.Empty<BasicBlock>();
    }

    internal sealed class GotoTerm : Terminator
    {
        public BasicBlock Target;
        public override IEnumerable<BasicBlock> Successors => new[] { Target };
    }

    internal sealed class BranchTerm : Terminator
    {
        public Operand Cond;
        public BasicBlock IfTrue, IfFalse;
        public override IEnumerable<BasicBlock> Successors => new[] { IfTrue, IfFalse };
    }

    internal sealed class SwitchTerm : Terminator
    {
        public Operand Value;
        public TypeSymbol Type;
        public List<(ConstantValue Value, BasicBlock Target)> Cases = new List<(ConstantValue, BasicBlock)>();
        public BasicBlock Default;
        public override IEnumerable<BasicBlock> Successors => Cases.Select(c => c.Target).Append(Default);
    }

    /// <summary>
    /// A suspension point of a coroutine: `await` when it must wait, `yield return` when it hands out
    /// a value. To the borrow checker it is a plain edge, because the frame survives the suspension.
    /// </summary>
    internal sealed class SuspendTerm : Terminator
    {
        public BasicBlock Resume;
        public bool IsYield;
        public override IEnumerable<BasicBlock> Successors => new[] { Resume };
    }

    internal sealed class ReturnTerm : Terminator { }
    /// <summary>Continues unwinding in the caller with the exception in the exception slot.</summary>
    internal sealed class ResumeTerm : Terminator { }
    internal sealed class UnreachableTerm : Terminator { }

    internal sealed class ThrowTerm : Terminator
    {
        public Operand Value;
        public BasicBlock Unwind;
        public override IEnumerable<BasicBlock> Successors => new[] { Unwind };
    }

    /// <summary>
    /// Ends a block whose last statement can fault (null, bounds, division, cast, overflow), so that
    /// the path to the handler exists in the CFG, for the borrow checker as well as for code generation.
    /// </summary>
    internal sealed class FaultEdgeTerm : Terminator
    {
        public BasicBlock Target, Unwind;
        public override IEnumerable<BasicBlock> Successors => new[] { Target, Unwind };
    }

    internal sealed class CallTerm : Terminator
    {
        public Place Dest;              // null when the result is discarded
        public MethodSymbol Method;     // null for a function-pointer call
        public Operand FnPtr;
        public FunctionPointerMethodSymbol FnSignature;
        public List<Operand> Args = new List<Operand>();
        public bool Virtual;
        public bool ReceiverIsSlot;     // receiver of unconstrained generic type: a pointer to a T slot
        public TypeSymbol ConstrainedTo;
        public BasicBlock Target, Unwind;
        public override IEnumerable<BasicBlock> Successors
            => Unwind is null ? new[] { Target } : new[] { Target, Unwind };
    }

    internal sealed class BasicBlock
    {
        public int Index;
        public List<Statement> Statements = new List<Statement>();
        public Terminator Term;
        public bool IsCleanup;
    }

    internal sealed class MirBody
    {
        public MethodSymbol Method;
        public List<MirLocal> Locals = new List<MirLocal>();
        public List<BasicBlock> Blocks = new List<BasicBlock>();
        public int ArgCount;            // args occupy locals 1..ArgCount; local 0 is the return slot
        public int ExceptionSlot = -1;
        public int YieldSlot = -1;
        public SyntaxNode Syntax;

        /// <summary>Blocks reachable from the entry, in discovery order.</summary>
        public List<BasicBlock> Reachable()
        {
            var seen = new HashSet<BasicBlock>();
            var order = new List<BasicBlock>();
            var work = new Stack<BasicBlock>();
            work.Push(Blocks[0]);
            while (work.Count > 0)
            {
                var b = work.Pop();
                if (!seen.Add(b)) continue;
                order.Add(b);
                foreach (var s in b.Term.Successors.Reverse()) work.Push(s);
            }
            return order;
        }

        /// <summary>The type of a place, resolved step by step along its projections.</summary>
        public MirType TypeOf(Place p)
        {
            var t = p.Static is null ? Locals[p.Local].Type : new MirType(p.Static.Type, p.Static.RefKind == RefKind.None ? RefMode.None : RefMode.Mut);
            foreach (var proj in p.Projs) t = Project(t, proj);
            return t;
        }

        public static MirType Project(MirType t, Proj proj)
        {
            switch (proj)
            {
                case DerefProj:
                    if (t.IsRef) return t.Pointee;
                    if (t.Type is PointerTypeSymbol ptr) return new MirType(ptr.PointedAtType);
                    return new MirType(t.Type, RefMode.None, contents: true);
                case FieldProj f:
                    return new MirType(f.Field.Type, f.Field.RefKind == RefKind.None ? RefMode.None
                        : f.Field.RefKind == RefKind.RefReadOnly ? RefMode.Shared : RefMode.Mut);
                case IndexProj:
                    return new MirType(((ArrayTypeSymbol)t.Type).ElementType);
                default:
                    throw ExceptionUtilities.UnexpectedValue(proj);
            }
        }

        public static bool IsClosureEnvironment(TypeSymbol t) => t.OriginalDefinition is SynthesizedClosureEnvironment;

        public string Describe(Place p)
        {
            // Captured variables live in a closure environment; they read as themselves.
            if (p.Static is null && IsClosureEnvironment(Locals[p.Local].Type.Type))
            {
                var field = p.Projs.OfType<FieldProj>().FirstOrDefault();
                return field?.Field.Name ?? "captured variables";
            }

            var sb = new StringBuilder(p.Static is null ? Locals[p.Local].ToString() : p.Static.Name);
            var t = p.Static is null ? Locals[p.Local].Type : new MirType(p.Static.Type);
            foreach (var proj in p.Projs)
            {
                switch (proj)
                {
                    case FieldProj f: sb.Append('.').Append(f.Field.AssociatedSymbol?.Name ?? f.Field.Name); break;
                    case IndexProj: sb.Append("[..]"); break;
                }
                t = Project(t, proj);
            }
            return sb.ToString();
        }

        public override string ToString()
        {
            var sb = new StringBuilder();
            sb.Append("fn ").Append(Method.ToDisplayString()).Append(" {\n");
            foreach (var l in Locals)
                sb.Append($"    let _{l.Index}: {l.Type}; // {l.Kind} {l.Name}\n");
            foreach (var b in Reachable())
            {
                sb.Append($"  bb{b.Index}:{(b.IsCleanup ? " (cleanup)" : "")}\n");
                foreach (var s in b.Statements) sb.Append("    ").Append(Show(s)).Append('\n');
                sb.Append("    ").Append(Show(b.Term)).Append('\n');
            }
            return sb.Append("}\n").ToString();
        }

        private string Show(Place p)
        {
            var s = p.Static is null ? "_" + p.Local : p.Static.ToDisplayString();
            foreach (var proj in p.Projs)
                s = proj switch
                {
                    DerefProj => "(*" + s + ")",
                    FieldProj f => s + "." + f.Field.Name,
                    IndexProj i => s + "[" + string.Join(", ", i.Indices.Select(Show)) + "]",
                    _ => s
                };
            return s;
        }

        private string Show(Operand o) => o switch
        {
            CopyOp c => "copy " + Show(c.Place),
            MoveOp m => "move " + Show(m.Place),
            ConstOp k => "const " + (k.Value?.ToString() ?? "null"),
            _ => "?"
        };

        private string Show(Rvalue r) => r switch
        {
            UseRv u => Show(u.Op),
            RefRv x => (x.Mode == RefMode.Mut ? "&mut " : "&") + Show(x.Place),
            AddrOfRv a => "&raw " + Show(a.Place),
            BinaryRv b => $"{b.Op}({Show(b.Left)}, {Show(b.Right)})",
            UnaryRv u => $"{u.Op}({Show(u.Value)})",
            ConvertRv c => $"{Show(c.Value)} as {c.To.ToDisplayString()}",
            RefCastRv c => $"refcast {Show(c.Value)} as {c.To.ToDisplayString()}",
            IsInstRv i => $"{Show(i.Place)} is {i.Target.ToDisplayString()}",
            IsNullRv i => $"isnull {Show(i.Place)}",
            NewObjRv n => "alloc " + n.Type.ToDisplayString(),
            TypeOfRv t => "typeof " + t.Type.ToDisplayString(),
            StaticStringRv s => "static \"" + s.Value + "\"",
            DefaultRv d => "default " + d.Type.ToDisplayString(),
            NewArrayRv n => $"new {n.ArrayType.ToDisplayString()}[{string.Join(", ", n.Lengths.Select(Show))}]",
            ArrayDimRv a => $"dim {Show(a.Array)} {Show(a.Dimension)}",
            StackAllocRv a => $"stackalloc {Show(a.Bytes)}",
            ArrayLenRv a => "len " + Show(a.Array),
            BoxRv b => "box " + Show(b.Value),
            UnboxRv b => "unbox " + Show(b.Value),
            PeekBoxRv b => "peekbox " + Show(b.Place),
            RetainRv x => "retain " + Show(x.Place),
            StructEqRv e => $"eq {Show(e.Left)}, {Show(e.Right)}",
            SizeOfRv s => "sizeof " + s.Type.ToDisplayString(),
            FnPtrRv f => "fnptr " + f.Method.ToDisplayString(),
            NewDelegateRv d => $"delegate {d.Method.ToDisplayString()}({(d.Borrowed is null ? Show(d.Target) : "borrow " + Show(d.Borrowed))})",
            LinkRv l => "link " + Show(l.Source),
            _ => r.GetType().Name
        };

        private string Show(Statement s) => s switch
        {
            AssignStmt a => $"{Show(a.Dest)} = {Show(a.Value)}",
            DropStmt d => $"drop {Show(d.Place)}",
            StorageDeadStmt d => $"dead _{d.Local}",
            _ => "?"
        };

        private string Show(Terminator t) => t switch
        {
            GotoTerm g => $"goto bb{g.Target.Index}",
            BranchTerm b => $"if {Show(b.Cond)} bb{b.IfTrue.Index} else bb{b.IfFalse.Index}",
            SwitchTerm s => $"switch {Show(s.Value)} [{string.Join(", ", s.Cases.Select(c => c.Value + ": bb" + c.Target.Index))}, default: bb{s.Default.Index}]",
            FaultEdgeTerm f => $"goto bb{f.Target.Index} fault bb{f.Unwind.Index}",
            SuspendTerm x => $"{(x.IsYield ? "yield" : "suspend")} -> bb{x.Resume.Index}",
            ReturnTerm => "return",
            ResumeTerm => "resume",
            UnreachableTerm => "unreachable",
            ThrowTerm x => $"throw {Show(x.Value)} unwind bb{x.Unwind.Index}",
            CallTerm c => $"{(c.Dest is null ? "" : Show(c.Dest) + " = ")}{(c.Virtual ? "virtual " : "")}call {c.Method?.ToDisplayString() ?? "fnptr"}({string.Join(", ", c.Args.Select(Show))}) -> bb{c.Target.Index}{(c.Unwind is null ? "" : " unwind bb" + c.Unwind.Index)}",
            _ => "?"
        };
    }
}
