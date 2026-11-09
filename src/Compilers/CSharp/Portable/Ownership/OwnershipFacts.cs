// RustSharp: the type-level rules of the ownership model.

using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.CodeAnalysis.CSharp.Symbols;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Microsoft.CodeAnalysis.CSharp.Ownership
{
    /// <summary>How an instance method receives <c>this</c>.</summary>
    internal enum ThisMode { None, Shared, Mut, Value }

    /// <summary>The lifetime shape of a signature. Index 0 is <c>this</c> for instance methods.</summary>
    internal sealed class LifetimeSig
    {
        /// <summary>Lifetime per input, null when that input carries no borrow.</summary>
        public string[] Inputs;
        /// <summary>Lifetime of the result, null when the result carries no borrow.</summary>
        public string Output;
        /// <summary>The result may borrow from any input (no annotation could be derived).</summary>
        public bool OutputFromAll;
        public bool MissingSpecifier;
        /// <summary>Declared `where 'a : 'b` relations.</summary>
        public List<(string Longer, string Shorter)> Bounds = new List<(string, string)>();
        /// <summary>
        /// Lifetime parameters: per input, one name per slot of its type (<c>['a, 'b]</c> for <c>in Pair&lt;'a, 'b&gt;</c>),
        /// or null when the type declares no lifetimes. For `this`, the names the type declares.
        /// </summary>
        public string[][] InputSlots;
        /// <summary>One name per slot of the result's type, or null.</summary>
        public string[] OutputSlots;
        /// <summary>
        /// Inputs that are `out` or `ref` parameters which the callee fills with what it holds, such as
        /// Option's <c>Deconstruct(out T value)</c> behind the pattern <c>Some(var v)</c>: what lands there may
        /// come from any other input.
        /// </summary>
        public List<int> FilledFromInputs;
        /// <summary>Whether a name is the lifetime of some input's slot, such as <c>'a</c> in <c>First(in Pair&lt;'a, 'b&gt;)</c>.</summary>
        public bool IsSlotName(string name) => name != null && InputSlots != null && InputSlots.Any(s => s != null && System.Array.IndexOf(s, name) >= 0);
    }

    internal static class OwnershipFacts
    {
        private static readonly ConcurrentDictionary<TypeSymbol, bool> s_copy = new(Symbols.SymbolEqualityComparer.AllIgnoreOptions);
        private static readonly ConcurrentDictionary<TypeSymbol, bool> s_drop = new(Symbols.SymbolEqualityComparer.AllIgnoreOptions);

        public static bool IsString(TypeSymbol t) => t.SpecialType == SpecialType.System_String;

        public static MethodSymbol FindDestructor(TypeSymbol t)
            => t.GetMembers(WellKnownMemberNames.DestructorName).OfType<MethodSymbol>().FirstOrDefault(m => m.MethodKind == MethodKind.Destructor);

        public static IEnumerable<FieldSymbol> InstanceFields(NamedTypeSymbol t)
            => t.GetMembers().OfType<FieldSymbol>().Where(f => !f.IsStatic && !f.IsConst);

        /// <summary>A value of a Copy type can be duplicated by a bitwise copy; reading it never moves.</summary>
        public static bool IsCopy(TypeSymbol t)
        {
            switch (t.TypeKind)
            {
                case TypeKind.Enum:
                    return !IsUserType(t) || HasAttribute(t, "CopyAttribute");
                case TypeKind.Pointer:
                case TypeKind.FunctionPointer:
                    return true;
                case TypeKind.TypeParameter:
                    return ((TypeParameterSymbol)t).HasUnmanagedTypeConstraint;
                case TypeKind.Struct:
                    return s_copy.GetOrAdd(t, static x => ComputeStructCopy((NamedTypeSymbol)x));
                default:
                    return false;
            }
        }

        /// <summary>Set by the driver. User types follow Rust: Copy only with [Copy], like #[derive(Copy)].</summary>
        internal static System.Func<SyntaxTree, bool> IsUserTree;

        public static bool IsUserType(TypeSymbol t)
            => IsUserTree != null && t.OriginalDefinition.DeclaringSyntaxReferences.Any(r => IsUserTree(r.SyntaxTree));

        private static bool ComputeStructCopy(NamedTypeSymbol t)
        {
            if (FindDestructor(t) is not null) return false;
            if (IsUserType(t) && !HasAttribute(t, "CopyAttribute")) return false;
            if (t.IsRefLikeType && !t.IsReadOnly) return false;
            foreach (var f in InstanceFields(t))
            {
                if (f.RefKind == RefKind.Ref) return false;
                if (f.RefKind == RefKind.None && !Equals(f.Type, t) && !IsCopy(f.Type)) return false;
            }
            return true;
        }

        /// <summary>Whether a value may own resources. Conservatively true for open type parameters.</summary>
        public static bool NeedsDrop(TypeSymbol t)
        {
            switch (t.TypeKind)
            {
                case TypeKind.Enum:
                case TypeKind.Pointer:
                case TypeKind.FunctionPointer:
                    return false;
                case TypeKind.TypeParameter:
                    return !((TypeParameterSymbol)t).HasUnmanagedTypeConstraint;
                case TypeKind.Struct:
                    return s_drop.GetOrAdd(t, static x => FindDestructor(x) is not null
                        || InstanceFields((NamedTypeSymbol)x).Any(f => f.RefKind == RefKind.None && !Equals(f.Type, x) && NeedsDrop(f.Type)));
                default:
                    return true;
            }
        }

        // Send and Sync are auto traits: derived from a type's fields, except for types that state their
        // rule with [SendWhen] or [SyncWhen], which is the equivalent of `unsafe impl Send`.
        private const int BoundNever = 0, BoundAlways = 1, BoundSend = 2, BoundSync = 4;

        private static int? DeclaredBound(TypeSymbol t, string attribute)
        {
            var data = t.OriginalDefinition.GetAttributes().FirstOrDefault(a => a.AttributeClass?.Name == attribute);
            return data is null ? null : System.Convert.ToInt32(data.CommonConstructorArguments[0].ValueInternal);
        }

        private static bool ArgumentsSatisfy(TypeSymbol t, int bound, HashSet<TypeSymbol> seen)
        {
            if (bound == BoundNever) return false;
            if (bound == BoundAlways || t is not NamedTypeSymbol n) return true;
            foreach (var arg in n.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics)
            {
                if ((bound & BoundSend) != 0 && !IsThreadSafe(arg.Type, send: true, seen)) return false;
                if ((bound & BoundSync) != 0 && !IsThreadSafe(arg.Type, send: false, seen)) return false;
            }
            return true;
        }

        /// <summary>
        /// Whether a suspended coroutine may continue on another thread. Tasks inside it are skipped:
        /// each nested coroutine makes this decision for its own frame when it runs.
        /// </summary>
        public static bool IsFrameSend(IEnumerable<MirType> locals)
        {
            foreach (var t in locals)
            {
                if (t.Type.SpecialType == SpecialType.System_Void || IsCoroutineType(t.Type)) continue;
                if (t.Type.SpecialType == SpecialType.System_Object) continue; // the exception slot
                if (t.Type is PointerTypeSymbol { PointedAtType.SpecialType: SpecialType.System_Void }) continue;
                if (t.Contents || t.Ref == RefMode.Mut ? !IsSend(t.Type) : t.Ref == RefMode.Shared ? !IsSync(t.Type) : !IsSend(t.Type)) return false;
            }
            return true;
        }

        public static bool IsSend(TypeSymbol t) => IsThreadSafe(t, send: true, new HashSet<TypeSymbol>(Symbols.SymbolEqualityComparer.AllIgnoreOptions));
        public static bool IsSync(TypeSymbol t) => IsThreadSafe(t, send: false, new HashSet<TypeSymbol>(Symbols.SymbolEqualityComparer.AllIgnoreOptions));

        private static bool IsThreadSafe(TypeSymbol t, bool send, HashSet<TypeSymbol> seen)
        {
            if (t.TypeKind == TypeKind.Enum || t.SpecialType is not SpecialType.None and not SpecialType.System_Object) return t.TypeKind != TypeKind.Pointer;
            if (t.TypeKind is TypeKind.Pointer or TypeKind.FunctionPointer) return false;
            if (t is ArrayTypeSymbol array) return IsThreadSafe(array.ElementType, send, seen);
            // A closure may change what it captures, so calling one from two threads is never safe.
            if (t.IsDelegateType()) return send && HasAttribute(t, "SendAttribute");
            if (DeclaredBound(t, send ? "SendWhenAttribute" : "SyncWhenAttribute") is int bound) return ArgumentsSatisfy(t, bound, seen);

            // Like `dyn Trait`: nothing is known about the object behind it.
            if (t.SpecialType == SpecialType.System_Object || t.TypeKind == TypeKind.Interface) return false;
            if (t is not NamedTypeSymbol n || !seen.Add(t)) return true;

            for (var c = n; c is not null; c = c.BaseTypeNoUseSiteDiagnostics)
            {
                var fields = c.IsAnonymousType ? InstanceFields(AnonymousTypeManager.TranslateAnonymousTypeSymbol(c)) : InstanceFields(c);
                foreach (var f in fields)
                {
                    if (f.RefKind == RefKind.None && !IsThreadSafe(f.Type, send, seen)) return false;
                    if (f.RefKind != RefKind.None && !IsThreadSafe(f.Type, send && f.RefKind == RefKind.Ref, seen)) return false;
                }
            }
            return true;
        }

        /// <summary>The backing field read directly for an auto-property with an owned type, or null.</summary>
        public static FieldSymbol OwnedAutoPropertyField(MethodSymbol m)
        {
            if (m.MethodKind != MethodKind.PropertyGet || m.IsMetadataVirtual()) return null;
            if (m.OriginalDefinition.AssociatedSymbol is not SourcePropertySymbolBase { IsAutoProperty: true, BackingField: { } field }) return null;
            var type = m.ReturnType;
            return IsCopy(type) || IsString(type) || m.RefKind != RefKind.None ? null : field;
        }

        /// <summary>Record members that the backend generates structurally instead of Roslyn's bodies.</summary>
        public static bool IsGeneratedRecordMember(MethodSymbol m) => m is SynthesizedRecordClone or SynthesizedRecordCopyCtor or SynthesizedRecordEquals
            or SynthesizedRecordObjEquals or SynthesizedRecordBaseEquals or SynthesizedRecordGetHashCode or SynthesizedRecordToString
            or SynthesizedRecordPrintMembers or SynthesizedRecordEqualityOperatorBase
            || m.AssociatedSymbol is SynthesizedRecordEqualityContractProperty;

        public static bool HasAttribute(TypeSymbol t, string name)
            => t.OriginalDefinition.GetAttributes().Any(a => a.AttributeClass?.Name == name);

        /// <summary>A user implementation of IEq, IHash or IOrd, the equivalents of Rust's traits.</summary>
        public static MethodSymbol UserTrait(TypeSymbol t, string name, string member, bool generic)
        {
            if (t is not NamedTypeSymbol n) return null;
            foreach (var i in n.AllInterfacesNoUseSiteDiagnostics)
                if (i.Name == name && i.Arity == (generic ? 1 : 0) && (!generic || Equals(i.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics[0].Type, t)))
                    return t.FindImplementationForInterfaceMember(i.GetMembers(member).OfType<MethodSymbol>().First()) as MethodSymbol;
            return null;
        }

        /// <summary>The user's own <c>IClone&lt;T&gt;.Clone</c>, if any.</summary>
        public static MethodSymbol UserClone(TypeSymbol t)
        {
            if (t is not NamedTypeSymbol n) return null;
            foreach (var i in n.AllInterfacesNoUseSiteDiagnostics)
                if (i.Name == "IClone" && i.Arity == 1 && Equals(i.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics[0].Type, t))
                    return t.FindImplementationForInterfaceMember(i.GetMembers("Clone").OfType<MethodSymbol>().First()) as MethodSymbol;
            return null;
        }

        /// <summary>Whether a value can be duplicated: Copy, derived with [Clone], or implementing IClone.</summary>
        public static bool IsClone(TypeSymbol t)
        {
            if (IsCopy(t) || IsString(t)) return true;
            if (t is ArrayTypeSymbol a) return IsClone(a.ElementType);
            if (t.IsAnonymousType || t.IsRecord || t.IsRecordStruct || HasAttribute(t, "CloneAttribute")) return true;
            return UserClone(t) is not null;
        }

        /// <summary>Only references and ref structs can hold a borrow.</summary>
        public static bool CarriesBorrow(MirType t) => t.IsRef || IsBorrowHolder(t.Type);

        /// <summary>
        /// Types that can hold a borrow by value: ref structs, and delegates, which are C#'s closures. A
        /// delegate behaves like Rust's <c>Box&lt;dyn Fn() + 'a&gt;</c>: its lifetime is that of what it captures.
        /// </summary>
        public static bool IsBorrowHolder(TypeSymbol t) => t.IsRefLikeOrAllowsRefLikeType() || t.IsDelegateType() || IsCoroutineType(t)
            || IsReference(t) || CarriesBorrows(t) || HasLifetimeParameters(t);

        /// <summary>
        /// A class or struct that declares lifetimes, like Rust's <c>struct Index&lt;'a&gt;</c>: it may hold borrows in
        /// the fields that name them. A class is Rust's <c>Box&lt;Index&lt;'a&gt;&gt;</c>, its one owner keeps them alive.
        /// </summary>
        public static bool HasLifetimeParameters(TypeSymbol t)
            => t.TypeKind is TypeKind.Class or TypeKind.Struct && !Lifetimes.Declared(t).IsEmpty;

        /// <summary>Ref&lt;T&gt; and RefMut&lt;T&gt;: Rust's &amp;T and &amp;mut T as values, usable as type arguments.</summary>
        public static bool IsReference(TypeSymbol t) => t is NamedTypeSymbol && HasAttribute(t, "ReferenceAttribute");

        /// <summary>Whether a type is or contains a type parameter, which might stand for a reference.</summary>
        private static bool MentionsTypeParameter(TypeSymbol t) => t switch
        {
            TypeParameterSymbol => true,
            ArrayTypeSymbol a => MentionsTypeParameter(a.ElementType),
            NamedTypeSymbol n => n.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics.Any(a => MentionsTypeParameter(a.Type)),
            _ => false,
        };

        /// <summary>
        /// Result and Option may contain borrows, like Rust's Result&lt;&amp;T, &amp;E&gt;. Such a value has one lifetime,
        /// the one of what it borrows. Only an actual reference among the type arguments makes it one.
        /// </summary>
        public static bool CarriesBorrows(TypeSymbol t)
            => t is NamedTypeSymbol { IsGenericType: true } n && HasAttribute(n, "CarriesBorrowsAttribute")
                && n.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics.Any(a => IsBorrowHolder(a.Type));

        /// <summary>
        /// For signatures of generic code: a type parameter might stand for a reference, so a method that
        /// takes or returns one inside Result or Option (or a bare one in their own methods) passes it on.
        /// Bodies are checked with the type parameters as they are.
        /// </summary>
        private static bool MayCarry(MethodSymbol m, TypeSymbol t)
        {
            // The type's own parameters, and those of its generic methods (`Some<T>(T value)`, `MapOr<U>(U
            // fallback, ...)`): [CarriesBorrows] promises that such code only passes values on.
            if (t is TypeParameterSymbol tp)
                return m.ContainingType is { } ct && HasAttribute(ct, "CarriesBorrowsAttribute")
                    && (ReferenceEquals(tp.ContainingSymbol, ct.OriginalDefinition) || ReferenceEquals(tp.ContainingSymbol, m.OriginalDefinition));
            return t is NamedTypeSymbol { IsGenericType: true } n && HasAttribute(n, "CarriesBorrowsAttribute")
                && n.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics.Any(a => a.Type is TypeParameterSymbol || IsBorrowHolder(a.Type) || MayCarry(m, a.Type));
        }

        private static readonly ConcurrentDictionary<TypeSymbol, bool> s_coroutine = new(Symbols.SymbolEqualityComparer.AllIgnoreOptions);

        /// <summary>Tasks and generators are suspended code that can hold a borrow, like a Rust future.</summary>
        public static bool IsCoroutineType(TypeSymbol t)
        {
            if (t.TypeKind is not (TypeKind.Class or TypeKind.Interface or TypeKind.Struct)) return false;
            return s_coroutine.GetOrAdd(t.OriginalDefinition, static x =>
            {
                for (var c = x; c is not null; c = c.BaseTypeNoUseSiteDiagnostics)
                    if (HasAttribute(c, "BorrowHolderAttribute")) return true;
                return false;
            });
        }

        public static bool IsCoroutine(MethodSymbol m) => m.IsAsync || m.IsIterator;

        /// <summary>Rust's FnOnce: such a delegate may consume its captures, and calling it consumes it.</summary>
        public static bool IsOnceDelegate(TypeSymbol t) => t.IsDelegateType() && HasAttribute(t, "OnceAttribute");

        /// <summary>Rust's FnMut: such a delegate may change its captures, and calling it needs exclusive access.</summary>
        public static bool IsMutDelegate(TypeSymbol t) => t.IsDelegateType() && HasAttribute(t, "MutAttribute");

        public static bool IsClosureBody(MethodSymbol m) => m.OriginalDefinition is SynthesizedClosureMethod;

        /// <summary>What a coroutine's `return` produces: T for Task&lt;T&gt;, nothing otherwise.</summary>
        public static TypeSymbol CoroutineResult(MethodSymbol m, CSharpCompilation compilation)
        {
            if (m.IsAsync && !m.IsIterator && m.ReturnType is NamedTypeSymbol { Arity: 1 } task) return task.TypeArgumentsWithAnnotationsNoUseSiteDiagnostics[0].Type;
            return compilation.GetSpecialType(SpecialType.System_Void);
        }

        /// <summary>
        /// Whether dropping a value can observe the borrows it holds. Only a destructor can; a delegate
        /// merely releases what it owns, the equivalent of Rust's <c>#[may_dangle]</c>.
        /// </summary>
        public static bool DropUsesBorrows(TypeSymbol t)
        {
            if (t.IsDelegateType() || t is ArrayTypeSymbol || IsCoroutineType(t)) return false;
            if (t.TypeKind == TypeKind.TypeParameter) return ((TypeParameterSymbol)t).AllowsRefLikeType;
            // Rust's drop check: a value that holds borrows and has a destructor uses them when it is
            // dropped, so they must still be alive then. That is a ref struct, or a class or struct that
            // declares lifetimes.
            // Ref and RefMut are references: dropping one observes nothing (RefMut's empty destructor only
            // makes it move-only), as Rust's &T and &mut T have no Drop.
            if (IsReference(t)) return false;
            if (!t.IsRefLikeType && !HasLifetimeParameters(t)) return false;
            if (FindDestructor(t) is not null) return true;
            return t is NamedTypeSymbol n && InstanceFields(n).Any(f => f.RefKind == RefKind.None && !Equals(f.Type, t) && DropUsesBorrows(f.Type));
        }

        /// <summary>
        /// Fields of a closure environment that link to something the environment does not own: the
        /// enclosing scope's environment, or a captured <c>this</c>.
        /// </summary>
        public static bool IsLinkField(FieldSymbol f)
            => f.ContainingType.OriginalDefinition is SynthesizedClosureEnvironment && (f.Type.OriginalDefinition is SynthesizedClosureEnvironment || f.Name == GeneratedNames.ThisProxyFieldName());

        private static SyntaxTokenList ModifiersOf(MethodSymbol m)
        {
            var decl = m.OriginalDefinition.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
            return decl switch
            {
                BaseMethodDeclarationSyntax x => x.Modifiers,
                AccessorDeclarationSyntax x => x.Modifiers,
                _ => default
            };
        }

        public static ThisMode GetThisMode(MethodSymbol m)
        {
            if (m.IsStatic) return ThisMode.None;
            if (m.MethodKind is MethodKind.Constructor or MethodKind.Destructor) return ThisMode.Mut;
            if (m.OriginalDefinition is SynthesizedRecordClone or SynthesizedRecordObjectMethod or SynthesizedRecordEquals or SynthesizedRecordObjEquals or SynthesizedRecordBaseEquals)
                return ThisMode.Shared;

            // Destructuring moves owned members out, like a `let` pattern in Rust.
            if (m.OriginalDefinition is SynthesizedRecordDeconstruct)
                return InstanceFields(m.ContainingType).All(f => IsCopy(f.Type) || IsString(f.Type)) ? ThisMode.Shared : ThisMode.Value;

            var mods = ModifiersOf(m);
            foreach (var t in mods)
            {
                if (t.IsKind(SyntaxKind.MoveKeyword)) return ThisMode.Value;
                if (t.IsKind(SyntaxKind.ReadOnlyKeyword)) return ThisMode.Shared;
            }

            if (m.MethodKind == MethodKind.PropertyGet) return m.RefKind == RefKind.Ref ? ThisMode.Mut : ThisMode.Shared;
            if (m.AssociatedSymbol is PropertySymbol { } p && m.MethodKind == MethodKind.PropertySet) return ThisMode.Mut;
            if (m.ContainingType.IsReadOnly) return ThisMode.Shared;
            if (m.ContainingType.IsDelegateType())
                return IsOnceDelegate(m.ContainingType) ? ThisMode.Value : IsMutDelegate(m.ContainingType) ? ThisMode.Mut : ThisMode.Shared;
            return ThisMode.Mut;
        }

        public static RefMode ParamMode(ParameterSymbol p) => p.RefKind switch
        {
            RefKind.None => RefMode.None,
            RefKind.In or RefKind.RefReadOnlyParameter => RefMode.Shared,
            _ => RefMode.Mut
        };

        public static RefMode ReturnMode(MethodSymbol m) => m.RefKind switch
        {
            RefKind.None => RefMode.None,
            RefKind.RefReadOnly => RefMode.Shared,
            _ => RefMode.Mut
        };

        private static readonly ConcurrentDictionary<MethodSymbol, LifetimeSig> s_sigs = new(Symbols.SymbolEqualityComparer.AllIgnoreOptions);

        public static LifetimeSig GetLifetimeSig(MethodSymbol method)
            => s_sigs.GetOrAdd(method.OriginalDefinition, static m => ElideOutputSlots(ComputeSig(m)));

        /// <summary>A delegate's Invoke signature for a lambda body: the environment takes the place of the delegate.</summary>
        private static LifetimeSig ForLambda(LifetimeSig invoke, LifetimeSig own, bool isStatic)
        {
            int skip = isStatic ? 1 : 0;
            var inputs = invoke.Inputs.Skip(skip).ToArray();
            var slots = invoke.InputSlots?.Skip(skip).Select(x => (string[])x?.Clone()).ToArray() ?? new string[inputs.Length][];
            // `this` is the lambda's own: its environment, or the object whose method it lives in, with
            // that object's lifetimes. Only the parameters and the result follow Invoke.
            if (!isStatic && own.Inputs.Length > 0 && inputs.Length > 0)
            {
                inputs[0] = own.Inputs[0];
                slots[0] = own.InputSlots?[0];
            }
            return new LifetimeSig
            {
                Inputs = inputs,
                InputSlots = slots,
                Output = invoke.Output,
                OutputSlots = (string[])invoke.OutputSlots?.Clone(),
                OutputFromAll = invoke.OutputFromAll,
                MissingSpecifier = false,
                Bounds = new List<(string, string)>(invoke.Bounds),
            };
        }

        /// <summary>The name of an output slot that is simply the lifetime of the whole result.</summary>
        public const string WholeResult = "'#result";

        /// <summary>
        /// Rust's elision for lifetimes in the result's type: an elided one is the lifetime the result
        /// comes from. Where that is not a plain lifetime ('#data, '#self, or from all inputs), the slot is
        /// the lifetime of the whole result, which is what it was before lifetime parameters.
        /// </summary>
        private static LifetimeSig ElideOutputSlots(LifetimeSig sig)
        {
            if (sig.OutputSlots is not { } slots) return sig;
            bool plain = sig.Output != null && !sig.Output.StartsWith("'#data", System.StringComparison.Ordinal) && sig.Output != "'#self";
            for (int k = 0; k < slots.Length; k++)
                if (slots[k].StartsWith("'#elided", System.StringComparison.Ordinal)) slots[k] = plain ? sig.Output : WholeResult;
            return sig;
        }

        private static string ExplicitLifetime(SyntaxTokenList mods)
        {
            foreach (var t in mods)
                if (t.IsKind(SyntaxKind.LifetimeToken)) return t.ValueText;
            return null;
        }

        private static LifetimeSig ComputeSig(MethodSymbol m)
        {
            var inputs = new List<string>();
            var scoped = new List<bool>();
            var decl = m.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
            var paramList = (decl as BaseMethodDeclarationSyntax)?.ParameterList ?? (decl as DelegateDeclarationSyntax)?.ParameterList;
            var returnSyntax = (decl as MethodDeclarationSyntax)?.ReturnType ?? (decl as DelegateDeclarationSyntax)?.ReturnType;

            var thisMode = GetThisMode(m);
            bool thisBorrows = thisMode is ThisMode.Shared or ThisMode.Mut;
            if (!m.IsStatic)
            {
                inputs.Add(thisBorrows || IsBorrowHolder(m.ContainingType) || MayCarry(m, m.ContainingType) ? "'#this" : null);
                scoped.Add(false);
            }

            // A container such as List<T> may hold references; a value it stores lives in its content,
            // the lifetime called '#self, which is not the borrow of `this` for the call.
            bool container = !m.IsStatic && thisBorrows && HasAttribute(m.ContainingType, "CarriesBorrowsAttribute");

            for (int i = 0; i < m.ParameterCount; i++)
            {
                var p = m.Parameters[i];
                bool borrow = p.RefKind != RefKind.None || IsBorrowHolder(p.Type) || MayCarry(m, p.Type);
                if (container && p.RefKind == RefKind.None && !IsBorrowHolder(p.Type) && MayCarry(m, p.Type))
                {
                    inputs.Add("'#self");
                    scoped.Add(false);
                    continue;
                }
                string name = null;
                if (paramList != null && i < paramList.Parameters.Count)
                    name = ExplicitLifetime(paramList.Parameters[i].Modifiers);
                inputs.Add(borrow ? name ?? "'#" + i : null);
                scoped.Add(p.EffectiveScope != ScopedKind.None);
            }

            var sig = new LifetimeSig { Inputs = inputs.ToArray() };

            // Lifetime parameters of the inputs' and the result's types, one name per slot.
            sig.InputSlots = new string[sig.Inputs.Length][];
            int first = m.IsStatic ? 0 : 1;
            if (!m.IsStatic && Lifetimes.Declared(m.ContainingType) is { IsEmpty: false } own) sig.InputSlots[0] = own.ToArray();
            for (int i = 0; i < m.ParameterCount; i++)
            {
                var typeSyntax = paramList != null && i < paramList.Parameters.Count ? paramList.Parameters[i].Type : null;
                sig.InputSlots[first + i] = Lifetimes.Slots(m.Parameters[i].Type, typeSyntax, i.ToString());
            }
            sig.OutputSlots = Lifetimes.Slots(m.ReturnType, returnSyntax, "ret");

            // A container's generic code is trusted, not checked: an `out T` it fills carries its content.
            for (int i = 0; i < m.ParameterCount; i++)
                if (m.Parameters[i].RefKind is RefKind.Out or RefKind.Ref && MayCarry(m, m.Parameters[i].Type))
                    (sig.FilledFromInputs ??= new List<int>()).Add(first + i);

            // A value of a type with one lifetime, such as Ref<'a, T>, lives exactly as long as that
            // lifetime: `Ref<'a, int> x` is an input named 'a, like Rust's `x: &'a i32`.
            for (int i = first; i < sig.Inputs.Length; i++)
                if (sig.InputSlots[i] is { Length: 1 } one && !one[0].StartsWith("'#", System.StringComparison.Ordinal) && sig.Inputs[i] == "'#" + (i - first))
                    sig.Inputs[i] = one[0];

            // The parser keeps `where 'a : 'b` as skipped tokens behind the parameter list.
            if (paramList != null)
            {
                var names = new List<string>();
                foreach (var trivia in paramList.GetTrailingTrivia())
                    if (trivia.IsKind(SyntaxKind.SkippedTokensTrivia))
                        foreach (var token in ((SkippedTokensTriviaSyntax)trivia.GetStructure()).Tokens)
                            if (token.IsKind(SyntaxKind.LifetimeToken)) names.Add(token.ValueText);
                for (int i = 0; i + 1 < names.Count; i += 2) sig.Bounds.Add((names[i], names[i + 1]));
            }

            // A ref-struct constructor stores its arguments: they all share the lifetime of `this`. With
            // lifetime parameters, an argument named after one (`ref readonly 'a int x`) goes to that slot.
            if (m.MethodKind == MethodKind.Constructor && IsBorrowHolder(m.ContainingType))
            {
                var slots = sig.InputSlots[0];
                for (int i = 0; i < sig.Inputs.Length; i++)
                    if (sig.Inputs[i] != null && (slots is null || System.Array.IndexOf(slots, sig.Inputs[i]) < 0)) sig.Inputs[i] = "'#this";
                return sig;
            }

            // A ref struct's own generic result (an iterator's `Option<T> Next()`, an enumerator's `T Current`)
            // may be a reference for some T, and then it points at what the ref struct borrows.
            bool genericFromRefStruct = !m.ReturnsVoid && m.ContainingType.IsRefLikeType && MentionsTypeParameter(m.ReturnType);
            bool returnsBorrow = m.RefKind != RefKind.None || (!m.ReturnsVoid && (IsBorrowHolder(m.ReturnType) || MayCarry(m, m.ReturnType))) || genericFromRefStruct;
            if (!returnsBorrow) return sig;

            // Delegates: a caller of Invoke cannot see where a lambda's result comes from, so it binds the
            // result to every input, the delegate included (for a [Mut] one, its exclusive borrow). A lambda's
            // body may then return a borrow of any of them: its captures, or the data behind an argument,
            // as in `OrderBy(s => s)` on Ref<string> items. Both sides agree, as Rust's closure signatures do.
            // A delegate type that declares lifetimes says where the result comes from, like Rust's
            // `for<'a> Fn(&'a i32) -> &'a i32`: its Invoke is computed like any method, and a lambda body
            // converted to it must keep exactly that signature, so it cannot return its captures instead.
            if (IsClosureBody(m) && Lifetimes.TargetDelegate(m) is { DelegateInvokeMethod: { } invoke } target && Lifetimes.DelegateDeclaresLifetimes(target))
                return ForLambda(GetLifetimeSig(invoke), sig, m.IsStatic);
            if (IsClosureBody(m) || (m.MethodKind == MethodKind.DelegateInvoke && !Lifetimes.DelegateDeclaresLifetimes(m.ContainingType)))
            {
                sig.OutputFromAll = true;
                return sig;
            }

            // A value taken out of a container (Pop, Remove, Clone) carries its content, not a borrow of it.
            if (container && m.RefKind == RefKind.None && !IsBorrowHolder(m.ReturnType) && MayCarry(m, m.ReturnType))
            {
                sig.Output = "'#self";
                return sig;
            }

            // Iterator adapters: `move` on a borrow holder keeps every input alive in the result.
            if (thisMode == ThisMode.Value && (IsBorrowHolder(m.ContainingType) || MayCarry(m, m.ContainingType)))
            {
                sig.OutputFromAll = true;
                return sig;
            }

            string explicitOut = null;
            if (decl is MethodDeclarationSyntax or DelegateDeclarationSyntax)
            {
                explicitOut = (returnSyntax as RefTypeSyntax)?.LifetimeToken.ValueText;
                if (string.IsNullOrEmpty(explicitOut) && decl is MethodDeclarationSyntax md) explicitOut = ExplicitLifetime(md.Modifiers);
                // `Ref<'a, int> Pick(...)`: a result of a type with one named lifetime lives for it.
                if (string.IsNullOrEmpty(explicitOut) && sig.OutputSlots is { Length: 1 } one && !one[0].StartsWith("'#", System.StringComparison.Ordinal))
                    explicitOut = one[0];
            }

            if (!string.IsNullOrEmpty(explicitOut))
            {
                sig.Output = explicitOut;
                return sig;
            }

            if (decl is null)
            {
                sig.OutputFromAll = true;
                return sig;
            }

            // A ref struct or Ref cannot return a reference to its own fields (C# forbids it), so a
            // reference it returns points at what it borrows: Rust's `fn next(&mut self) -> &'a T`.
            // Not with a destructor: a guard releases what it guards, so its references end with it.
            if (!m.IsStatic && thisBorrows && (m.RefKind != RefKind.None || IsBorrowHolder(m.ReturnType) || genericFromRefStruct)
                && (m.ContainingType.IsRefLikeType || IsReference(m.ContainingType)) && FindDestructor(m.ContainingType) is null)
            {
                // With further borrowed inputs (`text.Split(separator)`) the result borrows those too.
                sig.Output = m.RefKind == RefKind.None && sig.Inputs.Skip(1).Any(x => x != null) ? "'#data+" : "'#data";
                return sig;
            }

            // Elision: `this` first, then the only unscoped borrowed input.
            if (!m.IsStatic && thisBorrows)
            {
                sig.Output = sig.Inputs[0];
                return sig;
            }

            var candidates = Enumerable.Range(0, sig.Inputs.Length).Where(i => sig.Inputs[i] != null && !scoped[i]).ToList();
            if (candidates.Count == 1)
            {
                sig.Output = sig.Inputs[candidates[0]];
            }
            else if (candidates.Select(i => sig.Inputs[i]).Distinct().Count() == 1 && candidates.Count > 0)
            {
                sig.Output = sig.Inputs[candidates[0]];
            }
            else
            {
                sig.MissingSpecifier = candidates.Count > 1;
                sig.OutputFromAll = true;
            }

            return sig;
        }
    }
}
