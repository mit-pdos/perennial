/-
`Pos.Countable` instances for Go types and GooseLang syntax. Port of the
`Countable` instances of `src/goose_lang/lang.v` (`enc_val`/`dec_val`) and
`new/golang/defn`.

As in Rocq, each syntax type is injected into generic trees (`GenTree`, stdpp
`gen_tree`); injectivity is proved directly instead of through a decoder.
These instances let ghost state (channels, `ghost_var`, ...) store values that
contain code: `val`, `expr`, `func.t`, `interface.t`, `slice.t`, `loc`, ...
-/
import Perennial.GooseLang.Lang

noncomputable section

namespace Perennial
open GenTree

/-! ## Go types -/

set_option hygiene false in
/-- The core of an injectivity proof `h : a.toTree = b.toTree ⊢ a = b`, for a fixed constructor
of `a`: case on `b`; `injection h` (which unfolds `toTree` by `whnf`) splits `h` into the
equality `h0` of the node tags, refuted by `contradiction` for mismatched constructors, and the
equality `h` of the children, which `simp only` turns into a conjunction (and the goal into the
conjunction of the equalities of the constructor arguments, with their `injEq` lemmas `ls`).
This needs neither the equation lemmas of the `toTree` functions nor `simp` with the default
simp set, both slow on these large mutual inductives. -/
local macro "inj_cases " b:ident " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (cases $b:ident <;> injection h with h0 h <;> first
    | contradiction
    | (try simp only [List.cons.injEq, GenTree.leaf.injEq, Pos.encode_eq_iff, and_true,
        Option.some.injEq, Prod.mk.injEq, $ls,*] at h ⊢)))

set_option hygiene false in
/-- `inj_cases` for the Go types. -/
local macro "inj_ty " b:ident : tactic => `(tactic| inj_cases $b:ident [
    go.type.Named.injEq, go.type.ArrayType.injEq, go.type.StructType.injEq,
    go.type.PointerType.injEq, go.type.FunctionType.injEq, go.type.InterfaceType.injEq,
    go.type.SliceType.injEq, go.type.MapType.injEq, go.type.ChannelType.injEq,
    go.type.UntypedType.injEq, go.field_decl.FieldDecl.injEq, go.field_decl.EmbeddedField.injEq,
    go.signature.Signature.injEq, go.interface_elem.MethodElem.injEq,
    go.interface_elem.TypeElem.injEq, go.type_term.TypeTerm.injEq,
    go.type_term.TypeTermUnderlying.injEq])

namespace go

mutual
def type.toTree : type → GenTree
  | .Named n args => node 0 [of n, typesToTree args]
  | .ArrayType n t => node 1 [of n, t.toTree]
  | .StructType fs => node 2 [fieldsToTree fs]
  | .PointerType t => node 3 [t.toTree]
  | .FunctionType s => node 4 [s.toTree]
  | .InterfaceType es => node 5 [elemsToTree es]
  | .SliceType t => node 6 [t.toTree]
  | .MapType k v => node 7 [k.toTree, v.toTree]
  | .ChannelType d t => node 8 [d.toTree, t.toTree]
  | .UntypedType n => node 9 [of n]
def chan_dir.toTree : chan_dir → GenTree
  | .sendrecv => node 0 []
  | .sendonly => node 1 []
  | .recvonly => node 2 []
def field_decl.toTree : field_decl → GenTree
  | .FieldDecl n t => node 0 [of n, t.toTree]
  | .EmbeddedField n t => node 1 [of n, t.toTree]
def signature.toTree : signature → GenTree
  | .Signature ps v rs => node 0 [typesToTree ps, of v, typesToTree rs]
def interface_elem.toTree : interface_elem → GenTree
  | .MethodElem n s => node 0 [of n, s.toTree]
  | .TypeElem ts => node 1 [terms_toTree ts]
def type_term.toTree : type_term → GenTree
  | .TypeTerm t => node 0 [t.toTree]
  | .TypeTermUnderlying t => node 1 [t.toTree]
def typesToTree : List type → GenTree
  | [] => node 0 []
  | t :: ts => node 1 [t.toTree, typesToTree ts]
def fieldsToTree : List field_decl → GenTree
  | [] => node 0 []
  | t :: ts => node 1 [t.toTree, fieldsToTree ts]
def elemsToTree : List interface_elem → GenTree
  | [] => node 0 []
  | t :: ts => node 1 [t.toTree, elemsToTree ts]
def terms_toTree : List type_term → GenTree
  | [] => node 0 []
  | t :: ts => node 1 [t.toTree, terms_toTree ts]
end

mutual
theorem type.toTree_inj : ∀ {a b : type}, a.toTree = b.toTree → a = b
  | .Named n a, b, h => by inj_ty b; exact ⟨h.1, typesToTree_inj h.2⟩
  | .ArrayType n t, b, h => by inj_ty b; exact ⟨h.1, type.toTree_inj h.2⟩
  | .StructType fs, b, h => by inj_ty b; exact fieldsToTree_inj h
  | .PointerType t, b, h => by inj_ty b; exact type.toTree_inj h
  | .FunctionType s, b, h => by inj_ty b; exact signature.toTree_inj h
  | .InterfaceType es, b, h => by inj_ty b; exact elemsToTree_inj h
  | .SliceType t, b, h => by inj_ty b; exact type.toTree_inj h
  | .MapType k v, b, h => by inj_ty b; exact ⟨type.toTree_inj h.1, type.toTree_inj h.2⟩
  | .ChannelType d t, b, h => by inj_ty b; exact ⟨chan_dir.toTree_inj h.1, type.toTree_inj h.2⟩
  | .UntypedType n, b, h => by inj_ty b; exact h
termination_by structural a _ _ => a
theorem chan_dir.toTree_inj : ∀ {a b : chan_dir}, a.toTree = b.toTree → a = b
  | a, b, h => by cases a <;> cases b <;> first | rfl | (injection h with h0 h; contradiction)
theorem field_decl.toTree_inj : ∀ {a b : field_decl}, a.toTree = b.toTree → a = b
  | .FieldDecl n t, b, h => by inj_ty b; exact ⟨h.1, type.toTree_inj h.2⟩
  | .EmbeddedField n t, b, h => by inj_ty b; exact ⟨h.1, type.toTree_inj h.2⟩
termination_by structural a _ _ => a
theorem signature.toTree_inj : ∀ {a b : signature}, a.toTree = b.toTree → a = b
  | .Signature ps v rs, b, h => by
    inj_ty b; exact ⟨typesToTree_inj h.1, h.2.1, typesToTree_inj h.2.2⟩
termination_by structural a _ _ => a
theorem interface_elem.toTree_inj : ∀ {a b : interface_elem}, a.toTree = b.toTree → a = b
  | .MethodElem n s, b, h => by inj_ty b; exact ⟨h.1, signature.toTree_inj h.2⟩
  | .TypeElem ts, b, h => by inj_ty b; exact terms_toTree_inj h
termination_by structural a _ _ => a
theorem type_term.toTree_inj : ∀ {a b : type_term}, a.toTree = b.toTree → a = b
  | .TypeTerm t, b, h => by inj_ty b; exact type.toTree_inj h
  | .TypeTermUnderlying t, b, h => by inj_ty b; exact type.toTree_inj h
termination_by structural a _ _ => a
theorem typesToTree_inj : ∀ {a b : List type}, typesToTree a = typesToTree b → a = b
  | [], b, h => by inj_ty b
  | t :: ts, b, h => by inj_ty b; exact ⟨type.toTree_inj h.1, typesToTree_inj h.2⟩
termination_by structural a _ _ => a
theorem fieldsToTree_inj : ∀ {a b : List field_decl}, fieldsToTree a = fieldsToTree b → a = b
  | [], b, h => by inj_ty b
  | t :: ts, b, h => by inj_ty b; exact ⟨field_decl.toTree_inj h.1, fieldsToTree_inj h.2⟩
termination_by structural a _ _ => a
theorem elemsToTree_inj : ∀ {a b : List interface_elem}, elemsToTree a = elemsToTree b → a = b
  | [], b, h => by inj_ty b
  | t :: ts, b, h => by inj_ty b; exact ⟨interface_elem.toTree_inj h.1, elemsToTree_inj h.2⟩
termination_by structural a _ _ => a
theorem terms_toTree_inj : ∀ {a b : List type_term}, terms_toTree a = terms_toTree b → a = b
  | [], b, h => by inj_ty b
  | t :: ts, b, h => by inj_ty b; exact ⟨type_term.toTree_inj h.1, terms_toTree_inj h.2⟩
termination_by structural a _ _ => a
end

instance type.countable : Pos.Countable type := countableOfTree type.toTree type.toTree_inj

end go

/-! ## Locations, slices and base literals -/

instance loc.countable : Pos.Countable loc :=
  countableOfLeftInverse (fun l : loc => (l.locCar, l.locOff)) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl)

instance slice.countable : Pos.Countable slice.t :=
  countableOfLeftInverse (fun s : slice.t => (s.ptr, s.len, s.cap)) (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (fun _ => rfl)

instance binder.countable : Pos.Countable binder :=
  countableOfLeftInverse (fun b : binder => match b with | .BAnon => none | .BNamed s => some s)
    (fun | none => .BAnon | some s => .BNamed s) (by intro b; cases b <;> rfl)

private local instance : Inhabited PrimOp0 := ⟨.ArbitraryIntOp⟩
private local instance : Inhabited go_operator := ⟨.GoEquals⟩
private local instance : Inhabited go_unary_operator := ⟨.GoPos⟩
private local instance : Inhabited go_instruction := ⟨.AngelicExit⟩

def PrimOp1.toNat : PrimOp1 → Nat
  | .PrepareWriteOp => 0
  | .StartReadOp => 1
  | .FinishReadOp => 2
  | .LoadOp => 3
  | .AllocOp => 4
def PrimOp1.fromNat : Nat → PrimOp1
  | 0 => .PrepareWriteOp
  | 1 => .StartReadOp
  | 2 => .FinishReadOp
  | 3 => .LoadOp
  | 4 => .AllocOp
  | _ => .PrepareWriteOp
instance PrimOp1.countable : Pos.Countable PrimOp1 :=
  countableOfLeftInverse PrimOp1.toNat PrimOp1.fromNat (by intro x; cases x <;> rfl)

def PrimOp2.toNat : PrimOp2 → Nat
  | .FinishStoreOp => 0
  | .AtomicSwapOp => 1
  | .AtomicAddOp => 2
def PrimOp2.fromNat : Nat → PrimOp2
  | 0 => .FinishStoreOp
  | 1 => .AtomicSwapOp
  | 2 => .AtomicAddOp
  | _ => .FinishStoreOp
instance PrimOp2.countable : Pos.Countable PrimOp2 :=
  countableOfLeftInverse PrimOp2.toNat PrimOp2.fromNat (by intro x; cases x <;> rfl)

def go_operator.toNat : go_operator → Nat
  | .GoEquals => 0
  | .GoLt => 1
  | .GoLe => 2
  | .GoGt => 3
  | .GoGe => 4
  | .GoPlus => 5
  | .GoSub => 6
  | .GoMul => 7
  | .GoDiv => 8
  | .GoRemainder => 9
  | .GoAnd => 10
  | .GoOr => 11
  | .GoXor => 12
  | .GoBitClear => 13
  | .GoShiftl => 14
  | .GoShiftr => 15
def go_operator.fromNat : Nat → go_operator
  | 0 => .GoEquals
  | 1 => .GoLt
  | 2 => .GoLe
  | 3 => .GoGt
  | 4 => .GoGe
  | 5 => .GoPlus
  | 6 => .GoSub
  | 7 => .GoMul
  | 8 => .GoDiv
  | 9 => .GoRemainder
  | 10 => .GoAnd
  | 11 => .GoOr
  | 12 => .GoXor
  | 13 => .GoBitClear
  | 14 => .GoShiftl
  | 15 => .GoShiftr
  | _ => .GoEquals
instance go_operator.countable : Pos.Countable go_operator :=
  countableOfLeftInverse go_operator.toNat go_operator.fromNat (by intro x; cases x <;> rfl)

def go_unary_operator.toNat : go_unary_operator → Nat
  | .GoPos => 0
  | .GoNeg => 1
  | .GoNot => 2
  | .GoComplement => 3
def go_unary_operator.fromNat : Nat → go_unary_operator
  | 0 => .GoPos
  | 1 => .GoNeg
  | 2 => .GoNot
  | 3 => .GoComplement
  | _ => .GoPos
instance go_unary_operator.countable : Pos.Countable go_unary_operator :=
  countableOfLeftInverse go_unary_operator.toNat go_unary_operator.fromNat (by intro x; cases x <;> rfl)

def PrimOp0.toTree : PrimOp0 → GenTree
  | .PanicOp x0 => node 0 [of x0]
  | .ArbitraryIntOp => node 1 []
def PrimOp0.ofTree : GenTree → PrimOp0
  | node 0 [x0] => .PanicOp (decLeaf x0)
  | node 1 [] => .ArbitraryIntOp
  | _ => default
instance PrimOp0.countable : Pos.Countable PrimOp0 :=
  countableOfLeftInverse PrimOp0.toTree PrimOp0.ofTree
    (by intro x; cases x <;> (conv => lhs; whnf) <;> simp only [decLeaf_of])

def BaseLit.toTree : BaseLit → GenTree
  | .LitInt x0 => node 0 [of x0]
  | .LitInt32 x0 => node 1 [of x0]
  | .LitInt16 x0 => node 2 [of x0]
  | .LitBool x0 => node 3 [of x0]
  | .LitByte x0 => node 4 [of x0]
  | .LitString x0 => node 5 [of x0]
  | .LitUnit => node 6 []
  | .LitPoison => node 7 []
  | .LitLoc x0 => node 8 [of x0]
  | .LitProphecy x0 => node 9 [of x0]
  | .LitSlice x0 => node 10 [of x0]
def BaseLit.ofTree : GenTree → BaseLit
  | node 0 [x0] => .LitInt (decLeaf x0)
  | node 1 [x0] => .LitInt32 (decLeaf x0)
  | node 2 [x0] => .LitInt16 (decLeaf x0)
  | node 3 [x0] => .LitBool (decLeaf x0)
  | node 4 [x0] => .LitByte (decLeaf x0)
  | node 5 [x0] => .LitString (decLeaf x0)
  | node 6 [] => .LitUnit
  | node 7 [] => .LitPoison
  | node 8 [x0] => .LitLoc (decLeaf x0)
  | node 9 [x0] => .LitProphecy (decLeaf x0)
  | node 10 [x0] => .LitSlice (decLeaf x0)
  | _ => default
instance BaseLit.countable : Pos.Countable BaseLit :=
  countableOfLeftInverse BaseLit.toTree BaseLit.ofTree
    (by intro x; cases x <;> (conv => lhs; whnf) <;> simp only [decLeaf_of])

def go_instruction.toTree : go_instruction → GenTree
  | .AngelicExit => node 0 []
  | .Convert x0 x1 => node 1 [of x0, of x1]
  | .GoOp x0 x1 => node 2 [of x0, of x1]
  | .GoUnOp x0 x1 => node 3 [of x0, of x1]
  | .CheckComparable x0 => node 4 [of x0]
  | .GoLoad x0 => node 5 [of x0]
  | .GoStore x0 => node 6 [of x0]
  | .GoAlloc x0 => node 7 [of x0]
  | .GoPrealloc => node 8 []
  | .GoZeroVal x0 => node 9 [of x0]
  | .FuncResolve x0 x1 => node 10 [of x0, of x1]
  | .MethodResolve x0 x1 => node 11 [of x0, of x1]
  | .TypeAssert x0 => node 12 [of x0]
  | .TypeAssert2 x0 => node 13 [of x0]
  | .PackageInitCheck x0 => node 14 [of x0]
  | .PackageInitStart x0 => node 15 [of x0]
  | .PackageInitFinish x0 => node 16 [of x0]
  | .GlobalVarAddr x0 => node 17 [of x0]
  | .StructFieldRef x0 x1 => node 18 [of x0, of x1]
  | .StructFieldGet x0 x1 => node 19 [of x0, of x1]
  | .StructFieldSet x0 x1 => node 20 [of x0, of x1]
  | .InternalSliceLen => node 21 []
  | .InternalSliceCap => node 22 []
  | .InternalDynamicArrayAlloc x0 => node 23 [of x0]
  | .InternalMakeSlice => node 24 []
  | .IndexRef x0 => node 25 [of x0]
  | .Index x0 => node 26 [of x0]
  | .Slice x0 => node 27 [of x0]
  | .FullSlice x0 => node 28 [of x0]
  | .ArraySet => node 29 []
  | .ArrayLength => node 30 []
  | .InternalMapCheckKey x0 => node 31 [of x0]
  | .InternalMapLookup => node 32 []
  | .InternalMapInsert => node 33 []
  | .InternalMapDelete => node 34 []
  | .InternalMapLength => node 35 []
  | .InternalMapForRange x0 x1 => node 36 [of x0, of x1]
  | .InternalMapMake => node 37 []
  | .CompositeLiteral x0 => node 38 [of x0]
  | .SelectStmt => node 39 []
  | .InternalStringLen => node 40 []
def go_instruction.ofTree : GenTree → go_instruction
  | node 0 [] => .AngelicExit
  | node 1 [x0, x1] => .Convert (decLeaf x0) (decLeaf x1)
  | node 2 [x0, x1] => .GoOp (decLeaf x0) (decLeaf x1)
  | node 3 [x0, x1] => .GoUnOp (decLeaf x0) (decLeaf x1)
  | node 4 [x0] => .CheckComparable (decLeaf x0)
  | node 5 [x0] => .GoLoad (decLeaf x0)
  | node 6 [x0] => .GoStore (decLeaf x0)
  | node 7 [x0] => .GoAlloc (decLeaf x0)
  | node 8 [] => .GoPrealloc
  | node 9 [x0] => .GoZeroVal (decLeaf x0)
  | node 10 [x0, x1] => .FuncResolve (decLeaf x0) (decLeaf x1)
  | node 11 [x0, x1] => .MethodResolve (decLeaf x0) (decLeaf x1)
  | node 12 [x0] => .TypeAssert (decLeaf x0)
  | node 13 [x0] => .TypeAssert2 (decLeaf x0)
  | node 14 [x0] => .PackageInitCheck (decLeaf x0)
  | node 15 [x0] => .PackageInitStart (decLeaf x0)
  | node 16 [x0] => .PackageInitFinish (decLeaf x0)
  | node 17 [x0] => .GlobalVarAddr (decLeaf x0)
  | node 18 [x0, x1] => .StructFieldRef (decLeaf x0) (decLeaf x1)
  | node 19 [x0, x1] => .StructFieldGet (decLeaf x0) (decLeaf x1)
  | node 20 [x0, x1] => .StructFieldSet (decLeaf x0) (decLeaf x1)
  | node 21 [] => .InternalSliceLen
  | node 22 [] => .InternalSliceCap
  | node 23 [x0] => .InternalDynamicArrayAlloc (decLeaf x0)
  | node 24 [] => .InternalMakeSlice
  | node 25 [x0] => .IndexRef (decLeaf x0)
  | node 26 [x0] => .Index (decLeaf x0)
  | node 27 [x0] => .Slice (decLeaf x0)
  | node 28 [x0] => .FullSlice (decLeaf x0)
  | node 29 [] => .ArraySet
  | node 30 [] => .ArrayLength
  | node 31 [x0] => .InternalMapCheckKey (decLeaf x0)
  | node 32 [] => .InternalMapLookup
  | node 33 [] => .InternalMapInsert
  | node 34 [] => .InternalMapDelete
  | node 35 [] => .InternalMapLength
  | node 36 [x0, x1] => .InternalMapForRange (decLeaf x0) (decLeaf x1)
  | node 37 [] => .InternalMapMake
  | node 38 [x0] => .CompositeLiteral (decLeaf x0)
  | node 39 [] => .SelectStmt
  | node 40 [] => .InternalStringLen
  | _ => default
instance go_instruction.countable : Pos.Countable go_instruction :=
  countableOfLeftInverse go_instruction.toTree go_instruction.ofTree
    (by intro x; cases x <;> (conv => lhs; whnf) <;> simp only [decLeaf_of])

/-! ## Expressions and values -/

section goose_syntax
variable [ffi_syntax]

set_option hygiene false in
/-- `inj_cases` for GooseLang syntax. -/
local macro "inj_ex " b:ident : tactic => `(tactic| inj_cases $b:ident [
    expr.Val.injEq, expr.Var.injEq, expr.Rec.injEq, expr.App.injEq, expr.If.injEq,
    expr.Pair.injEq, expr.Fst.injEq, expr.Snd.injEq, expr.Fork.injEq, expr.Primitive0.injEq,
    expr.Primitive1.injEq, expr.Primitive2.injEq, expr.CmpXchg.injEq, expr.ExternalOp.injEq,
    expr.ResolveProph.injEq, expr.LiteralValue.injEq, expr.SelectStmtClauses.injEq,
    val.LitV.injEq, val.RecV.injEq, val.PairV.injEq, val.InjLV.injEq, val.InjRV.injEq,
    val.ExtV.injEq, val.GoInstruction.injEq, val.ArrayV.injEq, val.InterfaceV.injEq,
    val.LiteralValueV.injEq, val.SelectStmtClausesV.injEq,
    keyed_element.KeyedElement.injEq, key.KeyField.injEq, key.KeyInteger.injEq,
    key.KeyExpression.injEq, key.KeyLiteralValue.injEq, element.ElementExpression.injEq,
    element.ElementLiteralValue.injEq, comm_clause.CommClause.injEq, comm_case.SendCase.injEq,
    comm_case.RecvCase.injEq])

mutual
def expr.toTree : expr → GenTree
  | .Val v => node 0 [v.toTree]
  | .Var x => node 1 [of x]
  | .Rec f x e => node 2 [of f, of x, e.toTree]
  | .App e1 e2 => node 3 [e1.toTree, e2.toTree]
  | .If e0 e1 e2 => node 4 [e0.toTree, e1.toTree, e2.toTree]
  | .Pair e1 e2 => node 5 [e1.toTree, e2.toTree]
  | .Fst e => node 6 [e.toTree]
  | .Snd e => node 7 [e.toTree]
  | .Fork e => node 8 [e.toTree]
  | .Primitive0 op => node 9 [of op]
  | .Primitive1 op e => node 10 [of op, e.toTree]
  | .Primitive2 op e1 e2 => node 11 [of op, e1.toTree, e2.toTree]
  | .CmpXchg e0 e1 e2 => node 12 [e0.toTree, e1.toTree, e2.toTree]
  | .ExternalOp op e => node 13 [of op, e.toTree]
  | .NewProph => node 14 []
  | .ResolveProph e1 e2 => node 15 [e1.toTree, e2.toTree]
  | .LiteralValue l => node 16 [kesToTree l]
  | .SelectStmtClauses d l => node 17 [optexprToTree d, clausesToTree l]
def val.toTree : val → GenTree
  | .LitV l => node 0 [of l]
  | .RecV f x e => node 1 [of f, of x, e.toTree]
  | .PairV v1 v2 => node 2 [v1.toTree, v2.toTree]
  | .InjLV v => node 3 [v.toTree]
  | .InjRV v => node 4 [v.toTree]
  | .ExtV ev => node 5 [of ev]
  | .GoInstruction o => node 6 [of o]
  | .ArrayV vs => node 7 [valsToTree vs]
  | .InterfaceV t => node 8 [optifaceToTree t]
  | .LiteralValueV l => node 9 [kesToTree l]
  | .SelectStmtClausesV d l => node 10 [optexprToTree d, clausesToTree l]
  | .UntypedNil => node 11 []
def keyed_element.toTree : keyed_element → GenTree
  | .KeyedElement k v => node 0 [optkeyToTree k, v.toTree]
def key.toTree : key → GenTree
  | .KeyField f => node 0 [of f]
  | .KeyInteger s => node 1 [of s]
  | .KeyExpression t e => node 2 [of t, e.toTree]
  | .KeyLiteralValue l => node 3 [kesToTree l]
def element.toTree : element → GenTree
  | .ElementExpression t e => node 0 [of t, e.toTree]
  | .ElementLiteralValue l => node 1 [kesToTree l]
def comm_clause.toTree : comm_clause → GenTree
  | .CommClause c body => node 0 [c.toTree, body.toTree]
def comm_case.toTree : comm_case → GenTree
  | .SendCase t ch e => node 0 [of t, ch.toTree, e.toTree]
  | .RecvCase t ch => node 1 [of t, ch.toTree]
def kesToTree : List keyed_element → GenTree
  | [] => node 0 []
  | k :: ks => node 1 [k.toTree, kesToTree ks]
def clausesToTree : List comm_clause → GenTree
  | [] => node 0 []
  | c :: cs => node 1 [c.toTree, clausesToTree cs]
def valsToTree : List val → GenTree
  | [] => node 0 []
  | v :: vs => node 1 [v.toTree, valsToTree vs]
def optexprToTree : Option expr → GenTree
  | none => node 0 []
  | some e => node 1 [e.toTree]
def optkeyToTree : Option key → GenTree
  | none => node 0 []
  | some k => node 1 [k.toTree]
def optifaceToTree : Option (go.type × val) → GenTree
  | none => node 0 []
  | some tv => node 1 [tyvalToTree tv]
def tyvalToTree : go.type × val → GenTree
  | (t, v) => node 0 [of t, v.toTree]
end

mutual
theorem expr.toTree_inj : ∀ {a b : expr}, a.toTree = b.toTree → a = b
  | .Val _, b, h => by inj_ex b; exact val.toTree_inj h
  | .Var _, b, h => by inj_ex b; exact h
  | .Rec .., b, h => by inj_ex b; exact ⟨h.1, h.2.1, expr.toTree_inj h.2.2⟩
  | .App .., b, h => by inj_ex b; exact ⟨expr.toTree_inj h.1, expr.toTree_inj h.2⟩
  | .If .., b, h => by
    inj_ex b; exact ⟨expr.toTree_inj h.1, expr.toTree_inj h.2.1, expr.toTree_inj h.2.2⟩
  | .Pair .., b, h => by inj_ex b; exact ⟨expr.toTree_inj h.1, expr.toTree_inj h.2⟩
  | .Fst _, b, h => by inj_ex b; exact expr.toTree_inj h
  | .Snd _, b, h => by inj_ex b; exact expr.toTree_inj h
  | .Fork _, b, h => by inj_ex b; exact expr.toTree_inj h
  | .Primitive0 _, b, h => by inj_ex b; exact h
  | .Primitive1 .., b, h => by inj_ex b; exact ⟨h.1, expr.toTree_inj h.2⟩
  | .Primitive2 .., b, h => by
    inj_ex b; exact ⟨h.1, expr.toTree_inj h.2.1, expr.toTree_inj h.2.2⟩
  | .CmpXchg .., b, h => by
    inj_ex b; exact ⟨expr.toTree_inj h.1, expr.toTree_inj h.2.1, expr.toTree_inj h.2.2⟩
  | .ExternalOp .., b, h => by inj_ex b; exact ⟨h.1, expr.toTree_inj h.2⟩
  | .NewProph, b, h => by inj_ex b
  | .ResolveProph .., b, h => by inj_ex b; exact ⟨expr.toTree_inj h.1, expr.toTree_inj h.2⟩
  | .LiteralValue _, b, h => by inj_ex b; exact kesToTree_inj h
  | .SelectStmtClauses .., b, h => by
    inj_ex b; exact ⟨optexprToTree_inj h.1, clausesToTree_inj h.2⟩
termination_by structural a _ _ => a
theorem val.toTree_inj : ∀ {a b : val}, a.toTree = b.toTree → a = b
  | .LitV _, b, h => by inj_ex b; exact h
  | .RecV .., b, h => by inj_ex b; exact ⟨h.1, h.2.1, expr.toTree_inj h.2.2⟩
  | .PairV .., b, h => by inj_ex b; exact ⟨val.toTree_inj h.1, val.toTree_inj h.2⟩
  | .InjLV _, b, h => by inj_ex b; exact val.toTree_inj h
  | .InjRV _, b, h => by inj_ex b; exact val.toTree_inj h
  | .ExtV _, b, h => by inj_ex b; exact h
  | .GoInstruction _, b, h => by inj_ex b; exact h
  | .ArrayV _, b, h => by inj_ex b; exact valsToTree_inj h
  | .InterfaceV _, b, h => by inj_ex b; exact optifaceToTree_inj h
  | .LiteralValueV _, b, h => by inj_ex b; exact kesToTree_inj h
  | .SelectStmtClausesV .., b, h => by
    inj_ex b; exact ⟨optexprToTree_inj h.1, clausesToTree_inj h.2⟩
  | .UntypedNil, b, h => by inj_ex b
termination_by structural a _ _ => a
theorem keyed_element.toTree_inj : ∀ {a b : keyed_element}, a.toTree = b.toTree → a = b
  | .KeyedElement .., b, h => by
    inj_ex b; exact ⟨optkeyToTree_inj h.1, element.toTree_inj h.2⟩
termination_by structural a _ _ => a
theorem key.toTree_inj : ∀ {a b : key}, a.toTree = b.toTree → a = b
  | .KeyField _, b, h => by inj_ex b; exact h
  | .KeyInteger _, b, h => by inj_ex b; exact h
  | .KeyExpression .., b, h => by inj_ex b; exact ⟨h.1, expr.toTree_inj h.2⟩
  | .KeyLiteralValue _, b, h => by inj_ex b; exact kesToTree_inj h
termination_by structural a _ _ => a
theorem element.toTree_inj : ∀ {a b : element}, a.toTree = b.toTree → a = b
  | .ElementExpression .., b, h => by inj_ex b; exact ⟨h.1, expr.toTree_inj h.2⟩
  | .ElementLiteralValue _, b, h => by inj_ex b; exact kesToTree_inj h
termination_by structural a _ _ => a
theorem comm_clause.toTree_inj : ∀ {a b : comm_clause}, a.toTree = b.toTree → a = b
  | .CommClause .., b, h => by
    inj_ex b; exact ⟨comm_case.toTree_inj h.1, expr.toTree_inj h.2⟩
termination_by structural a _ _ => a
theorem comm_case.toTree_inj : ∀ {a b : comm_case}, a.toTree = b.toTree → a = b
  | .SendCase .., b, h => by
    inj_ex b; exact ⟨h.1, expr.toTree_inj h.2.1, expr.toTree_inj h.2.2⟩
  | .RecvCase .., b, h => by inj_ex b; exact ⟨h.1, expr.toTree_inj h.2⟩
termination_by structural a _ _ => a
theorem kesToTree_inj : ∀ {a b : List keyed_element}, kesToTree a = kesToTree b → a = b
  | [], b, h => by inj_ex b
  | _ :: _, b, h => by inj_ex b; exact ⟨keyed_element.toTree_inj h.1, kesToTree_inj h.2⟩
termination_by structural a _ _ => a
theorem clausesToTree_inj : ∀ {a b : List comm_clause}, clausesToTree a = clausesToTree b → a = b
  | [], b, h => by inj_ex b
  | _ :: _, b, h => by inj_ex b; exact ⟨comm_clause.toTree_inj h.1, clausesToTree_inj h.2⟩
termination_by structural a _ _ => a
theorem valsToTree_inj : ∀ {a b : List val}, valsToTree a = valsToTree b → a = b
  | [], b, h => by inj_ex b
  | _ :: _, b, h => by inj_ex b; exact ⟨val.toTree_inj h.1, valsToTree_inj h.2⟩
termination_by structural a _ _ => a
theorem optexprToTree_inj : ∀ {a b : Option expr}, optexprToTree a = optexprToTree b → a = b
  | none, b, h => by inj_ex b
  | some _, b, h => by inj_ex b; exact expr.toTree_inj h
termination_by structural a _ _ => a
theorem optkeyToTree_inj : ∀ {a b : Option key}, optkeyToTree a = optkeyToTree b → a = b
  | none, b, h => by inj_ex b
  | some _, b, h => by inj_ex b; exact key.toTree_inj h
termination_by structural a _ _ => a
theorem optifaceToTree_inj : ∀ {a b : Option (go.type × val)},
    optifaceToTree a = optifaceToTree b → a = b
  | none, b, h => by inj_ex b
  | some _, b, h => by inj_ex b; exact tyvalToTree_inj h
termination_by structural a _ _ => a
theorem tyvalToTree_inj : ∀ {a b : go.type × val}, tyvalToTree a = tyvalToTree b → a = b
  | (_, _), (_, _), h => by
    injection h with _ h
    simp only [List.cons.injEq, GenTree.leaf.injEq, Pos.encode_eq_iff, and_true,
      Prod.mk.injEq] at h ⊢
    exact ⟨h.1, val.toTree_inj h.2⟩
termination_by structural a _ _ => a
end

instance expr.countable : Pos.Countable expr := countableOfTree expr.toTree expr.toTree_inj
instance val.countable : Pos.Countable val := countableOfTree val.toTree val.toTree_inj

instance func.countable : Pos.Countable func.t :=
  countableOfLeftInverse (fun f : func.t => (f.f, f.x, f.e)) (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (fun _ => rfl)

instance interface.countable : Pos.Countable interface.t :=
  countableOfLeftInverse
    (fun i : interface.t => match i with | .ok ⟨t, v⟩ => some (t, v) | .nil => none)
    (fun | some (t, v) => .ok ⟨t, v⟩ | none => .nil)
    (by intro i; rcases i with ⟨t, v⟩ | _ <;> rfl)

instance array.countable {V : Type} [Pos.Countable V] {n : Int} : Pos.Countable (array.t V n) :=
  countableOfLeftInverse (fun a : array.t V n => a.arr) (fun l => ⟨l⟩) (fun _ => rfl)

end goose_syntax

end Perennial
