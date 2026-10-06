/-
GooseLang. Port of `src/goose_lang/lang.v`.

GooseLang is an adaptation of HeapLang with extensions to model Go, including
a customizable FFI (foreign-function interface) for new primitive operations.

Differences from the Rocq version:
* There is no crash semantics (`ffi_crash_step`, `goose_crash`).
* The base step is an inductive relation (`base_step`) instead of being written
  with the `Transitions` monad, and FFI steps (`FfiSemantics.ffi_step`) are a
  plain relation.
* The real semantics is `gooseRealEctxiLang`, an iris-lean
  `EctxItemLanguage` whose state is the pair `state × GlobalState`
  (`CfgState`). It is a `def`, not an instance: the registered language
  instance (used by the program logic) is the step-bounded layer
  `goose_ectxi_lang` of `Perennial/GooseLang/BoundedLang.lean`, which adds a
  step fuel on top of `base_step` for time receipts. The adequacy theorems
  are transferred back to `gooseRealEctxiLang` (`goose_adequacy`).
* Equality on the syntax is decided classically. Rocq proves it with an
  encoding into trees; nothing downstream computes with it.
-/
import Iris.ProgramLogic.EctxiLanguage
import Iris.ProgramLogic.Language
import Perennial.Std.GMap
import Perennial.Std.Countable
import Perennial.GooseLang.Locations
import Perennial.Golang.Defn.PreLang

namespace Perennial

open Iris.ProgramLogic

/-! ## Expressions and values -/

abbrev proph_id := Nat

/-- Rocq stdpp `binder`. -/
inductive Binder where
  | BAnon
  | BNamed (s : String)
deriving DecidableEq, Inhabited, Repr

export Binder (BAnon BNamed)

instance : Coe String Binder := ⟨BNamed⟩

class FfiSyntax where
  ffi_opcode : Type
  [ffi_opcode_eq_dec : DecidableEq ffi_opcode]
  [ffi_opcode_countable : Pos.Countable ffi_opcode]
  ffi_val : Type
  [ffi_val_eq_dec : DecidableEq ffi_val]
  [ffi_val_countable : Pos.Countable ffi_val]

attribute [instance] FfiSyntax.ffi_opcode_eq_dec FfiSyntax.ffi_val_eq_dec
  FfiSyntax.ffi_opcode_countable FfiSyntax.ffi_val_countable
export FfiSyntax (ffi_opcode ffi_val)

class FfiModel where
  ffi_state : Type
  ffi_global_state : Type
  [ffi_state_inhabited : Inhabited ffi_state]
  [ffi_global_state_inhabited : Inhabited ffi_global_state]

attribute [instance] FfiModel.ffi_state_inhabited FfiModel.ffi_global_state_inhabited
export FfiModel (ffi_state ffi_global_state)

namespace slice
structure _root_.Perennial.GoSlice where
  ptr : Loc
  len : w64
  cap : w64
deriving DecidableEq, Inhabited

def nil : GoSlice := ⟨null, 0, 0⟩
/-- Rocq `slice.mk`. -/
abbrev mk (ptr : Loc) (len cap : w64) : GoSlice := ⟨ptr, len, cap⟩
end slice

/-- Primitive (non-composite) values, injected into `val` by `LitV`. -/
inductive BaseLit where
  | LitInt (n : w64)
  | LitInt32 (n : w32)
  | LitInt16 (n : w16)
  | LitBool (b : Bool)
  | LitByte (n : w8)
  | LitString (s : byte_string)
  | LitUnit
  | LitPoison
  | LitLoc (l : Loc)
  | LitProphecy (p : proph_id)
  | LitSlice (s : GoSlice)
deriving DecidableEq, Inhabited

inductive PrimOp0 where
  /-- a stuck expression, to represent undefined behavior -/
  | PanicOp (s : String)
  /-- non-deterministically pick an integer -/
  | ArbitraryIntOp
deriving DecidableEq

inductive PrimOp1 where
  /-- non-atomic write, part 1 (loc) -/
  | PrepareWriteOp
  /-- non-atomic loads (which conflict with stores) -/
  | StartReadOp
  | FinishReadOp
  /-- atomic loads (which still conflict with non-atomic stores) -/
  | LoadOp
  /-- allocation (initial value) -/
  | AllocOp
deriving DecidableEq

inductive PrimOp2 where
  /-- pointer, value -/
  | FinishStoreOp
  /-- pointer, value; returns old value -/
  | AtomicSwapOp
  /-- pointer, value -/
  | AtomicAddOp
deriving DecidableEq

inductive GoOperator where
  | GoEquals | GoLt | GoLe | GoGt | GoGe
  | GoPlus | GoSub | GoMul | GoDiv | GoRemainder
  | GoAnd | GoOr | GoXor | GoBitClear | GoShiftl | GoShiftr
deriving DecidableEq

inductive GoUnaryOperator where
  | GoPos | GoNeg | GoNot | GoComplement
deriving DecidableEq

inductive GoInstruction where
  | AngelicExit
  | Convert (from_ to : go.GoType)
  | GoOp (o : GoOperator) (t : go.GoType)
  | GoUnOp (o : GoUnaryOperator) (t : go.GoType)
  | CheckComparable (t : go.GoType)
  | GoLoad (t : go.GoType)
  | GoStore (t : go.GoType)
  | GoAlloc (t : go.GoType)
  | GoPrealloc
  | GoZeroVal (t : go.GoType)
  | FuncResolve (f : GoString) (type_args : List go.GoType)
  | MethodResolve (t : go.GoType) (m : GoString)
  | TypeAssert (t : go.GoType)
  | TypeAssert2 (t : go.GoType)
  | PackageInitCheck (pkg_name : GoString)
  | PackageInitStart (pkg_name : GoString)
  | PackageInitFinish (pkg_name : GoString)
  | GlobalVarAddr (var_name : GoString)
  | StructFieldRef (t : go.GoType) (f : GoString)
  | StructFieldGet (t : go.GoType) (f : GoString)
  | StructFieldSet (t : go.GoType) (f : GoString)
  /- can do slice, array, string, map, etc. for these ops; the internal ones
     should not be directly called by GooseLang. -/
  | InternalSliceLen
  | InternalSliceCap
  | InternalDynamicArrayAlloc (elem_type : go.GoType)
  | InternalMakeSlice
  | IndexRef (t : go.GoType)
  | Index (t : go.GoType)
  | Slice (t : go.GoType)
  | FullSlice (t : go.GoType)
  | ArraySet
  | ArrayLength
  /- internal steps; the Go map lookup has to be implemented as multiple
     instructions because it is not atomic. -/
  | InternalMapCheckKey (key_type : go.GoType)
  | InternalMapLookup
  | InternalMapInsert
  | InternalMapDelete
  | InternalMapLength
  | InternalMapForRange (key_type elem_type : go.GoType)
  | InternalMapMake
  | CompositeLiteral (t : go.GoType)
  | SelectStmt
  | InternalStringLen

noncomputable instance : DecidableEq GoInstruction := fun a b => Classical.propDecidable (a = b)

section goose_syntax
variable [ext : FfiSyntax]

mutual
inductive Expr where
  -- Values
  | Val (v : val)
  -- Base lambda calculus
  | Var (x : String)
  | Rec (f x : Binder) (e : Expr)
  | App (e1 e2 : Expr)
  | If (e0 e1 e2 : Expr)
  -- Products
  | Pair (e1 e2 : Expr)
  | Fst (e : Expr)
  | Snd (e : Expr)
  -- Concurrency
  | Fork (e : Expr)
  -- Heap-based primitives
  | Primitive0 (op : PrimOp0)
  | Primitive1 (op : PrimOp1) (e : Expr)
  | Primitive2 (op : PrimOp2) (e1 e2 : Expr)
  /-- Compare-exchange -/
  | CmpXchg (e0 e1 e2 : Expr)
  /-- External FFI operation -/
  | ExternalOp (op : ffi_opcode) (e : Expr)
  -- Prophecy
  | NewProph
  | ResolveProph (e1 e2 : Expr)
  | LiteralValue (l : List keyed_element)
  | SelectStmtClauses (default_handler : Option Expr) (l : List comm_clause)

inductive val where
  | LitV (l : BaseLit)
  | RecV (f x : Binder) (e : Expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  /-- Pointers to opaque types that FFI operations may return. -/
  | ExtV (ev : ffi_val)
  -- Go stuff
  | GoInstruction (o : GoInstruction)
  | ArrayV (vs : List val)
  | InterfaceV (t : Option (go.GoType × val))
  | LiteralValueV (l : List keyed_element)
  | SelectStmtClausesV (default_handler : Option Expr) (l : List comm_clause)
  | UntypedNil

/-- https://go.dev/ref/spec#Composite_literals -/
inductive keyed_element where
  | KeyedElement (k : Option key) (v : Element)

inductive key where
  | KeyField (f : GoString)
  | KeyInteger (s : Int)
  | KeyExpression (t : go.GoType) (e : Expr)
  | KeyLiteralValue (l : List keyed_element)

inductive Element where
  | ElementExpression (t : go.GoType) (e : Expr)
  | ElementLiteralValue (l : List keyed_element)

inductive comm_clause where
  | CommClause (c : CommCase) (body : Expr)

/-- Variable bindings are desugared by goose into the body, so the send and
receives don't need to consider bindings or assignments. (`default` is
inlined into `SelectStmtClauses`.) -/
inductive CommCase where
  | SendCase (elem_type : go.GoType) (ch : Expr) (e : Expr)
  | RecvCase (elem_type : go.GoType) (ch : Expr)
end

noncomputable instance : DecidableEq Expr := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq val := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq keyed_element := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq key := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq Element := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq comm_clause := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq CommCase := fun a b => Classical.propDecidable (a = b)

instance : Inhabited val := ⟨.LitV .LitUnit⟩
instance : Inhabited Expr := ⟨.Val default⟩

end goose_syntax

export Expr (Val Var Rec App If Pair Fst Snd Fork Primitive0 Primitive1 Primitive2 CmpXchg
  ExternalOp NewProph ResolveProph LiteralValue SelectStmtClauses)
export val (LitV RecV PairV InjLV InjRV ExtV GoInstruction ArrayV InterfaceV LiteralValueV
  SelectStmtClausesV UntypedNil)
export keyed_element (KeyedElement)
export key (KeyField KeyInteger KeyExpression KeyLiteralValue)
export Element (ElementExpression ElementLiteralValue)
export comm_clause (CommClause)
export CommCase (SendCase RecvCase)
export BaseLit (LitInt LitInt32 LitInt16 LitBool LitByte LitString LitUnit LitPoison LitLoc
  LitProphecy LitSlice)
export GoOperator (GoEquals GoLt GoLe GoGt GoGe GoPlus GoSub GoMul GoDiv GoRemainder GoAnd
  GoOr GoXor GoBitClear GoShiftl GoShiftr)
export GoUnaryOperator (GoPos GoNeg GoNot GoComplement)
export GoInstruction (AngelicExit Convert GoOp GoUnOp CheckComparable GoLoad GoStore GoAlloc
  GoPrealloc GoZeroVal FuncResolve MethodResolve TypeAssert TypeAssert2 PackageInitCheck
  PackageInitStart PackageInitFinish GlobalVarAddr StructFieldRef StructFieldGet StructFieldSet
  InternalSliceLen InternalSliceCap InternalDynamicArrayAlloc InternalMakeSlice IndexRef Index
  Slice FullSlice ArraySet ArrayLength InternalMapCheckKey InternalMapLookup InternalMapInsert
  InternalMapDelete InternalMapLength InternalMapForRange InternalMapMake CompositeLiteral
  SelectStmt InternalStringLen)

section derived
variable [ext : FfiSyntax]

instance : Coe val Expr := ⟨Val⟩
instance : Coe String Expr := ⟨Var⟩
instance : CoeFun Expr (fun _ => Expr → Expr) := ⟨App⟩

abbrev Panic (s : String) : Expr := Primitive0 (.PanicOp s)
abbrev ArbitraryInt : Expr := Primitive0 .ArbitraryIntOp
abbrev Alloc (e : Expr) : Expr := Primitive1 .AllocOp e
abbrev PrepareWrite (e : Expr) : Expr := Primitive1 .PrepareWriteOp e
abbrev StartRead (e : Expr) : Expr := Primitive1 .StartReadOp e
abbrev FinishRead (e : Expr) : Expr := Primitive1 .FinishReadOp e
abbrev Load (e : Expr) : Expr := Primitive1 .LoadOp e
abbrev FinishStore (e1 e2 : Expr) : Expr := Primitive2 .FinishStoreOp e1 e2
abbrev AtomicSwap (e1 e2 : Expr) : Expr := Primitive2 .AtomicSwapOp e1 e2
abbrev AtomicAdd (e1 e2 : Expr) : Expr := Primitive2 .AtomicAddOp e1 e2

abbrev Lam (x : Binder) (e : Expr) : Expr := Rec BAnon x e
abbrev Let (x : Binder) (e1 e2 : Expr) : Expr := App (Lam x e2) e1
abbrev Seq (e1 e2 : Expr) : Expr := Let BAnon e1 e2
abbrev LamV (x : Binder) (e : Expr) : val := RecV BAnon x e
/-- Compare-and-set returns just a boolean indicating success or failure. -/
abbrev CAS (l e1 e2 : Expr) : Expr := Snd (CmpXchg l e1 e2)

def Store : val :=
  LamV "l" (Lam "v" (Seq (PrepareWrite (Var "l")) (FinishStore (Var "l") (Var "v"))))

def Read : val :=
  LamV "l" (Let "v" (StartRead (Var "l")) (Seq (FinishRead (Var "l")) (Var "v")))

end derived

namespace func
structure _root_.Perennial.GoFunc [FfiSyntax] where
  f : Binder
  x : Binder
  e : Expr

def nil [FfiSyntax] : GoFunc := ⟨BAnon, BAnon, Val (LitV LitPoison)⟩

instance [FfiSyntax] : Inhabited GoFunc := ⟨nil⟩
/-- Rocq `func.mk`. -/
abbrev mk [FfiSyntax] (f x : Binder) (e : Expr) : GoFunc := ⟨f, x, e⟩
end func

/-- `GoGlobalContext` contains the `intoVal` function. This allows for the Go
semantics to state constraints on `intoVal` (e.g. injectivity for certain
types). -/
class GoGlobalContext [FfiSyntax] where
  intoVal : {V : Type} → V → val
  intoVal_inj_loc : Function.Injective (intoVal (V := Loc))
  intoVal_inj_bool : Function.Injective (intoVal (V := Bool))
  intoVal_inj_proph_id : Function.Injective (intoVal (V := proph_id))
  intoVal_inj_w64 : Function.Injective (intoVal (V := w64))
  intoVal_inj_w8 : Function.Injective (intoVal (V := w8))

export GoGlobalContext (intoVal)

/-- `# x` is `intoVal x`. -/
scoped prefix:max "#" => intoVal

/-- `GoLocalContext` contains several low-level Go functions for typed memory
access, map updates, etc. -/
class GoLocalContext [FfiSyntax] where
  is_go_step_pure : GoInstruction → val → Expr → Prop

export GoLocalContext (is_go_step_pure)

namespace chan
abbrev _root_.Perennial.GoChan := Loc
def nil : GoChan := null
end chan

namespace interface

structure _root_.Perennial.GoInterfaceOk [FfiSyntax] where
  ty : go.GoType
  v : val

inductive _root_.Perennial.GoInterface [FfiSyntax] where
  | ok (i : GoInterfaceOk)
  | nil

export GoInterface (ok nil)

abbrev mkOk [FfiSyntax] (ty : go.GoType) (v : val) : GoInterface := .ok ⟨ty, v⟩
/-- Rocq `interface.mk`. -/
abbrev mk [FfiSyntax] (ty : go.GoType) (v : val) : GoInterfaceOk := ⟨ty, v⟩

end interface

namespace array
structure _root_.Perennial.GoArray (V : Type) (n : Int) where
  mk ::
  arr : List V
/-- Rocq `array.mk n arr`. -/
abbrev mk {V : Type} (n : Int) (arr : List V) : GoArray V n := ⟨arr⟩
end array

/-! ## State -/

inductive NaMode where
  | Writing
  | Reading (n : Nat)
deriving DecidableEq, Inhabited

export NaMode (Writing Reading)

abbrev NonAtomic (T : Type) := NaMode × T

def Free {T} (v : T) : NonAtomic T := (Reading 0, v)

class ZeroVal (V : Type) where
  zeroValDef : V

export ZeroVal (zeroValDef)

abbrev zero_val (V : Type) [ZeroVal V] : V := ZeroVal.zeroValDef

section zero_val_instances
variable [FfiSyntax]
instance : ZeroVal Loc := ⟨null⟩
instance : ZeroVal w64 := ⟨0⟩
instance : ZeroVal w32 := ⟨0⟩
instance : ZeroVal w16 := ⟨0⟩
instance : ZeroVal w8 := ⟨0⟩
instance : ZeroVal Unit := ⟨()⟩
instance : ZeroVal Bool := ⟨false⟩
instance : ZeroVal GoString := ⟨[]⟩
instance : ZeroVal GoFunc := ⟨func.nil⟩
instance {V} [ZeroVal V] (n : Int) : ZeroVal (GoArray V n) :=
  ⟨⟨List.replicate n.toNat (zero_val V)⟩⟩
instance : ZeroVal GoSlice := ⟨slice.nil⟩
instance : ZeroVal GoInterface := ⟨.nil⟩
instance : ZeroVal proph_id := ⟨1⟩
end zero_val_instances

section state
variable [FfiSyntax] [FfiModel]

structure GoState where
  goLctx : GoLocalContext
  packageState : GMap GoString Bool

instance : Inhabited GoLocalContext := ⟨⟨fun _ _ _ => False⟩⟩
instance : Inhabited GoState := ⟨⟨default, ∅⟩⟩

structure state where
  heap : GMap Loc (NonAtomic val)
  goState : GoState
  world : ffi_state

structure GlobalState where
  globalWorld : ffi_global_state
  usedProphId : GSet proph_id

instance : Inhabited state := ⟨⟨∅, default, default⟩⟩
instance : Inhabited GlobalState := ⟨⟨default, ∅⟩⟩

/-- The state of the iris-lean language: Rocq's `state * GlobalState`. -/
abbrev CfgState := state × GlobalState

/-- An observation associates a prophecy variable to the value it is resolved to. -/
abbrev Observation := proph_id × val

end state

def IsGoStep [FfiSyntax] [GoGlobalContext] [GoLocalContext]
    (op : GoInstruction) (arg : val) (e' : Expr) (s s' : GMap GoString Bool) : Prop :=
  match op with
  | PackageInitCheck p => arg = #() ∧ e' = Val #((s !! p).getD false) ∧ s' = s
  | PackageInitStart p => arg = #() ∧ e' = Val #() ∧ s' = <[p := false]> s
  | PackageInitFinish p => arg = #() ∧ e' = Val #() ∧ s' = <[p := true]> s
  | _ => GoLocalContext.is_go_step_pure op arg e' ∧ s = s'

/-- FFI semantics: `ffi_step op v σg e' σg'` says that the external operation
`op` applied to `v` in state `σg` can produce `e'` and state `σg'`. -/
class FfiSemantics (ext : FfiSyntax) (ffi : FfiModel) where
  ffi_step : ffi_opcode → val → CfgState → Expr → CfgState → Prop

export FfiSemantics (ffi_step)

/-! ## Evaluation contexts and substitution -/

section lang
variable [ext : FfiSyntax]

def toVal : Expr → Option val
  | Val v => some v
  | _ => none

@[simp] theorem to_of_val (v : val) : toVal (Val v) = some v := rfl

theorem of_to_val {e : Expr} {v : val} : toVal e = some v → Val v = e := by
  cases e <;> simp [toVal]; exact Eq.symm

inductive EctxItem where
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : Expr)
  | IfCtx (e1 e2 : Expr)
  | PairLCtx (e2 : Expr)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | Primitive1Ctx (op : PrimOp1)
  | Primitive2LCtx (op : PrimOp2) (e2 : Expr)
  | Primitive2RCtx (op : PrimOp2) (v1 : val)
  | ExternalOpCtx (op : ffi_opcode)
  | CmpXchgLCtx (e1 e2 : Expr)
  | CmpXchgMCtx (v1 : val) (e2 : Expr)
  | CmpXchgRCtx (v1 v2 : val)
  | ResolveProphLCtx (v2 : val)
  | ResolveProphRCtx (e1 : Expr)

open EctxItem in
def fillItem (Ki : EctxItem) (e : Expr) : Expr :=
  match Ki with
  | AppLCtx v2 => App e (Val v2)
  | AppRCtx e1 => App e1 e
  | IfCtx e1 e2 => If e e1 e2
  | PairLCtx e2 => Pair e e2
  | PairRCtx v1 => Pair (Val v1) e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | Primitive1Ctx op => Primitive1 op e
  | Primitive2LCtx op e2 => Primitive2 op e e2
  | Primitive2RCtx op v1 => Primitive2 op (Val v1) e
  | ExternalOpCtx op => ExternalOp op e
  | CmpXchgLCtx e1 e2 => CmpXchg e e1 e2
  | CmpXchgMCtx v0 e2 => CmpXchg (Val v0) e e2
  | CmpXchgRCtx v0 v1 => CmpXchg (Val v0) (Val v1) e
  | ResolveProphLCtx v2 => ResolveProph e (Val v2)
  | ResolveProphRCtx e1 => ResolveProph e1 e

mutual
def subst (x : String) (v : val) : Expr → Expr
  | Val v' => Val v'
  | Var y => if x = y then Val v else Var y
  | Rec f y e => Rec f y (if BNamed x ≠ f ∧ BNamed x ≠ y then subst x v e else e)
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | Fork e => Fork (subst x v e)
  | Primitive0 op => Primitive0 op
  | Primitive1 op e => Primitive1 op (subst x v e)
  | Primitive2 op e1 e2 => Primitive2 op (subst x v e1) (subst x v e2)
  | ExternalOp op e => ExternalOp op (subst x v e)
  | CmpXchg e0 e1 e2 => CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)
  | NewProph => NewProph
  | ResolveProph e1 e2 => ResolveProph (subst x v e1) (subst x v e2)
  | LiteralValue l => LiteralValue (substKeyedElements x v l)
  | SelectStmtClauses d l => SelectStmtClauses (substOpt x v d) (substCommClauses x v l)

def substOpt (x : String) (v : val) : Option Expr → Option Expr
  | none => none
  | some e => some (subst x v e)

def substKeyedElements (x : String) (v : val) : List keyed_element → List keyed_element
  | [] => []
  | ke :: l => substKeyedElement x v ke :: substKeyedElements x v l

def substKeyedElement (x : String) (v : val) : keyed_element → keyed_element
  | KeyedElement k el => KeyedElement (substOptKey x v k) (substElement x v el)

def substOptKey (x : String) (v : val) : Option key → Option key
  | none => none
  | some (KeyExpression t e) => some (KeyExpression t (subst x v e))
  | some (KeyLiteralValue l) => some (KeyLiteralValue (substKeyedElements x v l))
  | some k => some k

def substElement (x : String) (v : val) : Element → Element
  | ElementExpression t e => ElementExpression t (subst x v e)
  | ElementLiteralValue l => ElementLiteralValue (substKeyedElements x v l)

def substCommClauses (x : String) (v : val) : List comm_clause → List comm_clause
  | [] => []
  | c :: l => substCommClause x v c :: substCommClauses x v l

def substCommClause (x : String) (v : val) : comm_clause → comm_clause
  | CommClause (SendCase t b e) body => CommClause (SendCase t (subst x v b) (subst x v e)) (subst x v body)
  | CommClause (RecvCase t e) body => CommClause (RecvCase t (subst x v e)) (subst x v body)
end

def subst' (mx : Binder) (v : val) : Expr → Expr :=
  match mx with
  | BNamed x => subst x v
  | BAnon => id

end lang

/-! ## The base step relation -/

section step
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]

def stateInitHeap (l : Loc) (v : val) (σ : state) : state :=
  { σ with heap := {[l := Free v]} ∪ σ.heap }

def IsWriting {A} (mna : Option (NonAtomic A)) : Prop := ∃ x, mna = some (Writing, x)

/-- `l` is the start of a fresh block in `σg`. -/
def IsFresh (σg : CfgState) (l : Loc) : Prop :=
  (∀ i : Int, l +ₗ i ≠ null ∧ σg.1.heap !! (l +ₗ i) = none) ∧ l.addrOffset = 0

def atomicAddEval (v1 v2 : val) : Option val :=
  match v1, v2 with
  | LitV (LitInt n1), LitV (LitInt n2) => some #(n1 + n2)
  | LitV (LitInt32 n1), LitV (LitInt32 n2) => some #(n1 + n2)
  | LitV (LitInt16 n1), LitV (LitInt16 n2) => some #(n1 + n2)
  | LitV (LitByte n1), LitV (LitByte n2) => some #(n1 + n2)
  | _, _ => none

def setHeap (f : GMap Loc (NonAtomic val) → GMap Loc (NonAtomic val)) (σg : CfgState) :
    CfgState :=
  ({ σg.1 with heap := f σg.1.heap }, σg.2)

open Classical in
/-- Rocq `base_trans`/`base_step`, as an inductive relation:
`base_step e σg κs e' σg' efs`. -/
inductive BaseStep : Expr → CfgState → List Observation → Expr → CfgState → List Expr → Prop
  | RecS f x e σg : BaseStep (Rec f x e) σg [] (Val (RecV f x e)) σg []
  | PairS v1 v2 σg : BaseStep (Pair (Val v1) (Val v2)) σg [] (Val (PairV v1 v2)) σg []
  | BetaS f x e1 v2 σg :
      BaseStep (App (Val (RecV f x e1)) (Val v2)) σg []
        (subst' x v2 (subst' f (RecV f x e1) e1)) σg []
  | IfTrueS e1 e2 σg : BaseStep (If (Val #true) e1 e2) σg [] e1 σg []
  | IfFalseS e1 e2 σg : BaseStep (If (Val #false) e1 e2) σg [] e2 σg []
  | FstS v1 v2 σg : BaseStep (Fst (Val (PairV v1 v2))) σg [] (Val v1) σg []
  | SndS v1 v2 σg : BaseStep (Snd (Val (PairV v1 v2))) σg [] (Val v2) σg []
  | ForkS e σg : BaseStep (Fork e) σg [] (Val #()) σg [e]
  | ArbitraryIntS (x : w64) σg : BaseStep ArbitraryInt σg [] (Val #x) σg []
  | AllocS v l σg :
      IsFresh σg l →
      BaseStep (Alloc (Val v)) σg [] (Val #l) (stateInitHeap l v σg.1, σg.2) []
  /-- non-atomic load part 1 (used for map accesses) -/
  | StartReadS l n v σg :
      σg.1.heap !! l = some (Reading n, v) →
      BaseStep (StartRead (Val #l)) σg [] (Val v) (setHeap (<[l := (Reading (n + 1), v)]> ·) σg) []
  /-- non-atomic load part 2 -/
  | FinishReadS l n v σg :
      σg.1.heap !! l = some (Reading (n + 1), v) →
      BaseStep (FinishRead (Val #l)) σg [] (Val #()) (setHeap (<[l := (Reading n, v)]> ·) σg) []
  /-- atomic load (used for most normal Go loads) -/
  | LoadS l n v σg :
      σg.1.heap !! l = some (Reading n, v) →
      BaseStep (Load (Val #l)) σg [] (Val v) σg []
  /-- non-atomic write part 1 -/
  | PrepareWriteS l v σg :
      σg.1.heap !! l = some (Reading 0, v) →
      BaseStep (PrepareWrite (Val #l)) σg [] (Val #()) (setHeap (<[l := (Writing, v)]> ·) σg) []
  /-- non-atomic write part 2 -/
  | FinishStoreS l v σg :
      IsWriting (σg.1.heap !! l) →
      BaseStep (FinishStore (Val #l) (Val v)) σg [] (Val #()) (setHeap (<[l := Free v]> ·) σg) []
  | AtomicSwapS l v0 v σg :
      σg.1.heap !! l = some (Reading 0, v0) →
      BaseStep (AtomicSwap (Val #l) (Val v)) σg [] (Val v0) (setHeap (<[l := Free v]> ·) σg) []
  | AtomicAddS l v0 v v' σg :
      σg.1.heap !! l = some (Reading 0, v0) →
      atomicAddEval v0 v = some v' →
      BaseStep (AtomicAdd (Val #l) (Val v)) σg [] (Val v') (setHeap (<[l := Free v']> ·) σg) []
  | ExternalOpS op v e' σg σg' :
      ffi_step op v σg e' σg' →
      BaseStep (ExternalOp op (Val v)) σg [] e' σg' []
  | GoInstructionS op arg e' s' σg :
      @IsGoStep _ _ σg.1.goState.goLctx op arg e' σg.1.goState.packageState s' →
      BaseStep (App (Val (GoInstruction op)) (Val arg)) σg [] e'
        ({ σg.1 with goState := { σg.1.goState with packageState := s' } }, σg.2) []
  | CmpXchgFailS l n vl v1 v2 σg :
      σg.1.heap !! l = some (Reading n, vl) →
      vl ≠ v1 →
      BaseStep (CmpXchg (Val #l) (Val v1) (Val v2)) σg [] (Val (PairV vl #false)) σg []
  | CmpXchgSucS l vl v1 v2 σg :
      σg.1.heap !! l = some (Reading 0, vl) →
      vl = v1 →
      BaseStep (CmpXchg (Val #l) (Val v1) (Val v2)) σg [] (Val (PairV vl #true))
        (setHeap (<[l := Free v2]> ·) σg) []
  | NewProphS p σg :
      p ∉ σg.2.usedProphId →
      BaseStep NewProph σg [] (Val #p)
        (σg.1, { σg.2 with usedProphId := {[p := ()]} ∪ σg.2.usedProphId }) []
  | ResolveProphS (p : proph_id) w σg :
      BaseStep (ResolveProph (Val #p) (Val w)) σg [(p, w)] (Val #()) σg []
  | LiteralValueS l σg : BaseStep (LiteralValue l) σg [] (Val (LiteralValueV l)) σg []
  | SelectStmtClausesS d cs σg :
      BaseStep (SelectStmtClauses d cs) σg [] (Val (SelectStmtClausesV d cs)) σg []

theorem val_base_stuck {e σ κ e' σ' efs} : BaseStep e σ κ e' σ' efs → toVal e = none := by
  intro h; cases h <;> rfl

theorem fillItem_val (Ki : EctxItem) (e : Expr) :
    (toVal (fillItem Ki e)).isSome → (toVal e).isSome := by
  cases Ki <;> simp [fillItem, toVal]

theorem fillItem_inj (Ki : EctxItem) : Function.Injective (fillItem Ki) := by
  intro e1 e2 h; cases Ki <;> simp_all [fillItem]

theorem fillItem_no_val_inj (Ki1 Ki2 : EctxItem) {e1 e2 : Expr} :
    toVal e1 = none → toVal e2 = none → fillItem Ki1 e1 = fillItem Ki2 e2 → Ki1 = Ki2 := by
  intro h1 h2 h
  cases Ki1 <;> cases Ki2 <;> simp only [fillItem, reduceCtorEq] at h <;>
    (try simp only [Expr.App.injEq, Expr.Pair.injEq,
    Expr.If.injEq, Expr.Fst.injEq, Expr.Snd.injEq, Expr.Primitive1.injEq, Expr.Primitive2.injEq,
    Expr.ExternalOp.injEq, Expr.CmpXchg.injEq, Expr.ResolveProph.injEq] at h) <;>
    (try subst_eqs) <;> (first | (obtain ⟨_, _, _⟩ := h) | (obtain ⟨_, _⟩ := h) | skip) <;>
    subst_vars <;> simp_all [toVal]

theorem base_ctx_step_val (Ki : EctxItem) {e σ κ e2 σ2 efs} :
    BaseStep (fillItem Ki e) σ κ e2 σ2 efs → (toVal e).isSome := by
  intro h
  cases Ki <;> simp only [fillItem] at h <;> cases h <;> simp [toVal]

end step

/-! ## The iris-lean language instance -/

section language
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]

instance goose_toVal : ToVal Expr val where
  toVal := toVal
  ofVal := Val
  coe_of_toVal_eq_some := of_to_val
  toVal_coe _ := rfl

/-- The real GooseLang semantics as an iris-lean `EctxItemLanguage` (the trusted
model). Not an instance: the program logic uses the bounded layer
`goose_ectxi_lang` (`BoundedLang.lean`). -/
@[reducible] def gooseRealEctxiLang : EctxItemLanguage Expr EctxItem CfgState Observation val where
  toVal := toVal
  ofVal := Val
  coe_of_toVal_eq_some := of_to_val
  toVal_coe _ := rfl
  baseStep := fun (e, σ) κ (e', σ', efs) => BaseStep e σ κ e' σ' efs
  fillItem := fillItem
  fillItem_inj {Ki} := fillItem_inj Ki
  fillItem_val e Ki := fillItem_val Ki e
  fillItem_no_val_inj Ki1 Ki2 := fillItem_no_val_inj Ki1 Ki2
  val_stuck := val_base_stuck
  base_ctx_step_val {Ki} _ _ _ _ _ _ := base_ctx_step_val Ki

end language

end Perennial
