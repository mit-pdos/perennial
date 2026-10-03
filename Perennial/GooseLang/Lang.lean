/-
GooseLang. Port of `src/goose_lang/lang.v`.

GooseLang is an adaptation of HeapLang with extensions to model Go, including
a customizable FFI (foreign-function interface) for new primitive operations.

Differences from the Rocq version:
* There is no crash semantics (`ffi_crash_step`, `goose_crash`).
* The base step is an inductive relation (`base_step`) instead of being written
  with the `Transitions` monad, and FFI steps (`ffi_semantics.ffi_step`) are a
  plain relation.
* The real semantics is `goose_real_ectxi_lang`, an iris-lean
  `EctxItemLanguage` whose state is the pair `state × global_state`
  (`cfg_state`). It is a `def`, not an instance: the registered language
  instance (used by the program logic) is the step-bounded layer
  `goose_ectxi_lang` of `Perennial/GooseLang/BoundedLang.lean`, which adds a
  step fuel on top of `base_step` for time receipts. The adequacy theorems
  are transferred back to `goose_real_ectxi_lang` (`goose_adequacy`).
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
inductive binder where
  | BAnon
  | BNamed (s : String)
deriving DecidableEq, Inhabited, Repr

export binder (BAnon BNamed)

instance : Coe String binder := ⟨BNamed⟩

class ffi_syntax where
  ffi_opcode : Type
  [ffi_opcode_eq_dec : DecidableEq ffi_opcode]
  [ffi_opcode_countable : Pos.Countable ffi_opcode]
  ffi_val : Type
  [ffi_val_eq_dec : DecidableEq ffi_val]
  [ffi_val_countable : Pos.Countable ffi_val]

attribute [instance] ffi_syntax.ffi_opcode_eq_dec ffi_syntax.ffi_val_eq_dec
  ffi_syntax.ffi_opcode_countable ffi_syntax.ffi_val_countable
export ffi_syntax (ffi_opcode ffi_val)

class ffi_model where
  ffi_state : Type
  ffi_global_state : Type
  [ffi_state_inhabited : Inhabited ffi_state]
  [ffi_global_state_inhabited : Inhabited ffi_global_state]

attribute [instance] ffi_model.ffi_state_inhabited ffi_model.ffi_global_state_inhabited
export ffi_model (ffi_state ffi_global_state)

namespace slice
structure t where
  ptr : loc
  len : w64
  cap : w64
deriving DecidableEq, Inhabited

def nil : slice.t := ⟨null, 0, 0⟩
/-- Rocq `slice.mk`. -/
abbrev mk (ptr : loc) (len cap : w64) : slice.t := ⟨ptr, len, cap⟩
end slice

/-- Primitive (non-composite) values, injected into `val` by `LitV`. -/
inductive base_lit where
  | LitInt (n : w64)
  | LitInt32 (n : w32)
  | LitInt16 (n : w16)
  | LitBool (b : Bool)
  | LitByte (n : w8)
  | LitString (s : byte_string)
  | LitUnit
  | LitPoison
  | LitLoc (l : loc)
  | LitProphecy (p : proph_id)
  | LitSlice (s : slice.t)
deriving DecidableEq, Inhabited

inductive prim_op0 where
  /-- a stuck expression, to represent undefined behavior -/
  | PanicOp (s : String)
  /-- non-deterministically pick an integer -/
  | ArbitraryIntOp
deriving DecidableEq

inductive prim_op1 where
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

inductive prim_op2 where
  /-- pointer, value -/
  | FinishStoreOp
  /-- pointer, value; returns old value -/
  | AtomicSwapOp
  /-- pointer, value -/
  | AtomicAddOp
deriving DecidableEq

inductive go_operator where
  | GoEquals | GoLt | GoLe | GoGt | GoGe
  | GoPlus | GoSub | GoMul | GoDiv | GoRemainder
  | GoAnd | GoOr | GoXor | GoBitClear | GoShiftl | GoShiftr
deriving DecidableEq

inductive go_unary_operator where
  | GoPos | GoNeg | GoNot | GoComplement
deriving DecidableEq

inductive go_instruction where
  | AngelicExit
  | Convert (from_ to : go.type)
  | GoOp (o : go_operator) (t : go.type)
  | GoUnOp (o : go_unary_operator) (t : go.type)
  | CheckComparable (t : go.type)
  | GoLoad (t : go.type)
  | GoStore (t : go.type)
  | GoAlloc (t : go.type)
  | GoPrealloc
  | GoZeroVal (t : go.type)
  | FuncResolve (f : go_string) (type_args : List go.type)
  | MethodResolve (t : go.type) (m : go_string)
  | TypeAssert (t : go.type)
  | TypeAssert2 (t : go.type)
  | PackageInitCheck (pkg_name : go_string)
  | PackageInitStart (pkg_name : go_string)
  | PackageInitFinish (pkg_name : go_string)
  | GlobalVarAddr (var_name : go_string)
  | StructFieldRef (t : go.type) (f : go_string)
  | StructFieldGet (t : go.type) (f : go_string)
  | StructFieldSet (t : go.type) (f : go_string)
  /- can do slice, array, string, map, etc. for these ops; the internal ones
     should not be directly called by GooseLang. -/
  | InternalSliceLen
  | InternalSliceCap
  | InternalDynamicArrayAlloc (elem_type : go.type)
  | InternalMakeSlice
  | IndexRef (t : go.type)
  | Index (t : go.type)
  | Slice (t : go.type)
  | FullSlice (t : go.type)
  | ArraySet
  | ArrayLength
  /- internal steps; the Go map lookup has to be implemented as multiple
     instructions because it is not atomic. -/
  | InternalMapCheckKey (key_type : go.type)
  | InternalMapLookup
  | InternalMapInsert
  | InternalMapDelete
  | InternalMapLength
  | InternalMapForRange (key_type elem_type : go.type)
  | InternalMapMake
  | CompositeLiteral (t : go.type)
  | SelectStmt
  | InternalStringLen

noncomputable instance : DecidableEq go_instruction := fun a b => Classical.propDecidable (a = b)

section goose_syntax
variable [ext : ffi_syntax]

mutual
inductive expr where
  -- Values
  | Val (v : val)
  -- Base lambda calculus
  | Var (x : String)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  -- Products
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  -- Concurrency
  | Fork (e : expr)
  -- Heap-based primitives
  | Primitive0 (op : prim_op0)
  | Primitive1 (op : prim_op1) (e : expr)
  | Primitive2 (op : prim_op2) (e1 e2 : expr)
  /-- Compare-exchange -/
  | CmpXchg (e0 e1 e2 : expr)
  /-- External FFI operation -/
  | ExternalOp (op : ffi_opcode) (e : expr)
  -- Prophecy
  | NewProph
  | ResolveProph (e1 e2 : expr)
  | LiteralValue (l : List keyed_element)
  | SelectStmtClauses (default_handler : Option expr) (l : List comm_clause)

inductive val where
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  /-- Pointers to opaque types that FFI operations may return. -/
  | ExtV (ev : ffi_val)
  -- Go stuff
  | GoInstruction (o : go_instruction)
  | ArrayV (vs : List val)
  | InterfaceV (t : Option (go.type × val))
  | LiteralValueV (l : List keyed_element)
  | SelectStmtClausesV (default_handler : Option expr) (l : List comm_clause)
  | UntypedNil

/-- https://go.dev/ref/spec#Composite_literals -/
inductive keyed_element where
  | KeyedElement (k : Option key) (v : element)

inductive key where
  | KeyField (f : go_string)
  | KeyInteger (s : Int)
  | KeyExpression (t : go.type) (e : expr)
  | KeyLiteralValue (l : List keyed_element)

inductive element where
  | ElementExpression (t : go.type) (e : expr)
  | ElementLiteralValue (l : List keyed_element)

inductive comm_clause where
  | CommClause (c : comm_case) (body : expr)

/-- Variable bindings are desugared by goose into the body, so the send and
receives don't need to consider bindings or assignments. (`default` is
inlined into `SelectStmtClauses`.) -/
inductive comm_case where
  | SendCase (elem_type : go.type) (ch : expr) (e : expr)
  | RecvCase (elem_type : go.type) (ch : expr)
end

noncomputable instance : DecidableEq expr := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq val := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq keyed_element := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq key := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq element := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq comm_clause := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq comm_case := fun a b => Classical.propDecidable (a = b)

instance : Inhabited val := ⟨.LitV .LitUnit⟩
instance : Inhabited expr := ⟨.Val default⟩

end goose_syntax

export expr (Val Var Rec App If Pair Fst Snd Fork Primitive0 Primitive1 Primitive2 CmpXchg
  ExternalOp NewProph ResolveProph LiteralValue SelectStmtClauses)
export val (LitV RecV PairV InjLV InjRV ExtV GoInstruction ArrayV InterfaceV LiteralValueV
  SelectStmtClausesV UntypedNil)
export keyed_element (KeyedElement)
export key (KeyField KeyInteger KeyExpression KeyLiteralValue)
export element (ElementExpression ElementLiteralValue)
export comm_clause (CommClause)
export comm_case (SendCase RecvCase)
export base_lit (LitInt LitInt32 LitInt16 LitBool LitByte LitString LitUnit LitPoison LitLoc
  LitProphecy LitSlice)
export go_operator (GoEquals GoLt GoLe GoGt GoGe GoPlus GoSub GoMul GoDiv GoRemainder GoAnd
  GoOr GoXor GoBitClear GoShiftl GoShiftr)
export go_unary_operator (GoPos GoNeg GoNot GoComplement)
export go_instruction (AngelicExit Convert GoOp GoUnOp CheckComparable GoLoad GoStore GoAlloc
  GoPrealloc GoZeroVal FuncResolve MethodResolve TypeAssert TypeAssert2 PackageInitCheck
  PackageInitStart PackageInitFinish GlobalVarAddr StructFieldRef StructFieldGet StructFieldSet
  InternalSliceLen InternalSliceCap InternalDynamicArrayAlloc InternalMakeSlice IndexRef Index
  Slice FullSlice ArraySet ArrayLength InternalMapCheckKey InternalMapLookup InternalMapInsert
  InternalMapDelete InternalMapLength InternalMapForRange InternalMapMake CompositeLiteral
  SelectStmt InternalStringLen)

section derived
variable [ext : ffi_syntax]

instance : Coe val expr := ⟨Val⟩
instance : Coe String expr := ⟨Var⟩
instance : CoeFun expr (fun _ => expr → expr) := ⟨App⟩

abbrev Panic (s : String) : expr := Primitive0 (.PanicOp s)
abbrev ArbitraryInt : expr := Primitive0 .ArbitraryIntOp
abbrev Alloc (e : expr) : expr := Primitive1 .AllocOp e
abbrev PrepareWrite (e : expr) : expr := Primitive1 .PrepareWriteOp e
abbrev StartRead (e : expr) : expr := Primitive1 .StartReadOp e
abbrev FinishRead (e : expr) : expr := Primitive1 .FinishReadOp e
abbrev Load (e : expr) : expr := Primitive1 .LoadOp e
abbrev FinishStore (e1 e2 : expr) : expr := Primitive2 .FinishStoreOp e1 e2
abbrev AtomicSwap (e1 e2 : expr) : expr := Primitive2 .AtomicSwapOp e1 e2
abbrev AtomicAdd (e1 e2 : expr) : expr := Primitive2 .AtomicAddOp e1 e2

abbrev Lam (x : binder) (e : expr) : expr := Rec BAnon x e
abbrev Let (x : binder) (e1 e2 : expr) : expr := App (Lam x e2) e1
abbrev Seq (e1 e2 : expr) : expr := Let BAnon e1 e2
abbrev LamV (x : binder) (e : expr) : val := RecV BAnon x e
/-- Compare-and-set returns just a boolean indicating success or failure. -/
abbrev CAS (l e1 e2 : expr) : expr := Snd (CmpXchg l e1 e2)

def Store : val :=
  LamV "l" (Lam "v" (Seq (PrepareWrite (Var "l")) (FinishStore (Var "l") (Var "v"))))

def Read : val :=
  LamV "l" (Let "v" (StartRead (Var "l")) (Seq (FinishRead (Var "l")) (Var "v")))

end derived

namespace func
structure t [ffi_syntax] where
  f : binder
  x : binder
  e : expr

def nil [ffi_syntax] : func.t := ⟨BAnon, BAnon, Val (LitV LitPoison)⟩

instance [ffi_syntax] : Inhabited func.t := ⟨nil⟩
/-- Rocq `func.mk`. -/
abbrev mk [ffi_syntax] (f x : binder) (e : expr) : func.t := ⟨f, x, e⟩
end func

/-- `GoGlobalContext` contains the `into_val` function. This allows for the Go
semantics to state constraints on `into_val` (e.g. injectivity for certain
types). -/
class GoGlobalContext [ffi_syntax] where
  into_val : {V : Type} → V → val
  into_val_inj_loc : Function.Injective (into_val (V := loc))
  into_val_inj_bool : Function.Injective (into_val (V := Bool))
  into_val_inj_proph_id : Function.Injective (into_val (V := proph_id))
  into_val_inj_w64 : Function.Injective (into_val (V := w64))
  into_val_inj_w8 : Function.Injective (into_val (V := w8))

export GoGlobalContext (into_val)

/-- `# x` is `into_val x`. -/
scoped prefix:max "#" => into_val

/-- `GoLocalContext` contains several low-level Go functions for typed memory
access, map updates, etc. -/
class GoLocalContext [ffi_syntax] where
  is_go_step_pure : go_instruction → val → expr → Prop

export GoLocalContext (is_go_step_pure)

namespace chan
abbrev t := loc
def nil : chan.t := null
end chan

namespace interface

structure t_ok [ffi_syntax] where
  ty : go.type
  v : val

inductive t [ffi_syntax] where
  | ok (i : t_ok)
  | nil

export t (ok nil)

abbrev mk_ok [ffi_syntax] (ty : go.type) (v : val) : t := .ok ⟨ty, v⟩
/-- Rocq `interface.mk`. -/
abbrev mk [ffi_syntax] (ty : go.type) (v : val) : t_ok := ⟨ty, v⟩

end interface

namespace array
structure t (V : Type) (n : Int) where
  mk ::
  arr : List V
/-- Rocq `array.mk n arr`. -/
abbrev mk {V : Type} (n : Int) (arr : List V) : array.t V n := ⟨arr⟩
end array

/-! ## State -/

inductive naMode where
  | Writing
  | Reading (n : Nat)
deriving DecidableEq, Inhabited

export naMode (Writing Reading)

abbrev nonAtomic (T : Type) := naMode × T

def Free {T} (v : T) : nonAtomic T := (Reading 0, v)

class ZeroVal (V : Type) where
  zero_val_def : V

export ZeroVal (zero_val_def)

abbrev zero_val (V : Type) [ZeroVal V] : V := ZeroVal.zero_val_def

section zero_val_instances
variable [ffi_syntax]
instance : ZeroVal loc := ⟨null⟩
instance : ZeroVal w64 := ⟨0⟩
instance : ZeroVal w32 := ⟨0⟩
instance : ZeroVal w16 := ⟨0⟩
instance : ZeroVal w8 := ⟨0⟩
instance : ZeroVal Unit := ⟨()⟩
instance : ZeroVal Bool := ⟨false⟩
instance : ZeroVal go_string := ⟨[]⟩
instance : ZeroVal func.t := ⟨func.nil⟩
instance {V} [ZeroVal V] (n : Int) : ZeroVal (array.t V n) :=
  ⟨⟨List.replicate n.toNat (zero_val V)⟩⟩
instance : ZeroVal slice.t := ⟨slice.nil⟩
instance : ZeroVal interface.t := ⟨.nil⟩
instance : ZeroVal proph_id := ⟨1⟩
end zero_val_instances

section state
variable [ffi_syntax] [ffi_model]

structure GoState where
  go_lctx : GoLocalContext
  package_state : gmap go_string Bool

instance : Inhabited GoLocalContext := ⟨⟨fun _ _ _ => False⟩⟩
instance : Inhabited GoState := ⟨⟨default, ∅⟩⟩

structure state where
  heap : gmap loc (nonAtomic val)
  go_state : GoState
  world : ffi_state

structure global_state where
  global_world : ffi_global_state
  used_proph_id : gset proph_id

instance : Inhabited state := ⟨⟨∅, default, default⟩⟩
instance : Inhabited global_state := ⟨⟨default, ∅⟩⟩

/-- The state of the iris-lean language: Rocq's `state * global_state`. -/
abbrev cfg_state := state × global_state

/-- An observation associates a prophecy variable to the value it is resolved to. -/
abbrev observation := proph_id × val

end state

def is_go_step [ffi_syntax] [GoGlobalContext] [GoLocalContext]
    (op : go_instruction) (arg : val) (e' : expr) (s s' : gmap go_string Bool) : Prop :=
  match op with
  | PackageInitCheck p => arg = #() ∧ e' = Val #((s !! p).getD false) ∧ s' = s
  | PackageInitStart p => arg = #() ∧ e' = Val #() ∧ s' = <[p := false]> s
  | PackageInitFinish p => arg = #() ∧ e' = Val #() ∧ s' = <[p := true]> s
  | _ => GoLocalContext.is_go_step_pure op arg e' ∧ s = s'

/-- FFI semantics: `ffi_step op v σg e' σg'` says that the external operation
`op` applied to `v` in state `σg` can produce `e'` and state `σg'`. -/
class ffi_semantics (ext : ffi_syntax) (ffi : ffi_model) where
  ffi_step : ffi_opcode → val → cfg_state → expr → cfg_state → Prop

export ffi_semantics (ffi_step)

/-! ## Evaluation contexts and substitution -/

section lang
variable [ext : ffi_syntax]

def to_val : expr → Option val
  | Val v => some v
  | _ => none

@[simp] theorem to_of_val (v : val) : to_val (Val v) = some v := rfl

theorem of_to_val {e : expr} {v : val} : to_val e = some v → Val v = e := by
  cases e <;> simp [to_val]; exact Eq.symm

inductive ectx_item where
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | IfCtx (e1 e2 : expr)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | Primitive1Ctx (op : prim_op1)
  | Primitive2LCtx (op : prim_op2) (e2 : expr)
  | Primitive2RCtx (op : prim_op2) (v1 : val)
  | ExternalOpCtx (op : ffi_opcode)
  | CmpXchgLCtx (e1 e2 : expr)
  | CmpXchgMCtx (v1 : val) (e2 : expr)
  | CmpXchgRCtx (v1 v2 : val)
  | ResolveProphLCtx (v2 : val)
  | ResolveProphRCtx (e1 : expr)

open ectx_item in
def fill_item (Ki : ectx_item) (e : expr) : expr :=
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
def subst (x : String) (v : val) : expr → expr
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
  | LiteralValue l => LiteralValue (subst_keyed_elements x v l)
  | SelectStmtClauses d l => SelectStmtClauses (subst_opt x v d) (subst_comm_clauses x v l)

def subst_opt (x : String) (v : val) : Option expr → Option expr
  | none => none
  | some e => some (subst x v e)

def subst_keyed_elements (x : String) (v : val) : List keyed_element → List keyed_element
  | [] => []
  | ke :: l => subst_keyed_element x v ke :: subst_keyed_elements x v l

def subst_keyed_element (x : String) (v : val) : keyed_element → keyed_element
  | KeyedElement k el => KeyedElement (subst_opt_key x v k) (subst_element x v el)

def subst_opt_key (x : String) (v : val) : Option key → Option key
  | none => none
  | some (KeyExpression t e) => some (KeyExpression t (subst x v e))
  | some (KeyLiteralValue l) => some (KeyLiteralValue (subst_keyed_elements x v l))
  | some k => some k

def subst_element (x : String) (v : val) : element → element
  | ElementExpression t e => ElementExpression t (subst x v e)
  | ElementLiteralValue l => ElementLiteralValue (subst_keyed_elements x v l)

def subst_comm_clauses (x : String) (v : val) : List comm_clause → List comm_clause
  | [] => []
  | c :: l => subst_comm_clause x v c :: subst_comm_clauses x v l

def subst_comm_clause (x : String) (v : val) : comm_clause → comm_clause
  | CommClause (SendCase t b e) body => CommClause (SendCase t (subst x v b) (subst x v e)) (subst x v body)
  | CommClause (RecvCase t e) body => CommClause (RecvCase t (subst x v e)) (subst x v body)
end

def subst' (mx : binder) (v : val) : expr → expr :=
  match mx with
  | BNamed x => subst x v
  | BAnon => id

end lang

/-! ## The base step relation -/

section step
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_semantics ext ffi] [GoGlobalContext]

def state_init_heap (l : loc) (v : val) (σ : state) : state :=
  { σ with heap := {[l := Free v]} ∪ σ.heap }

def is_Writing {A} (mna : Option (nonAtomic A)) : Prop := ∃ x, mna = some (Writing, x)

/-- `l` is the start of a fresh block in `σg`. -/
def isFresh (σg : cfg_state) (l : loc) : Prop :=
  (∀ i : Int, l +ₗ i ≠ null ∧ σg.1.heap !! (l +ₗ i) = none) ∧ l.addr_offset = 0

def atomic_add_eval (v1 v2 : val) : Option val :=
  match v1, v2 with
  | LitV (LitInt n1), LitV (LitInt n2) => some #(n1 + n2)
  | LitV (LitInt32 n1), LitV (LitInt32 n2) => some #(n1 + n2)
  | LitV (LitInt16 n1), LitV (LitInt16 n2) => some #(n1 + n2)
  | LitV (LitByte n1), LitV (LitByte n2) => some #(n1 + n2)
  | _, _ => none

def set_heap (f : gmap loc (nonAtomic val) → gmap loc (nonAtomic val)) (σg : cfg_state) :
    cfg_state :=
  ({ σg.1 with heap := f σg.1.heap }, σg.2)

open Classical in
/-- Rocq `base_trans`/`base_step`, as an inductive relation:
`base_step e σg κs e' σg' efs`. -/
inductive base_step : expr → cfg_state → List observation → expr → cfg_state → List expr → Prop
  | RecS f x e σg : base_step (Rec f x e) σg [] (Val (RecV f x e)) σg []
  | PairS v1 v2 σg : base_step (Pair (Val v1) (Val v2)) σg [] (Val (PairV v1 v2)) σg []
  | BetaS f x e1 v2 σg :
      base_step (App (Val (RecV f x e1)) (Val v2)) σg []
        (subst' x v2 (subst' f (RecV f x e1) e1)) σg []
  | IfTrueS e1 e2 σg : base_step (If (Val #true) e1 e2) σg [] e1 σg []
  | IfFalseS e1 e2 σg : base_step (If (Val #false) e1 e2) σg [] e2 σg []
  | FstS v1 v2 σg : base_step (Fst (Val (PairV v1 v2))) σg [] (Val v1) σg []
  | SndS v1 v2 σg : base_step (Snd (Val (PairV v1 v2))) σg [] (Val v2) σg []
  | ForkS e σg : base_step (Fork e) σg [] (Val #()) σg [e]
  | ArbitraryIntS (x : w64) σg : base_step ArbitraryInt σg [] (Val #x) σg []
  | AllocS v l σg :
      isFresh σg l →
      base_step (Alloc (Val v)) σg [] (Val #l) (state_init_heap l v σg.1, σg.2) []
  /-- non-atomic load part 1 (used for map accesses) -/
  | StartReadS l n v σg :
      σg.1.heap !! l = some (Reading n, v) →
      base_step (StartRead (Val #l)) σg [] (Val v) (set_heap (<[l := (Reading (n + 1), v)]> ·) σg) []
  /-- non-atomic load part 2 -/
  | FinishReadS l n v σg :
      σg.1.heap !! l = some (Reading (n + 1), v) →
      base_step (FinishRead (Val #l)) σg [] (Val #()) (set_heap (<[l := (Reading n, v)]> ·) σg) []
  /-- atomic load (used for most normal Go loads) -/
  | LoadS l n v σg :
      σg.1.heap !! l = some (Reading n, v) →
      base_step (Load (Val #l)) σg [] (Val v) σg []
  /-- non-atomic write part 1 -/
  | PrepareWriteS l v σg :
      σg.1.heap !! l = some (Reading 0, v) →
      base_step (PrepareWrite (Val #l)) σg [] (Val #()) (set_heap (<[l := (Writing, v)]> ·) σg) []
  /-- non-atomic write part 2 -/
  | FinishStoreS l v σg :
      is_Writing (σg.1.heap !! l) →
      base_step (FinishStore (Val #l) (Val v)) σg [] (Val #()) (set_heap (<[l := Free v]> ·) σg) []
  | AtomicSwapS l v0 v σg :
      σg.1.heap !! l = some (Reading 0, v0) →
      base_step (AtomicSwap (Val #l) (Val v)) σg [] (Val v0) (set_heap (<[l := Free v]> ·) σg) []
  | AtomicAddS l v0 v v' σg :
      σg.1.heap !! l = some (Reading 0, v0) →
      atomic_add_eval v0 v = some v' →
      base_step (AtomicAdd (Val #l) (Val v)) σg [] (Val v') (set_heap (<[l := Free v']> ·) σg) []
  | ExternalOpS op v e' σg σg' :
      ffi_step op v σg e' σg' →
      base_step (ExternalOp op (Val v)) σg [] e' σg' []
  | GoInstructionS op arg e' s' σg :
      @is_go_step _ _ σg.1.go_state.go_lctx op arg e' σg.1.go_state.package_state s' →
      base_step (App (Val (GoInstruction op)) (Val arg)) σg [] e'
        ({ σg.1 with go_state := { σg.1.go_state with package_state := s' } }, σg.2) []
  | CmpXchgFailS l n vl v1 v2 σg :
      σg.1.heap !! l = some (Reading n, vl) →
      vl ≠ v1 →
      base_step (CmpXchg (Val #l) (Val v1) (Val v2)) σg [] (Val (PairV vl #false)) σg []
  | CmpXchgSucS l vl v1 v2 σg :
      σg.1.heap !! l = some (Reading 0, vl) →
      vl = v1 →
      base_step (CmpXchg (Val #l) (Val v1) (Val v2)) σg [] (Val (PairV vl #true))
        (set_heap (<[l := Free v2]> ·) σg) []
  | NewProphS p σg :
      p ∉ σg.2.used_proph_id →
      base_step NewProph σg [] (Val #p)
        (σg.1, { σg.2 with used_proph_id := {[p := ()]} ∪ σg.2.used_proph_id }) []
  | ResolveProphS (p : proph_id) w σg :
      base_step (ResolveProph (Val #p) (Val w)) σg [(p, w)] (Val #()) σg []
  | LiteralValueS l σg : base_step (LiteralValue l) σg [] (Val (LiteralValueV l)) σg []
  | SelectStmtClausesS d cs σg :
      base_step (SelectStmtClauses d cs) σg [] (Val (SelectStmtClausesV d cs)) σg []

theorem val_base_stuck {e σ κ e' σ' efs} : base_step e σ κ e' σ' efs → to_val e = none := by
  intro h; cases h <;> rfl

theorem fill_item_val (Ki : ectx_item) (e : expr) :
    (to_val (fill_item Ki e)).isSome → (to_val e).isSome := by
  cases Ki <;> simp [fill_item, to_val]

theorem fill_item_inj (Ki : ectx_item) : Function.Injective (fill_item Ki) := by
  intro e1 e2 h; cases Ki <;> simp_all [fill_item]

theorem fill_item_no_val_inj (Ki1 Ki2 : ectx_item) {e1 e2 : expr} :
    to_val e1 = none → to_val e2 = none → fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2 := by
  intro h1 h2 h
  cases Ki1 <;> cases Ki2 <;> simp only [fill_item, reduceCtorEq] at h <;>
    (try simp only [expr.App.injEq, expr.Pair.injEq,
    expr.If.injEq, expr.Fst.injEq, expr.Snd.injEq, expr.Primitive1.injEq, expr.Primitive2.injEq,
    expr.ExternalOp.injEq, expr.CmpXchg.injEq, expr.ResolveProph.injEq] at h) <;>
    (try subst_eqs) <;> (first | (obtain ⟨_, _, _⟩ := h) | (obtain ⟨_, _⟩ := h) | skip) <;>
    subst_vars <;> simp_all [to_val]

theorem base_ctx_step_val (Ki : ectx_item) {e σ κ e2 σ2 efs} :
    base_step (fill_item Ki e) σ κ e2 σ2 efs → (to_val e).isSome := by
  intro h
  cases Ki <;> simp only [fill_item] at h <;> cases h <;> simp [to_val]

end step

/-! ## The iris-lean language instance -/

section language
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_semantics ext ffi] [GoGlobalContext]

instance goose_toVal : ToVal expr val where
  toVal := to_val
  ofVal := Val
  coe_of_toVal_eq_some := of_to_val
  toVal_coe _ := rfl

/-- The real GooseLang semantics as an iris-lean `EctxItemLanguage` (the trusted
model). Not an instance: the program logic uses the bounded layer
`goose_ectxi_lang` (`BoundedLang.lean`). -/
@[reducible] def goose_real_ectxi_lang : EctxItemLanguage expr ectx_item cfg_state observation val where
  toVal := to_val
  ofVal := Val
  coe_of_toVal_eq_some := of_to_val
  toVal_coe _ := rfl
  baseStep := fun (e, σ) κ (e', σ', efs) => base_step e σ κ e' σ' efs
  fillItem := fill_item
  fillItem_inj {Ki} := fill_item_inj Ki
  fillItem_val e Ki := fill_item_val Ki e
  fillItem_no_val_inj Ki1 Ki2 := fill_item_no_val_inj Ki1 Ki2
  val_stuck := val_base_stuck
  base_ctx_step_val {Ki} _ _ _ _ _ _ := base_ctx_step_val Ki

end language

end Perennial
