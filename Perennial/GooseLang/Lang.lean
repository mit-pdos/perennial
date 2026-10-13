/-
GooseLang.

GooseLang is an adaptation of HeapLang with extensions to model Go, including
a customizable FFI (foreign-function interface) for new primitive operations.

* There is no crash semantics (`ffi_crash_step`, `goose_crash`).
* The base step is an inductive relation (`base_step`), and FFI steps (`FfiSemantics.ffi_step`) are a
  plain relation.
* The real semantics is `gooseRealEctxiLang`, an iris-lean
  `EctxItemLanguage` whose state is the pair `state × GlobalState`
  (`CfgState`). It is a `def`, not an instance: the registered language
  instance (used by the program logic) is the step-bounded layer
  `goose_ectxi_lang` of `Perennial/GooseLang/BoundedLang.lean`, which adds a
  step fuel on top of `base_step` for time receipts. The adequacy theorems
  are transferred back to `gooseRealEctxiLang` (`goose_adequacy`).
* Equality on the syntax is decided classically; nothing downstream computes with it.
-/
module

public import Iris.ProgramLogic.EctxiLanguage
public import Iris.ProgramLogic.Language
public import Perennial.Std.GMap
public import Perennial.Std.Countable
public import Perennial.GooseLang.Locations
public import Perennial.Golang.Defn.PreLang

@[expose] public section

namespace Perennial

open Iris.ProgramLogic

/-! ## Expressions and values -/

abbrev proph_id := Nat

/-- A binder: anonymous or named. -/
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
  /-- A cell of memory that holds no value of its own: one of the cells after the first of
  a value that is not represented as bytes (`Encoding.cell`), padding, or the cells of a
  fresh allocation before its first store. No load decodes it (`decode`). -/
  | LitTail
deriving DecidableEq, Inhabited

/-- How a value occupies the heap cells from its address on (a heap cell is a byte of
memory, `Golang/Defn/Layout.lean`): `encode`, `decode`. -/
inductive Encoding where
  /-- the `n` little-endian bytes (`LitByte` cells) of an integer of `n ∈ {1, 2, 4, 8}`
  bytes -/
  | word (n : Nat)
  /-- the whole value in the first cell and a `LitTail` in each of the `k - 1` cells after
  it: a value of size `k ≥ 1` that is not represented as bytes (a pointer, a string, …) -/
  | cell (k : Nat)
deriving DecidableEq

/-- The number of cells of an encoded value. -/
def Encoding.size : Encoding → Nat
  | .word n => n
  | .cell k => k

/-- The alignment the atomic operations need: an access of `n ≤ 8` bytes is atomic on
amd64 only if it does not straddle an `n`-byte boundary (`Go memory model`: an access
of at most a machine word at an aligned address). -/
def Encoding.align : Encoding → Nat
  | .word n => n
  | .cell k => min k 8

/-- The one-operand memory operations on an encoded value (`Encoding`), on all its cells
at once: the two halves of a non-atomic read (`startRead`, `finishRead`, which count a
reader on each cell, so that a concurrent write of any of them is stuck), the first half
of a non-atomic write (`prepareWrite`), and an atomic load (`load`). -/
inductive MemOp1 where
  | startRead | finishRead | prepareWrite | load
deriving DecidableEq

/-- The two-operand memory operations on an encoded value: the second half of a
non-atomic write (`finishStore`) and the atomic swap, add and compare-exchange (the
second operand the pair of the old and the new value). -/
inductive MemOp2 where
  | finishStore | swap | add | cmpxchg
deriving DecidableEq

inductive PrimOp0 where
  /-- a stuck expression, to represent undefined behavior -/
  | PanicOp (s : String)
  /-- non-deterministically pick an integer -/
  | ArbitraryIntOp
  /-- the end of a forked thread: `Fork e` spawns `e ;; ThreadExit`, and this step
  decrements the thread count of the global state (see `GlobalState.threads`) -/
  | ThreadExitOp
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
  /-- a memory operation on the encoded value at a location (`MemOp1`) -/
  | MemOp1Op (op : MemOp1) (enc : Encoding)
  /-- stuck unless the location is a cell of the heap (`unsafe.Add`) -/
  | CheckCellOp
deriving DecidableEq

inductive PrimOp2 where
  /-- pointer, value -/
  | FinishStoreOp
  /-- pointer, value; returns old value -/
  | AtomicSwapOp
  /-- pointer, value -/
  | AtomicAddOp
  /-- allocation of a contiguous block (the pair of the number of cells and the alignment,
  the initial value of each cell) -/
  | AllocNOp
  /-- a memory operation on the encoded value at a location (`MemOp2`) -/
  | MemOp2Op (op : MemOp2) (enc : Encoding)
deriving DecidableEq

inductive GoOperator where
  | GoEquals | GoLt | GoLe | GoGt | GoGe
  | GoPlus | GoSub | GoMul | GoDiv | GoRemainder
  | GoAnd | GoOr | GoXor | GoBitClear
deriving DecidableEq

inductive GoShiftOperator where
  | GoShiftl | GoShiftr
deriving DecidableEq

inductive GoUnaryOperator where
  | GoPos | GoNeg | GoNot | GoComplement
deriving DecidableEq

inductive GoInstruction where
  | AngelicExit
  | Convert (from_ to : go.GoType)
  | GoOp (o : GoOperator) (t : go.GoType)
  /-- `x << y` / `x >> y` with `x : t` and `y : count_t`: the two operands of a shift need not
  have the same type, so the instruction carries both, and the semantics chooses what to do
  with the count (`go.UntypedIntSemantics.shift_count_untyped_int`, ...). -/
  | GoShift (o : GoShiftOperator) (t count_t : go.GoType)
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
  LitProphecy LitSlice LitTail)
export GoOperator (GoEquals GoLt GoLe GoGt GoGe GoPlus GoSub GoMul GoDiv GoRemainder GoAnd
  GoOr GoXor GoBitClear)
export GoShiftOperator (GoShiftl GoShiftr)
export GoUnaryOperator (GoPos GoNeg GoNot GoComplement)
export GoInstruction (AngelicExit Convert GoOp GoShift GoUnOp CheckComparable GoLoad GoStore GoAlloc
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
/-- The last step of a forked thread (`ForkS` spawns `Seq e ThreadExit`): a no-op
that decrements the thread count `GlobalState.threads`. -/
abbrev ThreadExit : Expr := Primitive0 .ThreadExitOp
abbrev Alloc (e : Expr) : Expr := Primitive1 .AllocOp e
abbrev PrepareWrite (e : Expr) : Expr := Primitive1 .PrepareWriteOp e
abbrev StartRead (e : Expr) : Expr := Primitive1 .StartReadOp e
abbrev FinishRead (e : Expr) : Expr := Primitive1 .FinishReadOp e
abbrev Load (e : Expr) : Expr := Primitive1 .LoadOp e
abbrev FinishStore (e1 e2 : Expr) : Expr := Primitive2 .FinishStoreOp e1 e2
abbrev AtomicSwap (e1 e2 : Expr) : Expr := Primitive2 .AtomicSwapOp e1 e2
abbrev AtomicAdd (e1 e2 : Expr) : Expr := Primitive2 .AtomicAddOp e1 e2
/-- `AllocN (n, a) v`: a fresh block of `n` cells (one `LitTail` cell if `n = 0`), each
holding `v`, at an offset aligned to `a` (`AllocNS`). -/
abbrev AllocN (e1 e2 : Expr) : Expr := Primitive2 .AllocNOp e1 e2
abbrev StartReadN (enc : Encoding) (e : Expr) : Expr := Primitive1 (.MemOp1Op .startRead enc) e
abbrev FinishReadN (enc : Encoding) (e : Expr) : Expr := Primitive1 (.MemOp1Op .finishRead enc) e
abbrev PrepareWriteN (enc : Encoding) (e : Expr) : Expr := Primitive1 (.MemOp1Op .prepareWrite enc) e
/-- An atomic load of the encoded value at an aligned location. -/
abbrev LoadN (enc : Encoding) (e : Expr) : Expr := Primitive1 (.MemOp1Op .load enc) e
abbrev FinishStoreN (enc : Encoding) (e1 e2 : Expr) : Expr := Primitive2 (.MemOp2Op .finishStore enc) e1 e2
/-- An atomic swap, returning the old value. -/
abbrev SwapN (enc : Encoding) (e1 e2 : Expr) : Expr := Primitive2 (.MemOp2Op .swap enc) e1 e2
/-- An atomic add, returning the new value. -/
abbrev AddN (enc : Encoding) (e1 e2 : Expr) : Expr := Primitive2 (.MemOp2Op .add enc) e1 e2
/-- `CmpXchgN enc l (old, new)`: an atomic compare-exchange, returning the old value and
whether it wrote. -/
abbrev CmpXchgN (enc : Encoding) (e1 e2 : Expr) : Expr := Primitive2 (.MemOp2Op .cmpxchg enc) e1 e2
/-- `CheckCell l`: `#()` if `l` is a cell of the heap, else stuck. -/
abbrev CheckCell (e : Expr) : Expr := Primitive1 .CheckCellOp e

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

/-- The non-atomic store of an encoded value: all its cells become `Writing`, then are
written. -/
def StoreN (enc : Encoding) : val :=
  LamV "l" (Lam "v" (Seq (PrepareWriteN enc (Var "l")) (FinishStoreN enc (Var "l") (Var "v"))))

/-- The non-atomic load of an encoded value: a reader is counted on each of its cells
while it is read. -/
def ReadN (enc : Encoding) : val :=
  LamV "l" (Let "v" (StartReadN enc (Var "l")) (Seq (FinishReadN enc (Var "l")) (Var "v")))

end derived

namespace func
structure _root_.Perennial.GoFunc [FfiSyntax] where
  f : Binder
  x : Binder
  e : Expr

def nil [FfiSyntax] : GoFunc := ⟨BAnon, BAnon, Val (LitV LitPoison)⟩

instance [FfiSyntax] : Inhabited GoFunc := ⟨nil⟩
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
abbrev mk [FfiSyntax] (ty : go.GoType) (v : val) : GoInterfaceOk := ⟨ty, v⟩

end interface

namespace array
structure _root_.Perennial.GoArray (V : Type) (n : Int) where
  mk ::
  arr : List V
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
  /-- The number of live threads: the main thread (counted for the whole
  execution) and the forked threads that have not reached their `ThreadExit`.
  `ForkS` increments it and `ThreadExitS` decrements it; no other step changes
  it (`FfiSemantics.ffi_step_threads` for the FFI). A configuration whose only
  thread is the main thread has `threads = 1`. The bounded semantics
  (`BoundedLang.lean`) and the adequacy theorems bound it: see "thread tokens"
  in `Threads.lean`. -/
  threads : Nat

instance : Inhabited state := ⟨⟨∅, default, default⟩⟩
instance : Inhabited GlobalState := ⟨⟨default, ∅, 1⟩⟩

/-- The state of the iris-lean language: the local and the global state. -/
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
  /-- An FFI step does not change the thread count. -/
  ffi_step_threads : ∀ {op v σg e' σg'}, ffi_step op v σg e' σg' → σg'.2.threads = σg.2.threads

export FfiSemantics (ffi_step ffi_step_threads)

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

/-- The heap containing `vs` at `l, l +ₗ 1, ...`. -/
def heapArray {V : Type} (l : Loc) : List V → GMap Loc V
  | [] => ∅
  | v :: vs => <[l := v]> (heapArray (l +ₗ 1) vs)

/-- The `n` little-endian bytes of `z` (mod `2^(8n)`). -/
def leBytes : Nat → Int → List w8
  | 0, _ => []
  | n + 1, z => BitVec.ofInt 8 z :: leBytes n (z / 256)

/-- The value of little-endian bytes. -/
def leInt (bs : List w8) : Int :=
  bs.foldr (fun b acc => (b.toNat : Int) + 256 * acc) 0

theorem leBytes_length (n : Nat) (z : Int) : (leBytes n z).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [leBytes, ih]

theorem emod_256_mul (z m : Int) :
    z % (256 * m) = z % 256 + 256 * ((z / 256) % m) := by
  have e1 := Int.emod_def z (256 * m)
  have e2 := Int.emod_def z 256
  have e3 := Int.emod_def (z / 256) m
  rw [← Int.ediv_ediv_of_nonneg (by decide : (0 : Int) ≤ 256)] at e1
  rw [e1, e2, e3]
  generalize z / 256 = q
  generalize q / m = r
  rw [Int.mul_assoc]
  generalize m * r = t
  omega

theorem ofInt8_emod_256_mul (z m : Int) :
    BitVec.ofInt 8 (z % (256 * m)) = BitVec.ofInt 8 z := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  congr 1
  rw [emod_256_mul]
  have h0 := Int.emod_nonneg z (by decide : (256 : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos z (by decide : (0 : Int) < 256)
  show (z % 256 + 256 * (z / 256 % m)) % (2 ^ 8 : Nat) = z % (2 ^ 8 : Nat)
  rw [show ((2 ^ 8 : Nat) : Int) = 256 by decide, Int.add_mul_emod_self_left, Int.emod_emod_of_dvd _ (by decide)]

/-- The bytes of `z` depend only on `z` modulo `2^(8n)`. -/
theorem leBytes_emod (n : Nat) (z : Int) : leBytes n (z % 2 ^ (8 * n)) = leBytes n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [show 8 * (n + 1) = 8 + 8 * n by omega, Int.pow_add, show (2 : Int) ^ 8 = 256 by decide]
    simp only [leBytes, ofInt8_emod_256_mul]
    congr 1
    rw [emod_256_mul]
    have h0 := Int.emod_nonneg z (by decide : (256 : Int) ≠ 0)
    have h1 := Int.emod_lt_of_pos z (by decide : (0 : Int) < 256)
    rw [show (z % 256 + 256 * (z / 256 % 2 ^ (8 * n))) / 256 = z / 256 % 2 ^ (8 * n) by
      rw [Int.add_mul_ediv_left _ _ (by decide)]
      rw [Int.ediv_eq_zero_of_lt h0 h1, Int.zero_add]]
    exact ih (z / 256)

/-- Decoding the bytes of `z` gives `z` modulo `2^(8n)`. -/
theorem leInt_leBytes (n : Nat) (z : Int) : leInt (leBytes n z) = z % 2 ^ (8 * n) := by
  induction n generalizing z with
  | zero => simp [leBytes, leInt, Int.emod_one]
  | succ n ih =>
    have ih' := ih (z / 256)
    simp only [leBytes, leInt, List.foldr_cons] at *
    rw [ih']
    have h8 : ((BitVec.ofInt 8 z).toNat : Int) = z % 256 := by
      rw [BitVec.toNat_ofInt]
      have := Int.emod_nonneg z (by decide : (256 : Int) ≠ 0)
      simp only [Int.toNat_of_nonneg (by omega : 0 ≤ z % (2 ^ 8 : Nat))]
      rfl
    rw [h8, show 8 * (n + 1) = 8 + 8 * n by omega, Int.pow_add,
      show (2 : Int) ^ 8 = 256 by decide, emod_256_mul]

/-- A word of `n` bytes as a value: a `w8`, `w16`, `w32` or `w64`. -/
def wordLit (n : Nat) (z : Int) : val :=
  match n with
  | 1 => LitV (LitByte (BitVec.ofInt 8 z))
  | 2 => LitV (LitInt16 (BitVec.ofInt 16 z))
  | 4 => LitV (LitInt32 (BitVec.ofInt 32 z))
  | _ => LitV (LitInt (BitVec.ofInt 64 z))

/-- The (unsigned) value of a word value of `n` bytes. -/
def wordLitZ? (n : Nat) (v : val) : Option Int :=
  match n, v with
  | 1, LitV (LitByte x) => some x.toNat
  | 2, LitV (LitInt16 x) => some x.toNat
  | 4, LitV (LitInt32 x) => some x.toNat
  | 8, LitV (LitInt x) => some x.toNat
  | _, _ => none

/-- The cells of `v` under encoding `enc`, if `v` has that encoding. -/
noncomputable def encode : Encoding → val → Option (List val)
  | .word n, v => (wordLitZ? n v).map fun z => (leBytes n z).map fun b => LitV (LitByte b)
  | .cell k, v => if 1 ≤ k then some (v :: List.replicate (k - 1) (LitV LitTail)) else none

/-- The byte of a cell. -/
def byteOf? : val → Option w8
  | LitV (LitByte b) => some b
  | _ => none

/-- The value that the cells `cs` hold under encoding `enc`, if they hold one: for a word,
`n` bytes; for a `cell k` value, its first cell followed by `k - 1` tails. A `cell` load of
cells that do not hold such a value (bytes, or a tail in the first cell) gives a value
that is not one of the type (`LitByte`, `LitTail`), on which every operation of the type
is stuck: Go would give the bits of a corrupted value. -/
noncomputable def decode : Encoding → List val → Option val
  | .word n, cs =>
    if n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 then
      (cs.mapM byteOf?).bind fun bs => if bs.length = n then some (wordLit n (leInt bs)) else none
    else none
  | .cell k, [] => none
  | .cell k, v :: ts => if ts = List.replicate (k - 1) (LitV LitTail) then some v else none

/-- The cells `l, l +ₗ 1, …` of the heap `h` are `cs`. -/
def CellsAt (h : GMap Loc (NonAtomic val)) (l : Loc) (cs : List (NonAtomic val)) : Prop :=
  ∀ i (hi : i < cs.length), h !! (l +ₗ (i : Int)) = some (cs[i]'hi)

/-- The heap with the cells `l, l +ₗ 1, …` set to `cs`. -/
def setCells (l : Loc) (cs : List (NonAtomic val)) (σg : CfgState) : CfgState :=
  ({ σg.1 with heap := heapArray l cs ∪ σg.1.heap }, σg.2)

/-- The read-lock function for `NaMode`. -/
def naModeRl : NaMode → NaMode
  | Reading n => Reading (n + 1)
  | m => m

/-- The read-unlock function for `NaMode`. -/
def naModeUrl : NaMode → NaMode
  | Reading (n + 1) => Reading n
  | m => m

/-- The cells of a fresh allocation of `n` cells holding `v`: a zero-size allocation still
takes one cell (a `LitTail`, which nothing can load), so that its block is never
reused, as Go's zero-size variables do not share an address with a later variable. -/
def allocCells (n : Nat) (v : val) : List val :=
  if n = 0 then [LitV LitTail] else List.replicate n v

def IsWriting {A} (mna : Option (NonAtomic A)) : Prop := ∃ x, mna = some (Writing, x)

/-- `l` is the start of a fresh block in `σg`. -/
def IsFresh (σg : CfgState) (l : Loc) : Prop :=
  (∀ i : Int, l +ₗ i ≠ null ∧ σg.1.heap !! (l +ₗ i) = none) ∧ l.addrOffset = 0

/-- `l` is in a fresh block of `σg`, at an offset in `[0, 8)` that is a multiple of `a`.
By convention, offset `0` of every block is 8-aligned (8 is the largest alignment of a
gc/amd64 type), so the offset of a location is its address modulo 8: an object at an
address `A` aligned to `a` is the block based at `A - A % 8`, at offset `A % 8`. Go
promises a variable only its type's alignment, so the offset is any one with that
alignment. -/
def IsFreshAligned (σg : CfgState) (l : Loc) (a : Nat) : Prop :=
  (∀ i : Int, l +ₗ i ≠ null ∧ σg.1.heap !! (l +ₗ i) = none) ∧
    0 ≤ l.locOff ∧ l.locOff < 8 ∧ (a : Int) ∣ l.locOff

/-- `l` is aligned for an atomic operation on a value with encoding `enc`. -/
def Aligned (enc : Encoding) (l : Loc) : Prop := (enc.align : Int) ∣ l.locOff

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
/-- The base step relation:
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
  /-- `Fork e` spawns the thread `e ;; ThreadExit` and counts it. -/
  | ForkS e σg :
      BaseStep (Fork e) σg [] (Val #()) (σg.1, { σg.2 with threads := σg.2.threads + 1 })
        [Seq e ThreadExit]
  /-- The end of a forked thread: a no-op that uncounts the thread. -/
  | ThreadExitS σg :
      BaseStep ThreadExit σg [] (Val #()) (σg.1, { σg.2 with threads := σg.2.threads - 1 }) []
  | ArbitraryIntS (x : w64) σg : BaseStep ArbitraryInt σg [] (Val #x) σg []
  | AllocS v l σg :
      IsFresh σg l →
      BaseStep (Alloc (Val v)) σg [] (Val #l) (stateInitHeap l v σg.1, σg.2) []
  /-- A fresh block of `n` cells (`allocCells`) at an offset aligned to `a`. -/
  | AllocNS (n a : w64) v l σg :
      IsFreshAligned σg l (uint.nat a) →
      BaseStep (AllocN (Val (PairV (LitV (LitInt n)) (LitV (LitInt a)))) (Val v)) σg [] (Val #l)
        (setCells l ((allocCells (uint.nat n) v).map Free) σg) []
  /-- non-atomic load of an encoded value, part 1: a reader on each of its cells -/
  | StartReadNS enc l cs v σg :
      cs.length = enc.size → CellsAt σg.1.heap l cs →
      (∀ c ∈ cs, ∃ n, c.1 = Reading n) →
      decode enc (cs.map Prod.snd) = some v →
      BaseStep (StartReadN enc (Val #l)) σg [] (Val v)
        (setCells l (cs.map fun c => (naModeRl c.1, c.2)) σg) []
  /-- non-atomic load of an encoded value, part 2 -/
  | FinishReadNS enc l cs σg :
      cs.length = enc.size → CellsAt σg.1.heap l cs →
      (∀ c ∈ cs, ∃ n, c.1 = Reading (n + 1)) →
      BaseStep (FinishReadN enc (Val #l)) σg [] (Val #())
        (setCells l (cs.map fun c => (naModeUrl c.1, c.2)) σg) []
  /-- non-atomic store of an encoded value, part 1: each of its cells `Writing` -/
  | PrepareWriteNS enc l cs σg :
      cs.length = enc.size → CellsAt σg.1.heap l cs →
      (∀ c ∈ cs, c.1 = Reading 0) →
      BaseStep (PrepareWriteN enc (Val #l)) σg [] (Val #())
        (setCells l (cs.map fun c => (Writing, c.2)) σg) []
  /-- non-atomic store of an encoded value, part 2 -/
  | FinishStoreNS enc l v cs vs σg :
      cs.length = enc.size → CellsAt σg.1.heap l cs →
      (∀ c ∈ cs, c.1 = Writing) →
      encode enc v = some vs →
      BaseStep (FinishStoreN enc (Val #l) (Val v)) σg [] (Val #()) (setCells l (vs.map Free) σg) []
  /-- atomic load of an encoded value at an aligned location -/
  | LoadNS enc l cs v σg :
      Aligned enc l → cs.length = enc.size → CellsAt σg.1.heap l cs →
      (∀ c ∈ cs, ∃ n, c.1 = Reading n) →
      decode enc (cs.map Prod.snd) = some v →
      BaseStep (LoadN enc (Val #l)) σg [] (Val v) σg []
  | SwapNS enc l cs v0 v vs σg :
      Aligned enc l → cs.length = enc.size → CellsAt σg.1.heap l cs →
      (∀ c ∈ cs, c.1 = Reading 0) →
      decode enc (cs.map Prod.snd) = some v0 → encode enc v = some vs →
      BaseStep (SwapN enc (Val #l) (Val v)) σg [] (Val v0) (setCells l (vs.map Free) σg) []
  | AddNS n l cs v0 v v' vs σg :
      Aligned (.word n) l → cs.length = n → CellsAt σg.1.heap l cs →
      (∀ c ∈ cs, c.1 = Reading 0) →
      decode (.word n) (cs.map Prod.snd) = some v0 → atomicAddEval v0 v = some v' →
      encode (.word n) v' = some vs →
      BaseStep (AddN (.word n) (Val #l) (Val v)) σg [] (Val v') (setCells l (vs.map Free) σg) []
  | CmpXchgNFailS enc l cs vl v1 v2 σg :
      Aligned enc l → cs.length = enc.size → CellsAt σg.1.heap l cs →
      (∀ c ∈ cs, ∃ n, c.1 = Reading n) →
      decode enc (cs.map Prod.snd) = some vl → vl ≠ v1 →
      BaseStep (CmpXchgN enc (Val #l) (Val (PairV v1 v2))) σg [] (Val (PairV vl #false)) σg []
  | CmpXchgNSucS enc l cs vl v1 v2 vs σg :
      Aligned enc l → cs.length = enc.size → CellsAt σg.1.heap l cs →
      (∀ c ∈ cs, c.1 = Reading 0) →
      decode enc (cs.map Prod.snd) = some vl → vl = v1 → encode enc v2 = some vs →
      BaseStep (CmpXchgN enc (Val #l) (Val (PairV v1 v2))) σg [] (Val (PairV vl #true))
        (setCells l (vs.map Free) σg) []
  /-- `CheckCell l` (for `unsafe.Add`): `l` is a cell of the heap. -/
  | CheckCellS l σg :
      (σg.1.heap !! l).isSome →
      BaseStep (CheckCell (Val #l)) σg [] (Val #()) σg []
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
