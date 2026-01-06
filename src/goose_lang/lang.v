From Coq.Program Require Import Equality.
From RecordUpdate Require Import RecordSet.
From stdpp Require Export binders.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From Perennial.program_logic Require Export language ectx_language ectxi_language.
From Perennial.Helpers Require Import CountableTactics.
From Perennial.Helpers Require Import Transitions.
From Perennial.Helpers Require Import ByteString.
From Perennial.program_logic Require Export crash_lang.
From Perennial.goose_lang Require Export locations.
From Perennial Require Export Helpers.Integers.

From New.golang.defn Require Export prelang.

Set Default Proof Using "Type".

Open Scope Z_scope.

(** GooseLang, an adaptation of HeapLang with extensions to model Go, including
support for a customizable "FFI" (foreign-function interface) for new primitive
operations and crash semantics for foreign operations. See goose_lang/ffi/disk.v
for our main FFI example.

- Unlike HeapLang, we keep a left-to-right evaluation order to match Go and
  because curried functions no longer arise. (BUG(tej): built-in functions and
  operators are left-to-right, but function calls are still left-to-right. This
  should be fixed.)

*)

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module goose_lang.

(** Expressions and vals. *)
Definition proph_id := positive.

Class ffi_syntax :=
  mkExtOp {
      ffi_opcode: Set;
      #[global] ffi_opcode_eq_dec :: EqDecision ffi_opcode;
      #[global] ffi_opcode_countable :: Countable ffi_opcode;
      ffi_val: Type;
      #[global] ffi_val_eq_dec :: EqDecision ffi_val;
      #[global] ffi_val_countable :: Countable ffi_val;
    }.

Class ffi_model :=
  mkFfiModel {
      ffi_state : Type;
      ffi_global_state : Type;
      #[global] ffi_state_inhabited :: Inhabited ffi_state;
      #[global] ffi_global_state_inhabited :: Inhabited ffi_global_state;
    }.

Module slice.
Record t := mk { ptr: loc; len: w64; cap: w64; }.
Definition nil : slice.t := mk null (W64 0) (W64 0).
End slice.

Global Instance slice_eq_dec : EqDecision slice.t.
Proof. solve_decision. Qed.

Section external.

(* these are codes for external operations (which all take a single val as an
   argument and evaluate to a value) and data for external values *)
Context {ext : ffi_syntax}.

(** [base_lit] is a helper type of primitive values (i.e. this excludes composite
    values like structs and arrays); this is injected into [val] using [LitV] below.

    TODO: There's a notion of "poison" inherited from HeapLang. HeapLang uses it
    for stating an erasure theorem for prophecies, but GooseLang does not
    currently have such a theorem. *)
Inductive base_lit : Type :=
  | LitInt (n : u64) | LitInt32 (n : u32) | LitInt16 (n : w16) | LitBool (b : bool) | LitByte (n : u8)
  | LitString (s : byte_string) | LitUnit | LitPoison
  | LitLoc (l : loc) | LitProphecy (p: proph_id)
  | LitSlice (s : slice.t).

Inductive un_op : Set :=
  | NegOp | MinusUnOp
  | UToW64Op | UToW32Op | UToW16Op | UToW8Op
  | SToW64Op | SToW32Op | SToW16Op | SToW8Op
  | ToStringOp | StringLenOp | IsNoStringOverflowOp
.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | QuotSignedOp | RemOp | RemSignedOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp (k:Z) (* Pointer offset *)
  | StringGetOp
.

Inductive prim_op0 : Type :=
  (* a stuck expression, to represent undefined behavior *)
| PanicOp (s: string)
  (* non-deterministically pick an integer *)
| ArbitraryIntOp
.

Inductive prim_op1 : Set :=
  | PrepareWriteOp (* loc *)
  (* non-atomic loads (which conflict with stores) *)
  | StartReadOp (* loc *)
  | FinishReadOp (* loc *)
  (* atomic loads (which still conflict with non-atomic stores) *)
  | LoadOp
  | InputOp
  | OutputOp
.

Inductive prim_op2 : Set :=
 | AllocNOp (* array length (positive number), initial value *)
 | FinishStoreOp (* pointer, value *)
 | AtomicSwapOp (* pointer, value; returns old value *)
 | AtomicOpOp (op : bin_op) (* pointer, value *) (* atomic binary operation *)
 | GlobalPutOp (* string, val *)
.

Inductive arity : Set := args0 | args1 | args2.
Definition prim_op (ar:arity) : Type :=
  match ar with
  | args0 => prim_op0
  | args1 => prim_op1
  | args2 => prim_op2
  end.

Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. refine (
           fix go e1 e2 :=
             match e1, e2 with
             | LitInt x, LitInt x' => cast_if (decide (x = x'))
             | LitInt32 x, LitInt32 x' => cast_if (decide (x = x'))
             | LitInt16 x, LitInt16 x' => cast_if (decide (x = x'))
             | LitBool x, LitBool x' => cast_if (decide (x = x'))
             | LitByte x, LitByte x' => cast_if (decide (x = x'))
             | LitString x, LitString x' => cast_if (decide (x = x'))
             | LitUnit, LitUnit => left _
             | LitPoison, LitPoison => left _
             | LitLoc l, LitLoc l' => cast_if (decide (l = l'))
             | LitProphecy i, LitProphecy i' => cast_if (decide (i = i'))
             | LitSlice m, LitSlice m' => cast_if (decide (m = m'))
             (* | LitStruct m, LitStruct m' => cast_if (decide (m = m')) *)
             | _ , _ => right _
             end); [ try by intuition congruence .. | ].
       intros H. inversion H. done.
Defined.

Inductive go_operator : Type :=
(* binary ops *)
| GoEquals
| GoLt
| GoLe
| GoGt
| GoGe
| GoPlus
| GoSub
| GoMul
| GoDiv
| GoRemainder
| GoAnd
| GoOr
| GoXor
| GoBitClear
| GoShiftl
| GoShiftr.

Inductive go_instruction : Type :=
| AngelicExit

| GoOp (o : go_operator) (t : go.type)

| GoLoad (t : go.type)
| GoStore (t : go.type)
| GoAlloc (t : go.type)
| GoPrealloc
| GoZeroVal (t : go.type)

| FuncResolve (f : go_string) (type_args : list go.type)
| MethodResolve (t : go.type) (m : go_string)

| InterfaceMake (t : go.type)
| InterfaceGet (m : go_string)
| TypeAssert (t : go.type)
| TypeAssert2 (t : go.type)

| PackageInitCheck (pkg_name : go_string)
| PackageInitStart (pkg_name : go_string)
| PackageInitFinish (pkg_name : go_string)

| GlobalVarAddr (var_name : go_string)

| StructFieldRef (t : go.type) (f : go_string)
| StructFieldGet (t : go.type) (f : go_string)
| StructFieldSet (t : go.type) (f : go_string)

(* can do slice, array, string, map, etc. for these ops; the internal ones
   should not be directly called by GooseLang. *)
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

(* these are internal steps; the Go map lookup has to be implemented as multiple
   instructions because it is not atomic. *)
| InternalMapLookup
| InternalMapInsert
| InternalMapDelete
| InternalMapLength
| InternalMapForRange (key_type elem_type : go.type)
| InternalMapMake

| CompositeLiteral (t : go.type)
| SelectStmt.

Inductive expr :=
(* Values *)
| Val (v : val)
(* Base lambda calculus *)
| Var (x : string)
| Rec (f x : binder) (e : expr)
| App (e1 e2 : expr)
(* Base types and their operations *)
| UnOp (op : un_op) (e : expr)
| BinOp (op : bin_op) (e1 e2 : expr)
| If (e0 e1 e2 : expr)
(* Products *)
| Pair (e1 e2 : expr)
| Fst (e : expr)
| Snd (e : expr)
(* Sums *)
| InjL (e : expr)
| InjR (e : expr)
| Case (e0 : expr) (e1 : expr) (e2 : expr)
(* Concurrency *)
| Fork (e : expr)
| Atomically (e: expr) (e : expr)
(* Heap-based primitives *)
| Primitive0 (op: prim_op args0)
| Primitive1 (op: prim_op args1) (e : expr)
| Primitive2 (op: prim_op args2) (e1 e2 : expr)
(* | Primitive3 (op: prim_op args3) (e0 e1 e2 : expr) *)
| CmpXchg (e0 : expr) (e1 : expr) (e2 : expr) (* Compare-exchange *)
(* External FFI operation *)
| ExternalOp (op: ffi_opcode) (e: expr)
(* Prophecy *)
| NewProph
| ResolveProph (e1 : expr) (e2 : expr) (* proph, val *)

| LiteralValue (l : list keyed_element)
| SelectStmtClauses (default_handler : option expr) (l : list comm_clause)
with val :=
| LitV (l : base_lit)
| RecV (f x : binder) (e : expr)
| PairV (v1 v2 : val)
| InjLV (v : val)
| InjRV (v : val)
(** This represents "pointers to opaque types" that FFI operations may return
  and that regular Goose code may not do anything with except for passing it to
  other FFI operations. FFI implementations must ensure that these values are
  indeed truly independent from anything modeled in GooseLang (i.e., no
  aliasing/sharing with memory that GooseLang can "see").
  On the Go side, these should be pointers to some private type. *)
| ExtV (ev : ffi_val)
(* Go stuff *)
| GoInstruction (o : go_instruction)
| ArrayV (vs : list val)
| InterfaceV (t : option (go.type * val))

| LiteralValueV (l : list keyed_element)
| SelectStmtClausesV (default_handler : option expr) (l : list comm_clause)

(* https://go.dev/ref/spec#Composite_literals *)
with keyed_element :=
| KeyedElement (k : option key) (v : element)
with key :=
| KeyField (f : go_string)
| KeyInteger (s : Z)
| KeyExpression (e : expr)
| KeyLiteralValue (l : list keyed_element)
with element :=
| ElementExpression (e : expr)
| ElementLiteralValue (l : list keyed_element)

with comm_clause :=
| CommClause (c : comm_case) (body : expr)
(* Variable bindings are "desugared" by goose into the body, so the send and
   receives don't need to consider bindings or assignments. *)
with comm_case := (* skips default because it's inlined into SelectStmtClauses *)
| SendCase (elem_type : go.type) (ch : expr)
| RecvCase (elem_type : go.type) (ch : expr)
.

End external.
End goose_lang.

(* Prefer goose_lang names over ectx_language names. *)
Export goose_lang.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation Panic s := (Primitive0 (PanicOp s)).
Notation ArbitraryInt := (Primitive0 ArbitraryIntOp).
Notation AllocN := (Primitive2 AllocNOp).
Notation PrepareWrite := (Primitive1 PrepareWriteOp).
Notation FinishStore := (Primitive2 FinishStoreOp).
Notation AtomicSwap := (Primitive2 AtomicSwapOp).
Notation AtomicOp o := (Primitive2 (AtomicOpOp o)).
Notation StartRead := (Primitive1 StartReadOp).
Notation FinishRead := (Primitive1 FinishReadOp).
Notation Load := (Primitive1 LoadOp).
Notation Input := (Primitive1 InputOp).
Notation Output := (Primitive1 OutputOp).

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Global Open Scope Z. (* Make sure everyone gets this scope. *)

Coercion LitBool : bool >-> base_lit.
Coercion LitLoc : loc >-> base_lit.
(* TODO: this should be added *)
(* Coercion LitString : string >-> base_lit. *)
Coercion LitInt : u64 >-> base_lit.
Coercion LitInt32 : u32 >-> base_lit.
Coercion LitInt16 : w16 >-> base_lit.
Coercion LitByte : u8 >-> base_lit.
Coercion LitProphecy : proph_id >-> base_lit.
Notation "'str' s" := (LitString (s : byte_string)) (at level 30, format "'str'  s") : val_scope.

Definition b2val {ext: ffi_syntax}: u8 -> val := λ (b:u8), LitV (LitByte b).
Global Instance b2val_inj {ext: ffi_syntax} : Inj eq eq b2val.
Proof.
  intros b1 b2 Heq.
  inversion Heq; auto.
Qed.

Coercion App : expr >-> Funclass.

Coercion Val : val >-> expr.
(** As of https://github.com/coq/coq/pull/15789 Coq does not require the uniform
inheritance criteria, but silencing the warning is still required. *)
#[warning="-uniform-inheritance"]
Coercion Var : string >-> expr.

(** Define some derived forms. *)
Notation Lam x e := (Rec BAnon x e) (only parsing).
Notation Let x e1 e2 := (App (Lam x e2) e1) (only parsing).
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation LamV x e := (RecV BAnon x e) (only parsing).
Notation Match e0 x1 e1 x2 e2 := (Case e0 (Lam x1 e1) (Lam x2 e2)) (only parsing).
Notation Alloc e := (AllocN (Val $ LitV $ LitInt (W64 1)) e).
(** Compare-and-set (CAS) returns just a boolean indicating success or failure. *)
Notation CAS l e1 e2 := (Snd (CmpXchg l e1 e2)) (only parsing).

(* Skip should be atomic, we sometimes open invariants around
   it. Hence, we need to explicitly use LamV instead of e.g., Seq. *)
Notation Skip := (App (Val $ LamV BAnon (Val $ LitV LitUnit)) (Val $ LitV LitUnit)).
Definition Linearize {ext:ffi_syntax}: expr := Skip.

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# l" := (LitV l%Z%V%stdpp) (at level 8, format "# l").

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1 e2) .. en) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (PairV .. (PairV e1 e2) .. en) : val_scope.

(*
Using the '[hv' ']' printing box, we make sure that when the notation for match
does not fit on a single line, line breaks will be inserted for *each* breaking
point '/'. Note that after each breaking point /, one can put n spaces (for
example '/  '). That way, when the breaking point is turned into a line break,
indentation of n spaces will appear after the line break. As such, when the
match does not fit on one line, it will print it like:

  match: e0 with
    InjL x1 => e1
  | InjR x2 => e2
  end

Moreover, if the branches do not fit on a single line, it will be printed as:

  match: e0 with
    InjL x1 =>
    lots of stuff bla bla bla bla bla bla bla bla
  | InjR x2 =>
    even more stuff bla bla bla bla bla bla bla bla
  end
*)
Notation "'match:' e0 'with' 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" :=
  (Match e0 x1%binder e1 x2%binder e2)
  (e0, x1, e1, x2, e2 at level 200,
   format "'[hv' 'match:'  e0  'with'  '/  ' '[' 'InjL'  x1  =>  '/  ' e1 ']'  '/' '[' |  'InjR'  x2  =>  '/  ' e2 ']'  '/' 'end' ']'") : expr_scope.
Notation "'match:' e0 'with' 'InjR' x1 => e1 | 'InjL' x2 => e2 'end'" :=
  (Match e0 x2%binder e2 x1%binder e1)
  (e0, x1, e1, x2, e2 at level 200, only parsing) : expr_scope.

Notation "()" := LitUnit : val_scope.
Notation "! e" := (Load e%E) (at level 9, right associativity) : expr_scope.
Notation "'ref' e" := (Alloc e%E) (at level 10) : expr_scope.
Notation "- e" := (UnOp MinusUnOp e%E) : expr_scope.
Notation "'u_to_w64' e" := (UnOp UToW64Op e%E) (at level 10) : expr_scope.
Notation "'u_to_w32' e" := (UnOp UToW32Op e%E) (at level 10) : expr_scope.
Notation "'u_to_w16' e" := (UnOp UToW16Op e%E) (at level 10) : expr_scope.
Notation "'u_to_w8' e" := (UnOp UToW8Op e%E) (at level 10) : expr_scope.
Notation "'s_to_w64' e" := (UnOp SToW64Op e%E) (at level 10) : expr_scope.
Notation "'s_to_w32' e" := (UnOp SToW32Op e%E) (at level 10) : expr_scope.
Notation "'s_to_w16' e" := (UnOp SToW16Op e%E) (at level 10) : expr_scope.
Notation "'s_to_w8' e" := (UnOp SToW8Op e%E) (at level 10) : expr_scope.
Notation "'to_u64' e" := (UnOp UToW64Op e%E) (at level 10, only parsing) : expr_scope. (* backwards compatibility *)
Notation "'to_u32' e" := (UnOp UToW32Op e%E) (at level 10, only parsing) : expr_scope. (* backwards compatibility *)
Notation "'to_u16' e" := (UnOp UToW16Op e%E) (at level 10, only parsing) : expr_scope. (* backwards compatibility *)
Notation "'to_u8' e" := (UnOp UToW8Op e%E) (at level 10, only parsing) : expr_scope. (* backwards compatibility *)
Notation "'to_string' e" := (UnOp ToStringOp e%E) (at level 10) : expr_scope.
Notation "'StringLength' e" := (UnOp StringLenOp e%E) (at level 10) : expr_scope.
Notation "'IsNoStringOverflow' e" := (UnOp IsNoStringOverflowOp e%E) (at level 10) : expr_scope.

Notation "'StringGet'" := (BinOp StringGetOp) (at level 10) : expr_scope.
Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E) : expr_scope.
Notation "e1 +ₗ e2" := (BinOp (OffsetOp 1) e1%E e2%E) : expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E) : expr_scope.
Notation "e1 * e2" := (BinOp MultOp e1%E e2%E) : expr_scope.
Notation "e1 `or` e2" := (BinOp OrOp e1%E e2%E) (at level 40) : expr_scope.
Notation "e1 `and` e2" := (BinOp AndOp e1%E e2%E) (at level 40) : expr_scope.
Notation "e1 `xor` e2" := (BinOp XorOp e1%E e2%E) (at level 40) : expr_scope.
Notation "e1 `quot` e2" := (BinOp QuotOp e1%E e2%E) : expr_scope.
Notation "e1 `quots` e2" := (BinOp QuotSignedOp e1%E e2%E) (at level 35) : expr_scope.
Notation "e1 `rem` e2" := (BinOp RemOp e1%E e2%E) : expr_scope.
Notation "e1 `rems` e2" := (BinOp RemSignedOp e1%E e2%E) (at level 35) : expr_scope.
Notation "e1 ≪ e2" := (BinOp ShiftLOp e1%E e2%E) : expr_scope.
Notation "e1 ≫ e2" := (BinOp ShiftROp e1%E e2%E) : expr_scope.
(* models Go's &^ operator *)
Notation "e1 `and_not` e2" := (BinOp AndOp e1%E (UnOp NegOp e2%E)) (at level 40, only parsing) : expr_scope.

Notation "~ e" := (UnOp NegOp e%E) (at level 75, right associativity) : expr_scope.
Definition Store {ext:ffi_syntax} : val :=
  LamV "l" (Lam "v" (Seq
                     (PrepareWrite (Var "l"))
                     (FinishStore (Var "l") (Var "v")))).
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Store e1%E e2%E) (at level 80) : expr_scope.

Definition Read {ext:ffi_syntax} : val :=
  LamV "l" ((Let "v" (StartRead (Var "l"))
                     (Seq (FinishRead (Var "l"))
                          (Var "v")))).

(* The breaking point '/  ' makes sure that the body of the rec is indented
by two spaces in case the whole rec does not fit on a single line. *)
Notation "'rec:' f x := e" := (Rec f%binder x%binder e%E)
  (at level 200, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : expr_scope.
Notation "'rec:' f x := e" := (RecV f%binder x%binder e%E)
  (at level 200, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : val_scope.
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (at level 200, e1, e2, e3 at level 200) : expr_scope.

(** Derived notions, in order of declaration. The notations for let and seq
are stated explicitly instead of relying on the Notations Let and Seq as
defined above. This is needed because App is now a coercion, and these
notations are otherwise not pretty printed back accordingly. *)
Notation "'rec:' f x y .. z := e" := (Rec f%binder x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : expr_scope.
Notation "'rec:' f x y .. z := e" := (RecV f%binder x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : val_scope.

(* The breaking point '/  ' makes sure that the body of the λ: is indented
by two spaces in case the whole λ: does not fit on a single line. *)
Notation "λ: x , e" := (Lam x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : expr_scope.
Notation "λ: x y .. z , e" := (Lam x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : expr_scope.

Notation "λ: x , e" := (LamV x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : val_scope.
Notation "λ: x y .. z , e" := (LamV x%binder (Lam y%binder .. (Lam z%binder e%E) .. ))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : val_scope.

Notation "'let:' x := e1 'in' e2" := (Lam x%binder e2%E e1%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
(* TODO: this notation is not hygienic because it introduces __p into e1's scope

we could do slightly better by using a variable that can't appear in Go (eg, one
with spaces), but we would probably still handle nested destructuring
incorrectly *)
Notation "'let:' ( a1 , a2 ) := e1 'in' e2" :=
  (Lam "__p"
    (Lam a1%binder (Lam a2%binder e2%E (Snd "__p")) (Fst "__p"))
    e1%E)
  (at level 200, a1, a2 at level 1, e1, e2 at level 200,
   format "'[' 'let:' ( a1 , a2 ) := '[' e1 ']' 'in' '/' e2 ']'") : expr_scope.
Notation "'let:' ( ( a1 , a2 ) , a3 ) := e1 'in' e2" :=
  (Lam "__p"
    (Lam a1%binder (Lam a2%binder (Lam a3%binder e2%E
      (Snd "__p")) (Snd (Fst "__p"))) (Fst (Fst "__p")))
    e1%E)
  (at level 200, a1, a2, a3 at level 1, e1, e2 at level 200,
   format "'[' 'let:' ( ( a1 , a2 ) , a3 ) := '[' e1 ']' 'in' '/' e2 ']'") : expr_scope.
Notation "'let:' ( ( ( a1 , a2 ) , a3 ) , a4 ) := e1 'in' e2" :=
  (Lam "__p"
    (Lam a1%binder (Lam a2%binder (Lam a3%binder (Lam a4%binder e2%E
      (Snd "__p")) (Snd (Fst "__p"))) (Snd (Fst (Fst "__p"))))
      (Fst (Fst (Fst "__p"))))
    e1%E)
  (at level 200, a1, a2, a3, a4 at level 1, e1, e2 at level 200,
   format "'[' 'let:' ( ( ( a1 , a2 ) , a3 ) , a4 ) := '[' e1 ']' 'in' '/' e2 ']'") : expr_scope.
Notation "'let:' ( ( ( ( a1 , a2 ) , a3 ) , a4 ) , a5 ) := e1 'in' e2" :=
  (Lam "__p"
    (Lam a1%binder (Lam a2%binder (Lam a3%binder (Lam a4%binder (Lam a5%binder e2%E
      (Snd "__p")) (Snd (Fst "__p"))) (Snd (Fst (Fst "__p"))))
      (Snd (Fst (Fst (Fst "__p"))))) (Fst (Fst (Fst (Fst "__p")))))
    e1%E)
  (at level 200, a1, a2, a3, a4, a5 at level 1, e1, e2 at level 200,
   format "'[' 'let:' ( ( ( ( a1 , a2 ) , a3 ) , a4 ) , a5 ) := '[' e1 ']' 'in' '/' e2 ']'") : expr_scope.
Notation "'let:' ( ( ( ( ( a1 , a2 ) , a3 ) , a4 ) , a5 ) , a6 ) := e1 'in' e2" :=
  (Lam "__p"
    (Lam a1%binder (Lam a2%binder (Lam a3%binder (Lam a4%binder
      (Lam a5%binder (Lam a6%binder e2%E
      (Snd "__p")) (Snd (Fst "__p"))) (Snd (Fst (Fst "__p"))))
      (Snd (Fst (Fst (Fst "__p"))))) (Snd (Fst (Fst (Fst (Fst "__p"))))))
      (Fst (Fst (Fst (Fst (Fst "__p"))))))
    e1%E)
  (at level 200, a1, a2, a3, a4, a5, a6 at level 1, e1, e2 at level 200,
   format "'[' 'let:' ( ( ( ( ( a1 , a2 ) , a3 ) , a4 ) , a5 ) , a6 ) := '[' e1 ']' 'in' '/' e2 ']'") : expr_scope.
Notation "e1 ;; e2" := (Lam BAnon e2%E e1%E)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']' ;;  ']' '/' e2 ']'") : expr_scope.

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%E e2%E (LitV (LitBool false))) (only parsing) : expr_scope.
Notation "e1 || e2" :=
  (If e1%E (LitV (LitBool true)) e2%E) (only parsing) : expr_scope.

(** Notations for option *)
Notation NONE := (InjL (LitV LitUnit)) (only parsing).
Notation NONEV := (InjLV (LitV LitUnit)) (only parsing).
Notation SOME x := (InjR x) (only parsing).
Notation SOMEV x := (InjRV x) (only parsing).

Notation "'match:' e0 'with' 'NONE' => e1 | 'SOME' x => e2 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.
Notation "'match:' e0 'with' 'SOME' x => e2 | 'NONE' => e1 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.

(*
Notation ResolveProph e1 e2 := (Resolve Skip e1 e2) (only parsing).
Notation "'resolve_proph:' p 'to:' v" := (ResolveProph p v) (at level 100) : expr_scope.
*)

Module func.
Section defn.
Context `{ffi_syntax}.
Record t := mk {
      f : binder;
      x : binder;
      e : expr;
    }.
Definition nil := mk <> <> (Val $ LitV LitPoison).
End defn.
End func.

(** [GoGlobalContext] contains the [into_val] function. This allows for the Go
    semantics to state constraints on [into_val] (e.g. injectivity for certain
    types). *)
Class GoGlobalContext {ext : ffi_syntax} : Type :=
  {
    into_val : ∀ {V : Type} (v : V), val;
  }.

(** [GoLocalContext] contains several low-level Go functions for typed memory access,
    map updates, etc. *)
Class GoLocalContext {ext : ffi_syntax} : Type :=
  {
    is_go_step_pure : ∀ (op : go_instruction) (arg : val) (e' : expr), Prop;
  }.

Module chan.
Definition t := loc.
Definition nil : chan.t := null.
End chan.

Module interface.
Section goose_lang.
Context `{ffi_syntax}.

Inductive t :=
| mk (ty : go.type) (v : val) : t
| nil : t.

End goose_lang.
End interface.

Module array.
Section goose_lang.
Inductive t (ty : go.type) (V : Type) (n : Z) :=
| mk (arr : list V) : t ty V n.
Definition arr {ty V n} (x : t ty V n) := let (arr) := x in arr.
End goose_lang.
End array.
Arguments array.mk (ty) {_} (n arr).
Arguments array.arr {_ _ _} (_).

Section external.
(* these are codes for external operations (which all take a single val as an
   argument and evaluate to a value) and data for external values *)
Context {ext : ffi_syntax}.

(* XXX: to avoid splitting things into heap cells, can wrap it in e.g. an InjLV.
   This is how lists can avoid getting split into different heap cells when [ref]'d. *)
Fixpoint flatten_struct (v: val) : list val :=
  match v with
  | PairV v1 v2 => flatten_struct v1 ++ flatten_struct v2
  | LitV LitUnit => []
  | _ => [v]
  end.

Context {ffi : ffi_model}.

Inductive naMode : Set :=
  | Writing
  | Reading (n:nat).

Notation nonAtomic T := (naMode * T)%type.

(* TODO: Free should really be called something else - quiescent? just value?  *)
Definition Free {T} (v:T): nonAtomic T := (Reading 0, v).

Inductive event :=
  | In_ev (sel v:base_lit)
  | Out_ev (v:base_lit)
  | Crash_ev
.

(* a trace is a list of events, stored in reverse order *)
Definition Trace := list event.

Definition add_event (ev: event) (ts: Trace) : Trace := cons ev ts.

Definition add_crash (ts: Trace) : Trace :=
  match ts with
  | Crash_ev::ts' => ts
  | _ => add_event Crash_ev ts
  end.

Definition Oracle := Trace -> forall (sel:u64), u64.

Instance Oracle_Inhabited: Inhabited Oracle := populate (fun _ _ => word.of_Z 0).

Class ZeroVal V :=
  {
    zero_val_def : V
  }.
Global Hint Mode ZeroVal ! : typeclass_instances.
Global Arguments zero_val_def (V) {_}.

Section zero_val_instances.
Context `{ffi_syntax}.

Global Instance zero_val_loc : ZeroVal loc :=
  {| zero_val_def := null |}.

Global Instance zero_val_w64 : ZeroVal w64 :=
  {| zero_val_def := W64 0 |}.

Global Instance zero_val_w32 : ZeroVal w32 :=
  {| zero_val_def := W32 0 |}.

Global Instance zero_val_w16 : ZeroVal w16 :=
  {| zero_val_def := W16 0 |}.

Global Instance zero_val_w8 : ZeroVal w8 :=
  {| zero_val_def := W8 0 |}.

Global Instance zero_val_unit : ZeroVal () :=
  {| zero_val_def := () |}.

Global Instance zero_val_bool : ZeroVal bool :=
  {| zero_val_def := false |}.

Global Instance zero_val_go_string : ZeroVal go_string :=
  {| zero_val_def := ""%go |}.

Global Instance zero_val_func : ZeroVal func.t :=
  {| zero_val_def := func.nil |}.

Global Instance zero_val_array t `{!ZeroVal V} n : ZeroVal (array.t t V n) :=
  {| zero_val_def := array.mk t n $ replicate (Z.to_nat n) (zero_val_def V) |}.

Global Instance zero_val_slice : ZeroVal slice.t :=
  {| zero_val_def := slice.nil |}.

Global Instance zero_val_interface : ZeroVal interface.t :=
  {| zero_val_def := interface.nil |}.

End zero_val_instances.
Notation "()" := tt : val_scope.
#[global] Opaque to_val.

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%E e2%E #false) (only parsing) : expr_scope.
Notation "e1 || e2" :=
  (If e1%E #true e2%E) (only parsing) : expr_scope.

Local Notation "# x" := (into_val x%go).
Local Notation "#" := into_val (at level 0).

Definition is_go_step `{!GoGlobalContext} `{!GoLocalContext}
  (op : go_instruction) (arg : val) (e' : expr) (s s' : gmap go_string bool) : Prop :=
  match op with
  | PackageInitCheck p => arg = #() ∧ e' = #(default false (s !! p)) ∧ s' = s
  | PackageInitStart p => arg = #() ∧ e' = #() ∧ s' = (<[ p := false ]> s)
  | PackageInitFinish p => arg = #() ∧ e' = #() ∧ s' = (<[ p := true ]>s)
  | _ => is_go_step_pure op arg e' ∧ s = s'
  end.

Record GoState : Type :=
  {
    go_lctx : GoLocalContext;
    package_state : gmap go_string bool;
  }.

Record state : Type := {
  heap : gmap loc (nonAtomic val);
  go_state : GoState;
  world : ffi_state;
  trace : Trace;
  oracle : Oracle;
}.
Record global_state : Type := {
  global_world: ffi_global_state;
  used_proph_id: gset proph_id;
  go_gctx : GoGlobalContext;
}.

Global Instance eta_go_state : Settable _ := settable! Build_GoState <go_lctx; package_state>.
Global Instance eta_state : Settable _ := settable! Build_state <heap; go_state; world; trace; oracle>.
Global Instance eta_global_state : Settable _ := settable! Build_global_state <global_world; used_proph_id; go_gctx>.

(* Note that ffi_step takes a val, which is itself parameterized by the
external type, so the semantics of external operations depend on a definition of
the syntax of GooseLang. Similarly, it "returns" an expression, the result of
evaluating the external operation.

It also takes an entire state record, which is also parameterized by ffi_state,
since external operations can read and modify the heap.

(this makes sense because the FFI semantics has to pull out arguments from a
GooseLangh val, and it must produce a return value in expr)

We produce a val to make external operations atomic.

[global_state] cannot be affected by a crash.
*)
Class ffi_semantics :=
  {
    ffi_step : ffi_opcode -> val -> transition (state*global_state) expr;
    ffi_crash_step : ffi_state -> ffi_state -> Prop;
  }.
Context {ffi_semantics: ffi_semantics}.

Inductive goose_crash : state -> state -> Prop :=
  | GooseCrash σ w w' go_state' :
     w = σ.(world) ->
     ffi_crash_step w w' ->
     goose_crash σ (set go_state (fun _ => go_state') (set trace add_crash (set world (fun _ => w') (set heap (fun _ => ∅) σ))))
.


(** An observation associates a prophecy variable (identifier) to the
value it is resolved to. *)
Definition observation : Type := proph_id * val.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance arity_eq_dec : EqDecision arity.
Proof. solve_decision. Defined.
Global Instance prim_op0_eq_dec : EqDecision prim_op0.
Proof. solve_decision. Defined.
Global Instance prim_op1_eq_dec : EqDecision prim_op1.
Proof. solve_decision. Defined.
Global Instance prim_op2_eq_dec : EqDecision prim_op2.
Proof. solve_decision. Defined.
Global Instance prim_op_eq_dec ar : EqDecision (prim_op ar).
Proof. destruct ar; simpl; apply _. Defined.
Global Instance go_operator_eq_dec : EqDecision go_operator.
Proof. solve_decision. Qed.
Global Instance go_instruction_eq_dec : EqDecision go_instruction.
Proof. solve_decision. Qed.

Global Instance go_type_inhabited : Inhabited go.type := populate (go.Named "any"%go []).

Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).
Global Instance key_inhabited : Inhabited key := populate (KeyField []).
Global Instance element_inhabited : Inhabited element := populate (ElementExpression inhabitant).
Global Instance keyed_element_inhabited : Inhabited keyed_element :=
  populate (KeyedElement None inhabitant).
Global Instance comm_case_inhabited : Inhabited comm_case := populate (SendCase inhabitant inhabitant).
Global Instance comm_clause_inhabited : Inhabited comm_clause := populate (CommClause inhabitant inhabitant).

Global Instance func_t_inhabited : Inhabited func.t :=
  populate (func.mk inhabitant inhabitant inhabitant).
Global Instance GoGlobalContext_inhabited : Inhabited GoGlobalContext :=
  populate {| into_val := inhabitant |}.
Global Instance GoLocalContext_inhabited : Inhabited GoLocalContext :=
  populate {| is_go_step_pure := inhabitant; |}.
Global Instance GoState_inhabited : Inhabited GoState :=
  populate {| go_lctx := inhabitant; package_state := inhabitant |}.

Global Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant; go_state := inhabitant; world := inhabitant; trace := inhabitant; oracle := inhabitant; |}.
Global Instance global_state_inhabited : Inhabited global_state :=
  populate {| used_proph_id := inhabitant; global_world := inhabitant; go_gctx := inhabitant |}.

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

Canonical Structure u64O := leibnizO u64.
Canonical Structure u32O := leibnizO u32.
Canonical Structure u8O := leibnizO u8.

(** Evaluation contexts *)
Inductive ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (e2 : expr)
  | BinOpRCtx (op : bin_op) (v1 : val)
  | IfCtx (e1 e2 : expr)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : expr) (e2 : expr)
  | Primitive1Ctx  (op: prim_op args1)
  | Primitive2LCtx (op: prim_op args2) (e2 : expr)
  | Primitive2RCtx (op: prim_op args2) (v1 : val)
  (* | Primitive3LCtx (op: prim_op args3) (e1 : expr) (e2 : expr)
  | Primitive3MCtx (op: prim_op args3) (v0 : val) (e2 : expr)
  | Primitive3RCtx (op: prim_op args3) (v0 : val) (v1 : val) *)
  | ExternalOpCtx (op : ffi_opcode)
  | CmpXchgLCtx (e1 : expr) (e2 : expr)
  | CmpXchgMCtx (v1 : val) (e2 : expr)
  | CmpXchgRCtx (v1 : val) (v2 : val)
  | ResolveProphLCtx (v2 : val)
  | ResolveProphRCtx (e1 : expr)
  | AtomicallyCtx (e0 : expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (of_val v2)
  | AppRCtx e1 => App e1 e
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op v1 => BinOp op (Val v1) e
  | IfCtx e1 e2 => If e e1 e2
  | PairLCtx e2 => Pair e e2
  | PairRCtx v1 => Pair (Val v1) e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | Primitive1Ctx op => Primitive1 op e
  | Primitive2LCtx op e2 => Primitive2 op e e2
  | Primitive2RCtx op v1 => Primitive2 op (Val v1) e
  | ExternalOpCtx op => ExternalOp op e
  | CmpXchgLCtx e1 e2 => CmpXchg e e1 e2
  | CmpXchgMCtx v0 e2 => CmpXchg (Val v0) e e2
  | CmpXchgRCtx v0 v1 => CmpXchg (Val v0) (Val v1) e
  | ResolveProphLCtx v2 => ResolveProph e (Val v2)
  | ResolveProphRCtx e1 => ResolveProph e1 e
  | AtomicallyCtx e1 => Atomically e e1
  end.

(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | UnOp op e => UnOp op (subst x v e)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2)
  | Fork e => Fork (subst x v e)
  | Atomically el e => Atomically (subst x v el) (subst x v e)
  | Primitive0 op => Primitive0 op
  | Primitive1 op e => Primitive1 op (subst x v e)
  | Primitive2 op e1 e2 => Primitive2 op (subst x v e1) (subst x v e2)
  (* | Primitive3 op e1 e2 e3 => Primitive3 op (subst x v e1) (subst x v e2) (subst x v e3) *)
  | ExternalOp op e => ExternalOp op (subst x v e)
  | CmpXchg e0 e1 e2 => CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)
  | NewProph => NewProph
  | ResolveProph e1 e2 => ResolveProph (subst x v e1) (subst x v e2)
  | LiteralValue l => LiteralValue ((subst_keyed_element x v) <$> l)
  | SelectStmtClauses default_handler l =>
      SelectStmtClauses ((subst x v) <$> default_handler) ((subst_comm_clause x v) <$> l)
  end
with subst_keyed_element (x : string) (v : val) (ke : keyed_element) : keyed_element :=
match ke with
| KeyedElement k el =>
    KeyedElement
      (match k with
       | Some (KeyExpression e) => Some $ KeyExpression (subst x v e)
       | Some (KeyLiteralValue l) => Some $ KeyLiteralValue ((subst_keyed_element x v) <$> l)
       | _ => k
       end)
      (match el with
       | ElementExpression e => ElementExpression (subst x v e)
       | ElementLiteralValue l => ElementLiteralValue ((subst_keyed_element x v) <$> l)
       end)
end
with subst_comm_clause (x : string) (v : val) (c : comm_clause) : comm_clause :=
match c with
| CommClause c e =>
    CommClause
      (match c with
       | SendCase t e => SendCase t (subst x v e)
       | RecvCase t e => RecvCase t (subst x v e)
       end)
      (subst x v e)
end
.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (word.not n)
  | NegOp, LitV (LitInt32 n) => Some $ LitV $ LitInt32 (word.not n)
  | NegOp, LitV (LitInt16 n) => Some $ LitV $ LitInt16 (word.not n)
  | MinusUnOp, LitV (LitByte n) => Some $ LitV $ LitByte (word.opp n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (word.opp n)
  | MinusUnOp, LitV (LitInt32 n) => Some $ LitV $ LitInt32 (word.opp n)
  | MinusUnOp, LitV (LitInt16 n) => Some $ LitV $ LitInt16 (word.opp n)
  | NegOp, LitV (LitByte n) => Some $ LitV $ LitByte (word.not n)
  | UToW64Op, LitV (LitInt v)   => Some $ LitV $ LitInt (W64 (uint.Z v))
  | UToW64Op, LitV (LitInt32 v) => Some $ LitV $ LitInt (W64 (uint.Z v))
  | UToW64Op, LitV (LitInt16 v) => Some $ LitV $ LitInt (W64 (uint.Z v))
  | UToW64Op, LitV (LitByte v)  => Some $ LitV $ LitInt (W64 (uint.Z v))
  | UToW32Op, LitV (LitInt v)   => Some $ LitV $ LitInt32 (W32 (uint.Z v))
  | UToW32Op, LitV (LitInt32 v) => Some $ LitV $ LitInt32 (W32 (uint.Z v))
  | UToW32Op, LitV (LitInt16 v) => Some $ LitV $ LitInt32 (W32 (uint.Z v))
  | UToW32Op, LitV (LitByte v)  => Some $ LitV $ LitInt32 (W32 (uint.Z v))
  | UToW16Op, LitV (LitInt v)   => Some $ LitV $ LitInt16 (W16 (uint.Z v))
  | UToW16Op, LitV (LitInt32 v) => Some $ LitV $ LitInt16 (W16 (uint.Z v))
  | UToW16Op, LitV (LitInt16 v) => Some $ LitV $ LitInt16 (W16 (uint.Z v))
  | UToW16Op, LitV (LitByte v)  => Some $ LitV $ LitInt16 (W16 (uint.Z v))
  | UToW8Op, LitV (LitInt v)    => Some $ LitV $ LitByte (W8 (uint.Z v))
  | UToW8Op, LitV (LitInt32 v)  => Some $ LitV $ LitByte (W8 (uint.Z v))
  | UToW8Op, LitV (LitInt16 v)  => Some $ LitV $ LitByte (W8 (uint.Z v))
  | UToW8Op, LitV (LitByte v)   => Some $ LitV $ LitByte (W8 (uint.Z v))
  | SToW64Op, LitV (LitInt v)   => Some $ LitV $ LitInt (W64 (sint.Z v))
  | SToW64Op, LitV (LitInt32 v) => Some $ LitV $ LitInt (W64 (sint.Z v))
  | SToW64Op, LitV (LitInt16 v) => Some $ LitV $ LitInt (W64 (sint.Z v))
  | SToW64Op, LitV (LitByte v)  => Some $ LitV $ LitInt (W64 (sint.Z v))
  | SToW32Op, LitV (LitInt v)   => Some $ LitV $ LitInt32 (W32 (sint.Z v))
  | SToW32Op, LitV (LitInt32 v) => Some $ LitV $ LitInt32 (W32 (sint.Z v))
  | SToW32Op, LitV (LitInt16 v) => Some $ LitV $ LitInt32 (W32 (sint.Z v))
  | SToW32Op, LitV (LitByte v)  => Some $ LitV $ LitInt32 (W32 (sint.Z v))
  | SToW16Op, LitV (LitInt v)   => Some $ LitV $ LitInt16 (W16 (sint.Z v))
  | SToW16Op, LitV (LitInt32 v) => Some $ LitV $ LitInt16 (W16 (sint.Z v))
  | SToW16Op, LitV (LitInt16 v) => Some $ LitV $ LitInt16 (W16 (sint.Z v))
  | SToW16Op, LitV (LitByte v)  => Some $ LitV $ LitInt16 (W16 (sint.Z v))
  | SToW8Op, LitV (LitInt v)    => Some $ LitV $ LitByte (W8 (sint.Z v))
  | SToW8Op, LitV (LitInt32 v)  => Some $ LitV $ LitByte (W8 (sint.Z v))
  | SToW8Op, LitV (LitInt16 v)  => Some $ LitV $ LitByte (W8 (sint.Z v))
  | SToW8Op, LitV (LitByte v)   => Some $ LitV $ LitByte (W8 (sint.Z v))
  | ToStringOp, LitV (LitByte v) => Some $ LitV $ LitString [v]
  | StringLenOp, LitV (LitString v) => Some $ LitV $ LitInt (W64 (Z.of_nat (length v)))
  | IsNoStringOverflowOp, LitV (LitString v) => Some $ LitV $ LitBool (bool_decide (Z.of_nat (length v) < 2^64))
  | _, _ => None
  end.

Definition bin_op_eval_word (op : bin_op) {width} {word: Interface.word width} (n1 n2 : word) : option word :=
  match op with
  | PlusOp => Some $ word.add (word:=word) n1 n2
  | MinusOp => Some $ word.sub (word:=word) n1 n2
  | MultOp => Some $ (word.mul (word:=word) n1 n2)
  | QuotOp => Some $ (word.divu (word:=word) n1 n2)
  | QuotSignedOp => Some $ (word.divs (word:=word) n1 n2)
  | RemOp => Some $ (word.modu (word:=word) n1 n2)
  | RemSignedOp => Some $ (word.mods (word:=word) n1 n2)
  | AndOp => Some $ (word.and (word:=word) n1 n2)
  | OrOp => Some $ (word.or (word:=word) n1 n2)
  | XorOp => Some $ (word.xor (word:=word) n1 n2)
  | ShiftLOp => Some $ (word.slu (word:=word) n1 n2)
  | ShiftROp => Some $ (word.sru (word:=word) n1 n2)
  | _ => None
  end.

Definition bin_op_eval_shift (op : bin_op) {width} {word: Interface.word width} (n1 n2 : word) : option word :=
  if decide (op = ShiftLOp ∨ op = ShiftROp) then
    bin_op_eval_word op n1 n2
  else None.

Definition bin_op_eval_compare (op : bin_op) {width} {word: Interface.word width} (n1 n2 : word) : option bool :=
  match op with
  | LeOp => Some $ bool_decide (word.unsigned n1 <= word.unsigned n2)
  | LtOp => Some $ bool_decide (word.unsigned n1 < word.unsigned n2)
  | EqOp => Some $ bool_decide (word.unsigned n1 = word.unsigned n2)
  | _ => None
  end.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option bool :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (b1 && b2)
  | OrOp => Some (b1 || b2)
  | XorOp => Some (xorb b1 b2)
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (bool_decide (b1 = b2))
  | OffsetOp _ => None (* Pointer arithmetic *)
  | _ => None
  end.

Definition bin_op_eval_string (op : bin_op) (s1 s2 : byte_string) : option byte_string :=
  match op with
  | PlusOp => Some $ (s1 ++ s2)
  | _ => None
  end.

Definition bin_op_eval_string_word (op : bin_op) (s1 : byte_string) {width} {word: Interface.word width} (w2 : word): option w8 :=
  match op with
  | StringGetOp => (s1 !! (uint.nat w2))
  | _ => None
  end.

(* exclude some comparisons *)
Fixpoint is_comparable v :=
  match v with
  | RecV _ _ _ | ExtV _ => False
  | PairV v1 v2 => is_comparable v1 ∧ is_comparable v2
  | InjLV v => is_comparable v
  | InjRV v => is_comparable v
  | _ => True
  end.
Global Instance is_comparable_decide v : Decision (is_comparable v).
Proof.
  induction v; simpl; auto; solve_decision.
Defined.

Section instances.
Inductive tree (T : Type) : Type :=
    Leaf : T → tree T | Node : string → list (tree T) → tree T.
Global Arguments Leaf {_} _ : assert.
Global Arguments Node {_} _ _ : assert.

Global Instance eq_decision_tree `{EqDecision T} : EqDecision (tree T).
Proof.
  refine (
      fix go x y :=
        match x, y with
        | Leaf x, Leaf x' => cast_if (decide (x = x'))
        | Node x ts, Node x' ts' => cast_if_and (decide (ts = ts')) (decide (x = x'))
        | _, _ => right _
        end
    ); try congruence.
  unshelve eapply list.list_eq_dec; done.
Qed.

Global Instance countable_tree `{Countable T} : Countable (tree T).
Proof.
  apply (inj_countable'
           (fix enc t :=
              match t with
              | Leaf x => GenLeaf x
              | Node x ts => GenNode (Pos.to_nat $ encode x) (enc <$> ts)
              end)
           (fix dec t :=
              match t with
              | GenLeaf x => Leaf x
              | GenNode x ts => Node (default "" $ decode (Pos.of_nat x)) (dec <$> ts)
              end
           )
        ).
  fix IH 1. intros []; try done.
  rewrite Pos2Nat.id. rewrite decode_encode /=. f_equal.
  induction l; first done. rewrite !fmap_cons. rewrite IH IHl //.
Qed.

Inductive leaf_type : Type :=
  | BaseLitLeaf (val : base_lit)
  | BinOpLeaf (val : bin_op)
  | BinderLeaf (val : binder)
  | FfiOpcodeLeaf (val : ffi_opcode)
  | FfiValLeaf (val : ffi_val)
  | GoInstructionLeaf (val : go_instruction)
  | GoStringLeaf (val : go_string)
  | ZLeaf (val : Z)
  | PrimOpArgs0Leaf (val : prim_op args0)
  | PrimOpArgs1Leaf (val : prim_op args1)
  | PrimOpArgs2Leaf (val : prim_op args2)
  | StringLeaf (val : string)
  | UnOpLeaf (val : un_op)
  | GoTypeLeaf (t : go.type).

Global Instance eq_decision_leaf_type : EqDecision leaf_type.
Proof. solve_decision. Qed.

Global Instance countable_leaf_type : Countable leaf_type.
Proof. Admitted.

Fixpoint enc_expr (v : expr) : tree leaf_type :=
  match v with
  | Val arg1 => Node "Val" [enc_val arg1]
  | Var arg1 => Node "Var" [Leaf $ StringLeaf arg1]
  | Rec arg1 arg2 arg3 => Node "Rec" [Leaf $ BinderLeaf arg1; Leaf $ BinderLeaf arg2; enc_expr arg3]
  | App arg1 arg2 => Node "App" [enc_expr arg1; enc_expr arg2]
  | UnOp arg1 arg2 => Node "UnOp" [Leaf $ UnOpLeaf arg1; enc_expr arg2]
  | BinOp arg1 arg2 arg3 => Node "BinOp" [Leaf $ BinOpLeaf arg1; enc_expr arg2; enc_expr arg3]
  | If arg1 arg2 arg3 => Node "If" [enc_expr arg1; enc_expr arg2; enc_expr arg3]
  | Pair arg1 arg2 => Node "Pair" [enc_expr arg1; enc_expr arg2]
  | Fst arg1 => Node "Fst" [enc_expr arg1]
  | Snd arg1 => Node "Snd" [enc_expr arg1]
  | InjL arg1 => Node "InjL" [enc_expr arg1]
  | InjR arg1 => Node "InjR" [enc_expr arg1]
  | Case arg1 arg2 arg3 => Node "Case" [enc_expr arg1; enc_expr arg2; enc_expr arg3]
  | Fork arg1 => Node "Fork" [enc_expr arg1]
  | Atomically arg1 arg2 => Node "Atomically" [enc_expr arg1; enc_expr arg2]
  | Primitive0 arg1 => Node "Primitive0" [Leaf $ PrimOpArgs0Leaf arg1]
  | Primitive1 arg1 arg2 => Node "Primitive1" [Leaf $ PrimOpArgs1Leaf arg1; enc_expr arg2]
  | Primitive2 arg1 arg2 arg3 => Node "Primitive2" [Leaf $ PrimOpArgs2Leaf arg1; enc_expr arg2; enc_expr arg3]
  | CmpXchg arg1 arg2 arg3 => Node "CmpXchg" [enc_expr arg1; enc_expr arg2; enc_expr arg3]
  | ExternalOp arg1 arg2 => Node "ExternalOp" [Leaf $ FfiOpcodeLeaf arg1; enc_expr arg2]
  | NewProph  => Node "NewProph" []
  | ResolveProph arg1 arg2 => Node "ResolveProph" [enc_expr arg1; enc_expr arg2]
  | LiteralValue arg1 => Node "LiteralValue" (enc_keyed_element <$> arg1)
  | SelectStmtClauses default_handler l =>
      Node "SelectStmtClauses" (
          (match default_handler with
           | Some default_handler => Node "Some" [enc_expr default_handler]
           | None => Node "None" []
           end) :: (enc_comm_clause <$> l))
  end
with enc_val (v : val) : tree leaf_type :=
  match v with
  | LitV arg1 => Node "LitV" [Leaf $ BaseLitLeaf arg1]
  | RecV arg1 arg2 arg3 => Node "RecV" [Leaf $ BinderLeaf arg1; Leaf $ BinderLeaf arg2; enc_expr arg3]
  | PairV arg1 arg2 => Node "PairV" [enc_val arg1; enc_val arg2]
  | InjLV arg1 => Node "InjLV" [enc_val arg1]
  | InjRV arg1 => Node "InjRV" [enc_val arg1]
  | ExtV arg1 => Node "ExtV" [Leaf $ FfiValLeaf arg1]
  | GoInstruction arg1 => Node "GoInstruction" [Leaf $ GoInstructionLeaf arg1]
  | ArrayV arg1 => Node "ArrayV" (enc_val <$> arg1)
  | InterfaceV arg1 =>
      Node "InterfaceV"
        (match arg1 with
         | Some (t, v) => [Leaf $ GoTypeLeaf t; enc_val v]
         | None => []
         end)
  | LiteralValueV arg1 => Node "LiteralValueV" (enc_keyed_element <$> arg1)
  | SelectStmtClausesV default_handler l =>
      Node "SelectStmtClausesV" (
          (match default_handler with
           | Some default_handler => Node "Some" [enc_expr default_handler]
           | None => Node "None" []
           end) :: (enc_comm_clause <$> l))
  end
with enc_keyed_element (v : keyed_element) : tree leaf_type :=
  match v with
  | KeyedElement k v =>
      Node "KeyedElement"
              (match k with
               | Some k => [enc_key k; enc_element v]
               | None => [enc_element v]
               end)
  end
with enc_key (v : key) : tree leaf_type :=
  match v with
  | KeyField arg1 => Node "KeyField" [Leaf $ GoStringLeaf arg1]
  | KeyInteger arg1 => Node "KeyInteger" [Leaf $ ZLeaf arg1]
  | KeyExpression arg1 => Node "KeyExpression" [enc_expr arg1]
  | KeyLiteralValue arg1 => Node "KeyLiteralValue" (enc_keyed_element <$> arg1)
  end
with enc_element (v : element) : tree leaf_type :=
  match v with
  | ElementExpression arg1 => Node "ElementExpression" [enc_expr arg1]
  | ElementLiteralValue arg1 => Node "ElementLiteralValue" (enc_keyed_element <$> arg1)
  end
with enc_comm_clause (v : comm_clause) : tree leaf_type :=
  match v with
  | CommClause c e => Node "CommClause" [enc_comm_case c; enc_expr e]
  end
with enc_comm_case (v : comm_case) : tree leaf_type :=
  match v with
  | SendCase t e => Node "SendCase" [Leaf $ GoTypeLeaf t; enc_expr e]
  | RecvCase t e => Node "RecvCase" [Leaf $ GoTypeLeaf t; enc_expr e]
  end
.

Fixpoint dec_expr (v : tree leaf_type) : expr :=
  match v with
  | Node "Val" [arg1] => Val (dec_val arg1)
  | Node "Var" [Leaf (StringLeaf arg1)] => Var arg1
  | Node "Rec" [Leaf (BinderLeaf arg1); Leaf (BinderLeaf arg2); arg3] =>
       Rec arg1 arg2 (dec_expr arg3)
  | Node "App" [arg1; arg2] => App (dec_expr arg1) (dec_expr arg2)
  | Node "UnOp" [Leaf (UnOpLeaf arg1); arg2] => UnOp arg1 (dec_expr arg2)
  | Node "BinOp" [Leaf (BinOpLeaf arg1); arg2; arg3] =>
      BinOp arg1 (dec_expr arg2) (dec_expr arg3)
  | Node "If" [arg1; arg2; arg3] => If (dec_expr arg1) (dec_expr arg2) (dec_expr arg3)
  | Node "Pair" [arg1; arg2] => Pair (dec_expr arg1) (dec_expr arg2)
  | Node "Fst" [arg1] => Fst (dec_expr arg1)
  | Node "Snd" [arg1] => Snd (dec_expr arg1)
  | Node "InjL" [arg1] => InjL (dec_expr arg1)
  | Node "InjR" [arg1] => InjR (dec_expr arg1)
  | Node "Case" [arg1; arg2; arg3] => Case (dec_expr arg1) (dec_expr arg2) (dec_expr arg3)
  | Node "Fork" [arg1] => Fork (dec_expr arg1)
  | Node "Atomically" [arg1; arg2] => Atomically (dec_expr arg1) (dec_expr arg2)
  | Node "Primitive0" [Leaf (PrimOpArgs0Leaf arg1)] => Primitive0 arg1
  | Node "Primitive1" [Leaf (PrimOpArgs1Leaf arg1); arg2] =>
       Primitive1 arg1 (dec_expr arg2)
  | Node "Primitive2" [Leaf (PrimOpArgs2Leaf arg1); arg2; arg3] =>
       Primitive2 arg1 (dec_expr arg2) (dec_expr arg3)
  | Node "CmpXchg" [arg1; arg2; arg3] =>
       CmpXchg (dec_expr arg1) (dec_expr arg2) (dec_expr arg3)
  | Node "ExternalOp" [Leaf (FfiOpcodeLeaf arg1); arg2] =>
       ExternalOp arg1 (dec_expr arg2)
  | Node "NewProph" [] => NewProph
  | Node "ResolveProph" [arg1; arg2] =>
       ResolveProph (dec_expr arg1) (dec_expr arg2)
  | Node "LiteralValue" arg1 => LiteralValue (dec_keyed_element <$> arg1)
  | Node "SelectStmtClauses" (default_handler :: l) =>
      SelectStmtClauses
      (match default_handler with
       | Node "None" [] => None
       | Node "Some" [e] => Some (dec_expr e)
       | _ => inhabitant
       end) (dec_comm_clause <$> l)
  | _ => inhabitant
  end
with dec_val (v : tree leaf_type) : val :=
  match v with
  | Node "LitV" [Leaf (BaseLitLeaf arg1)] => LitV arg1
  | Node "RecV" [Leaf (BinderLeaf arg1); Leaf (BinderLeaf arg2); arg3] =>
       RecV arg1 arg2 (dec_expr arg3)
  | Node "PairV" [arg1; arg2] => PairV (dec_val arg1) (dec_val arg2)
  | Node "InjLV" [arg1] => InjLV (dec_val arg1)
  | Node "InjRV" [arg1] => InjRV (dec_val arg1)
  | Node "ExtV" [Leaf (FfiValLeaf arg1)] => ExtV arg1
  | Node "GoInstruction" [Leaf (GoInstructionLeaf arg1)] => GoInstruction arg1
  | Node "ArrayV" arg1 => ArrayV (dec_val <$> arg1)
  | Node "InterfaceV" l =>
        (match l with
         | [Leaf (GoTypeLeaf t); v] => InterfaceV $ Some (t, dec_val v)
         | [] => InterfaceV None
         | _ => inhabitant
         end)
  | Node "LiteralValueV" arg1 => LiteralValueV (dec_keyed_element <$> arg1)
  | Node "SelectStmtClausesV" (default_handler :: l) =>
      SelectStmtClausesV
      (match default_handler with
       | Node "None" [] => None
       | Node "Some" [e] => Some (dec_expr e)
       | _ => inhabitant
       end) (dec_comm_clause <$> l)
  | _ => inhabitant
  end
with dec_keyed_element (v : tree leaf_type) : keyed_element :=
  match v with
  | Node "KeyedElement" l =>
      (match l with
       | [k; v] =>
            KeyedElement (Some $ dec_key k) (dec_element v)
       | [v] =>
            KeyedElement None (dec_element v)
       | _ => inhabitant
       end)
  | _ => inhabitant
  end
with dec_key (v : tree leaf_type) : key :=
  match v with
  | Node "KeyField" [Leaf (GoStringLeaf arg1)] => KeyField arg1
  | Node "KeyInteger" [Leaf (ZLeaf arg1)] => KeyInteger arg1
  | Node "KeyExpression" [arg1] => KeyExpression (dec_expr arg1)
  | Node "KeyLiteralValue" arg1 => KeyLiteralValue (dec_keyed_element <$> arg1)
  | _ => inhabitant
  end
with dec_element (v : tree leaf_type) : element :=
  match v with
  | Node "ElementExpression" [arg1] => ElementExpression (dec_expr arg1)
  | Node "ElementLiteralValue" arg1 => ElementLiteralValue (dec_keyed_element <$> arg1)
  | _ => inhabitant
  end
with dec_comm_clause (v : tree leaf_type) : comm_clause  :=
  match v with
  | Node "CommClause" [c; e] => CommClause (dec_comm_case c) (dec_expr e)
  | _ => inhabitant
  end
with dec_comm_case (v : tree leaf_type) : comm_case :=
  match v with
  | Node "SendCase" [Leaf (GoTypeLeaf t); e] => SendCase t (dec_expr e)
  | Node "RecvCase" [Leaf (GoTypeLeaf t); e] => RecvCase t (dec_expr e)
  | _ => inhabitant
  end.

Local Ltac prove :=
  fix I 1 with
    (pf_expr e : dec_expr $ enc_expr e = e)
    (pf_val v : dec_val $ enc_val v = v)
    (pf_keyed_element v : dec_keyed_element $ enc_keyed_element v = v)
    (pf_key v : dec_key $ enc_key v = v)
    (pf_element v : dec_element $ enc_element v = v)
    (pf_comm_clause v : dec_comm_clause $ enc_comm_clause v = v)
    (pf_comm_case v : dec_comm_case $ enc_comm_case v = v)
  ; clear I; intros [];
  repeat match goal with
    | |- _ => progress simpl
    | |- _ => progress f_equal
    | |- _ => done
    | x : list _ |- _ => induction x
    | x : option _ |- _ => induction x
    | x : prod _ _ |- _ => induction x
    end.

Lemma dec_expr_enc_expr :
  (∀ e, dec_expr $ enc_expr e = e).
Proof. prove. Qed.
Lemma dec_val_enc_val :
  (∀ e, dec_val $ enc_val e = e).
Proof. prove. Qed.
Lemma dec_keyed_element_enc_keyed_element :
  (∀ e, dec_keyed_element $ enc_keyed_element e = e).
Proof. prove. Qed.
Lemma dec_key_enc_key :
  (∀ e, dec_key $ enc_key e = e).
Proof. prove. Qed.
Lemma dec_element_enc_element :
  (∀ e, dec_element $ enc_element e = e).
Proof. prove. Qed.
Lemma dec_comm_clause_enc_comm_clause :
  (∀ e, dec_comm_clause $ enc_comm_clause e = e).
Proof. prove. Qed.
Lemma dec_comm_case_enc_comm_case :
  (∀ e, dec_comm_case $ enc_comm_case e = e).
Proof. prove. Qed.

Global Instance eq_decision_expr : EqDecision expr.
Proof.
  intros x y. pose proof dec_expr_enc_expr.
  destruct (decide (enc_expr x = enc_expr y)); [left|right]; congruence.
Qed.
Global Instance eq_decision_val : EqDecision val.
Proof.
  intros x y. pose proof dec_val_enc_val.
  destruct (decide (enc_val x = enc_val y)); [left|right]; congruence.
Qed.
Global Instance eq_decision_keyed_element : EqDecision keyed_element.
Proof.
  intros x y. pose proof dec_keyed_element_enc_keyed_element.
  destruct (decide (enc_keyed_element x = enc_keyed_element y)); [left|right]; congruence.
Qed.
Global Instance eq_decision_key : EqDecision key.
Proof.
  intros x y. pose proof dec_key_enc_key.
  destruct (decide (enc_key x = enc_key y)); [left|right]; congruence.
Qed.
Global Instance eq_decision_element : EqDecision element.
Proof.
  intros x y. pose proof dec_element_enc_element.
  destruct (decide (enc_element x = enc_element y)); [left|right]; congruence.
Qed.

Global Instance countable_expr : Countable expr.
Proof.
  apply (inj_countable' enc_expr dec_expr).
  intros ?. apply dec_expr_enc_expr.
Qed.
Global Instance countable_val : Countable val.
Proof.
  apply (inj_countable' enc_val dec_val).
  intros ?. apply dec_val_enc_val.
Qed.
Global Instance countable_keyed_element : Countable keyed_element.
Proof.
  apply (inj_countable' enc_keyed_element dec_keyed_element).
  intros ?. apply dec_keyed_element_enc_keyed_element.
Qed.
Global Instance countable_key : Countable key.
Proof.
  apply (inj_countable' enc_key dec_key).
  intros ?. rewrite /= dec_key_enc_key //.
Qed.
Global Instance countable_element : Countable element.
Proof.
  apply (inj_countable' enc_element dec_element).
  intros ?. apply dec_element_enc_element.
Qed.

End instances.

Definition bin_op_eval_eq (v1 v2 : val) : option base_lit :=
  if decide (is_comparable v1 ∧ is_comparable v2) then
    Some $ LitBool $ bool_decide (v1 = v2)
  else None.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then LitV <$> bin_op_eval_eq v1 v2
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) =>
      LitV <$> ((LitInt <$> bin_op_eval_word op n1 n2)
                  ∪ (LitBool <$> bin_op_eval_compare op n1 n2))
    | LitV (LitInt32 n1), LitV (LitInt32 n2) =>
      LitV <$> ((LitInt32 <$> bin_op_eval_word op n1 n2)
                  ∪ (LitBool <$> bin_op_eval_compare op n1 n2))
    | LitV (LitInt16 n1), LitV (LitInt16 n2) =>
      LitV <$> ((LitInt16 <$> bin_op_eval_word op n1 n2)
                  ∪ (LitBool <$> bin_op_eval_compare op n1 n2))
    | LitV (LitByte n1), LitV (LitByte n2) =>
      LitV <$> ((LitByte <$> bin_op_eval_word op n1 n2)
                  ∪ (LitBool <$> bin_op_eval_compare op n1 n2))

    (* Shifts do not require matching bit width *)
    | LitV (LitByte n1), LitV (LitInt n2) =>
      LitV <$> (LitByte <$> bin_op_eval_shift op n1 (W8 (uint.Z n2)))
    | LitV (LitByte n1), LitV (LitInt32 n2) =>
      LitV <$> (LitByte <$> bin_op_eval_shift op n1 (W8 (uint.Z n2)))
    | LitV (LitByte n1), LitV (LitInt16 n2) =>
      LitV <$> (LitByte <$> bin_op_eval_shift op n1 (W8 (uint.Z n2)))
    | LitV (LitInt16 n1), LitV (LitInt n2) =>
      LitV <$> (LitInt16 <$> bin_op_eval_shift op n1 (W16 (uint.Z n2)))
    | LitV (LitInt16 n1), LitV (LitInt32 n2) =>
      LitV <$> (LitInt16 <$> bin_op_eval_shift op n1 (W16 (uint.Z n2)))
    | LitV (LitInt16 n1), LitV (LitByte n2) =>
      LitV <$> (LitInt16 <$> bin_op_eval_shift op n1 (W16 (uint.Z n2)))
    | LitV (LitInt32 n1), LitV (LitInt n2) =>
      LitV <$> (LitInt32 <$> bin_op_eval_shift op n1 (W32 (uint.Z n2)))
    | LitV (LitInt32 n1), LitV (LitInt16 n2) =>
      LitV <$> (LitInt32 <$> bin_op_eval_shift op n1 (W32 (uint.Z n2)))
    | LitV (LitInt32 n1), LitV (LitByte n2) =>
      LitV <$> (LitInt32 <$> bin_op_eval_shift op n1 (W32 (uint.Z n2)))
    | LitV (LitInt n1), LitV (LitByte n2) =>
      LitV <$> (LitInt <$> bin_op_eval_shift op n1 (W64 (uint.Z n2)))
    | LitV (LitInt n1), LitV (LitInt16 n2) =>
      LitV <$> (LitInt <$> bin_op_eval_shift op n1 (W64 (uint.Z n2)))
    | LitV (LitInt n1), LitV (LitInt32 n2) =>
      LitV <$> (LitInt <$> bin_op_eval_shift op n1 (W64 (uint.Z n2)))

    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> (LitBool <$> bin_op_eval_bool op b1 b2)
    | LitV (LitString s1), LitV (LitString s2) => LitV <$> (LitString <$> bin_op_eval_string op s1 s2)
    | LitV (LitLoc l), LitV (LitInt off) => match op with
                                           | OffsetOp k =>
                                             Some $ LitV $ LitLoc (l +ₗ k * (uint.Z (off: u64)))
                                           | _ => None
                                           end
    | LitV (LitString s1), LitV (LitByte n) => LitV <$> (LitByte <$> bin_op_eval_string_word op s1 n)
    | LitV (LitString s1), LitV (LitInt16 n) => LitV <$> (LitByte <$> bin_op_eval_string_word op s1 n)
    | LitV (LitString s1), LitV (LitInt32 n) => LitV <$> (LitByte <$> bin_op_eval_string_word op s1 n)
    | LitV (LitString s1), LitV (LitInt n) => LitV <$> (LitByte <$> bin_op_eval_string_word op s1 n)
    | _, _ => None
    end.

(* [h] is added on the right here to make [state_init_heap_singleton] true. *)
Definition state_insert_list (l: loc) (vs: list val) (σ: state): state :=
  set heap (λ h, heap_array l (fmap Free vs) ∪ h) σ.

Definition concat_replicate {A} (n: nat) (l: list A): list A :=
  concat (replicate n l).

Definition state_init_heap (l : loc) (n : Z) (v : val) (σ : state) : state :=
  state_insert_list l (concat_replicate (Z.to_nat n) (flatten_struct v)) σ.

Lemma state_init_heap_singleton l v σ :
  state_init_heap l 1 v σ = state_insert_list l (flatten_struct v) σ.
Proof.
  destruct σ as [h p]. rewrite /state_init_heap /concat_replicate /state_insert_list /set /=. f_equal.
  rewrite right_id. done.
Qed.

Definition is_Free {A} (mna: option (nonAtomic A)) := exists x, mna = Some (Free x).
Global Instance is_Free_dec A (x: option (nonAtomic A)) : Decision (is_Free x).
Proof.
  hnf; rewrite /is_Free /Free.
  destruct x as [na|]; [ | right; abstract (destruct 1; congruence) ].
  destruct na as ([|[]]&?).
  - right; abstract (destruct 1; congruence).
  - left; eauto.
  - right; abstract (destruct 1; congruence).
Defined.

Definition is_Writing {A} (mna: option (nonAtomic A)) := exists x, mna = Some (Writing, x).
Global Instance is_Writing_dec A (x: option (nonAtomic A)) : Decision (is_Writing x).
Proof.
  hnf; rewrite /is_Writing.
  destruct x as [na|]; [ | right; abstract (destruct 1; congruence) ].
  destruct na as ([|]&?).
  - left; eauto.
  - right; abstract (destruct 1; congruence).
Defined.

Existing Instances r_mbind r_mret r_fmap.

Definition ret_expr {state} (e:expr): transition state (list observation * expr * list expr) :=
  ret ([],e,[]).

Definition atomically {state} (tr: transition state val): transition state (list observation * expr * list expr) :=
  (λ v, ([], Val v, [])) <$> tr.

Definition atomicallyM {state} (tr: transition state expr): transition state (list observation * expr * list expr)
  := (λ v, ([], v, [])) <$> tr.

Definition isFresh (σg: state*global_state) (l: loc) :=
  (forall i, l +ₗ i ≠ null ∧ σg.1.(heap) !! (l +ₗ i) = None)%Z ∧
  (addr_offset l = 0).

Lemma addr_base_non_null_offset l:
  l ≠ null → (addr_offset l = 0)%Z →
  addr_base l ≠ null.
Proof.
  intros Hneq Heq Heq'. rewrite /addr_base -Heq addr_encode_decode' in Heq'.
  congruence.
Qed.

Lemma addr_base_non_null l:
  addr_base l ≠ null →
  l ≠ null.
Proof.
  intros Hneq Heq'. rewrite /addr_base Heq' addr_encode_decode' in Hneq.
  congruence.
Qed.

Lemma plus_off_preserves_non_null l:
  addr_base l ≠ null →
  ∀ z, l ≠ addr_plus_off null z.
Proof.
  intros Hneq z Heq. apply (f_equal addr_base) in Heq.
  rewrite addr_base_of_plus /null //= in Heq.
Qed.

Theorem isFresh_not_null σ l :
  isFresh σ l -> l ≠ null.
Proof.
  intros Hbound **.
  rewrite -(loc_add_0 l).
  eapply Hbound.
Qed.

Theorem isFresh_offset0 σ l :
  isFresh σ l -> addr_offset l = 0.
Proof.
  intros Hbound. destruct Hbound as (?&?); eauto.
Qed.

Theorem isFresh_base σ l :
  isFresh σ l -> addr_base l = l.
Proof.
  intros Hbound **. eapply addr_offset_0_is_base, isFresh_offset0; eauto.
Qed.

Theorem fresh_locs_isFresh σg :
  isFresh σg (fresh_locs (dom σg.1.(heap))).
Proof.
  split.
  - split.
    * apply fresh_locs_non_null; auto.
    * apply (not_elem_of_dom (D := gset loc)).
        by apply fresh_locs_fresh.
  - auto.
Qed.

Definition gen_isFresh σg : {l: loc | isFresh σg l}.
Proof.
  refine (exist _ (fresh_locs (dom σg.1.(heap))) _).
  by apply fresh_locs_isFresh.
Defined.

Global Instance alloc_gen : GenPred loc (state*global_state) (isFresh) :=
  fun _ σ => Some (gen_isFresh σ).

(** Generate a location for a fresh block; doesn't actually insert anything into
the heap. *)
Definition allocateN : transition (state*global_state) loc :=
  suchThat (isFresh).

Global Instance newProphId_gen: GenPred proph_id (state*global_state) (fun '(σ,g) p => p ∉ g.(used_proph_id)).
Proof.
  refine (fun _ '(σ,g) => Some (exist _ (fresh g.(used_proph_id)) _)).
  apply is_fresh.
Defined.

Definition newProphId: transition (state*global_state) proph_id :=
  suchThat (fun '(σ,g) p => p ∉ g.(used_proph_id)).

Instance gen_anyInt Σ: GenPred u64 Σ (fun _ _ => True).
  refine (fun z _ => Some (W64 z ↾ _)); auto.
Defined.

Definition arbitraryInt {state}: transition state u64 :=
  suchThat (fun _ _ => True).

Fixpoint transition_repeat (n:nat) {Σ T} (t: T → transition Σ T) (init:T) : transition Σ T :=
  match n with
  | 0%nat => ret init
  | S n => Transitions.bind (t init) (transition_repeat n t)
  end.

Definition transition_star {Σ T} (t : T → transition Σ T) (init:T) : transition Σ T :=
  n ← suchThat (gen:=fun _ _ => None) (fun _ (_:nat) => True);
  transition_repeat n t init.

Definition modifyσ (f : state → state) : transition (state*global_state) () :=
  modify (λ '(σ, g), (f σ, g)).
Definition modifyg (f : global_state → global_state) : transition (state*global_state) () :=
  modify (λ '(σ, g), (σ, f g)).

(* Only give semantics to CmpXchg for integers. *)
Definition val_cmpxchg_safe (v : val) : bool :=
  match v with
  | LitV l =>
      match l with
      | LitInt _ | LitInt32 _ | LitInt16 _ | LitByte _ => true
      | LitBool _ => true (* for old goose lock.v *)
      | _ => false
      end
  | _ => false
  end.

Definition go_instruction_step (op : go_instruction) (arg : val) :
  transition (state * global_state) (list observation * expr * list expr) :=
  '(e', s') ← suchThat
    (λ '(σ,g) '(e', s'),
       let _ := σ.(go_state).(go_lctx) in
       let _ := g.(go_gctx) in
       is_go_step op arg e' σ.(go_state).(package_state) s')
    (gen:=fallback_genPred _);
  modifyσ $ set go_state $ set package_state (λ _, s') ;;
  ret_expr e'.

Definition base_trans (e: expr) :
 transition (state * global_state) (list observation * expr * list expr) :=
  match e with
  | Rec f x e => atomically $ ret $ RecV f x e
  | Pair (Val v1) (Val v2) => atomically $ ret $ PairV v1 v2
  | InjL (Val v) => atomically $ ret $ InjLV v
  | InjR (Val v) => atomically $ ret $ InjRV v
  | App (Val (RecV f x e1)) (Val v2) =>
    ret_expr $ subst' x v2 (subst' f (RecV f x e1) e1)
  | UnOp op (Val v) => atomically $ unwrap $ un_op_eval op v
  | BinOp op (Val v1) (Val v2) => atomically $ unwrap $ bin_op_eval op v1 v2
  | If (Val (LitV (LitBool b))) e1 e2 => ret_expr $ if b then e1 else e2
  | Fst (Val (PairV v1 v2)) => atomically $ ret v1
  | Snd (Val (PairV v1 v2)) => atomically $ ret v2
  | Case (Val (InjLV v)) e1 e2 => ret_expr $ App e1 (Val v)
  | Case (Val (InjRV v)) e1 e2 => ret_expr $ App e2 (Val v)
  | Fork e => ret ([], Val $ LitV LitUnit, [e])
  (* handled separately *)
  | Atomically _ _ => undefined
  | ArbitraryInt =>
    atomically
      (x ← arbitraryInt;
      ret $ LitV $ LitInt x)
  | AllocN (Val (LitV (LitInt n))) (Val v) =>
    atomically
      (check (0 < uint.Z n)%Z;;
       l ← allocateN;
       modifyσ (state_init_heap l (uint.Z n) v);;
       ret $ LitV $ LitLoc l)
   | StartRead (Val (LitV (LitLoc l))) => (* non-atomic load part 1 (used for map accesses) *)
     atomically
       (nav ← reads (λ '(σ,g), σ.(heap) !! l) ≫= unwrap;
        match nav with
        | (Reading n, v) =>
          modifyσ (set heap <[l:=(Reading (S n), v)]>);;
          ret v
        | _ => undefined
        end)
   | FinishRead (Val (LitV (LitLoc l))) => (* non-atomic load part 2 *)
     atomically
       (nav ← reads (λ '(σ,g), σ.(heap) !! l) ≫= unwrap;
        match nav with
        | (Reading (S n), v) =>
          modifyσ (set heap <[l:=(Reading n, v)]>);;
                 ret $ LitV $ LitUnit
        | _ => undefined
        end)
   | Load (Val (LitV (LitLoc l))) => (* atomic load (used for most normal Go loads) *)
     atomically
       (nav ← reads (λ '(σ,g), σ.(heap) !! l) ≫= unwrap;
        match nav with
        | (Reading _, v) => ret v
        | _ => undefined
        end)
  | PrepareWrite (Val (LitV (LitLoc l))) => (* non-atomic write part 1 *)
    atomically
      (v ← (reads (λ '(σ,g), σ.(heap) !! l) ≫= unwrap);
        match v with
        | (Reading 0, v) =>
          modifyσ (set heap <[l:=(Writing, v)]>);;
          ret $ LitV $ LitUnit
        | _ => undefined
        end)
  | FinishStore (Val (LitV (LitLoc l))) (Val v) => (* non-atomic write part 2 *)
    atomically
      (nav ← reads (λ '(σ,g), σ.(heap) !! l);
       check (is_Writing nav);;
       modifyσ (set heap <[l:=Free v]>);;
       ret $ LitV $ LitUnit)
  | AtomicSwap (Val (LitV (LitLoc l))) (Val v) => (* atomic swap *)
    atomically
      (nav ← reads (λ '(σ,g), σ.(heap) !! l) ≫= unwrap;
       match nav with
       | (Reading 0, v0) =>
           modifyσ (set heap <[l:=Free v]>);;
           ret $ v0
       | _ => undefined
      end)
  | AtomicOp op (Val (LitV (LitLoc l))) (Val v) => (* atomic add *)
    atomically
      (nav ← reads (λ '(σ,g), σ.(heap) !! l) ≫= unwrap;
       match nav with
       | (Reading 0, oldv) =>
           v ← unwrap (bin_op_eval op oldv v);
           modifyσ (set heap <[l:=Free v]>);;
           ret $ v
       | _ => undefined
      end)
  | ExternalOp op (Val v) => atomicallyM $ ffi_step op v
  | Input (Val (LitV (LitInt selv))) =>
    atomically
      (x ← reads (λ '(σ,g), σ.(oracle) σ.(trace) selv);
      modifyσ (set trace (add_event (In_ev (LitInt selv) (LitInt x))));;
      ret $ LitV $ LitInt $ x)
  | Output (Val (LitV v)) =>
    atomically
      (modifyσ (set trace (add_event (Out_ev v)));;
       ret $ LitV $ LitUnit)
  | App (Val (GoInstruction op)) (Val arg) =>
      go_instruction_step op arg
  | CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2) =>
    atomically
      (nav ← reads (λ '(σ,g), σ.(heap) !! l) ≫= unwrap;
      match nav with
      | (Reading n, vl) =>
        check (val_cmpxchg_safe vl || val_cmpxchg_safe v1 = true);;
        when (vl = v1) (check (n = 0%nat);; modifyσ (set heap <[l:=Free v2]>));;
        ret $ PairV vl (LitV $ LitBool (bool_decide (vl = v1)))
      | _ => undefined
      end)
  | NewProph =>
    atomically
      (p ← newProphId;
       modifyg (set used_proph_id ({[ p ]} ∪.));;
       ret $ LitV $ LitProphecy p)
  | ResolveProph (Val (LitV (LitProphecy p))) (Val w) =>
    ret ([(p, w)], Val $ LitV LitUnit, [])
  | LiteralValue l => atomically $ ret $ LiteralValueV l
  | SelectStmtClauses d cs => atomically $ ret $ SelectStmtClausesV d cs
  | _ => undefined
  end.

Definition base_step:
    expr -> state -> global_state -> list observation -> expr -> state -> global_state -> list expr -> Prop :=
  fun e s g κs e' s' g' efs =>
      relation.denote (base_trans e) (s,g) (s',g') (κs, e', efs).

Definition fill' (K : list (ectx_item)) (e : expr) : expr := foldl (flip fill_item) e K.

Inductive prim_step' (e1 : expr) (σ1 : state) (g1 : global_state) (κ : list (observation))
    (e2 : expr) (σ2 : state) (g2 : global_state) (efs : list (expr)) : Prop :=
  Ectx_step' K e1' e2' :
    e1 = fill' K e1' → e2 = fill' K e2' →
    base_step e1' σ1 g1 κ e2' σ2 g2 efs → prim_step' e1 σ1 g1 κ e2 σ2 g2 efs.

Definition irreducible' (e : expr) (σ : state) (g : global_state) :=
  ∀ κ e' σ' g' efs, ¬prim_step' e σ g κ e' σ' g' efs.
Definition stuck' (e : expr) (σ : state) (g : global_state) :=
  to_val e = None ∧ irreducible' e σ g.

Definition prim_step'_safe e s g :=
  (∀ e' s' g', rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' []) (e, (s, g)) (e', (s', g')) →
            ¬ stuck' e' s' g'
              (* TODO: this definition could also forbid any executions of e
              starting at (s, g) from producing forked threads; otherwise our
              specifications implicitly say Atomically(Fork(#())) aborts. Our
              typing judgment for the txn refinement proof already forbids any
              Fork expressions. *)
  ).

Inductive base_step_atomic:
    expr -> state -> global_state -> list observation -> expr -> state -> global_state -> list expr -> Prop :=
 | base_step_trans : ∀ e s g κs e' s' g' efs,
     base_step e s g κs e' s' g' efs →
     base_step_atomic e s g κs e' s' g' efs
 | base_step_atomically : ∀ (vl : val) e s g κs v' s' g',
     rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' []) (e, (s, g)) (Val (InjRV v'), (s', g')) →
     prim_step'_safe e s g →
     base_step_atomic (Atomically (of_val vl) e) s g κs (Val (InjRV v')) s' g' []
 | base_step_atomically_fail : ∀ vl e s g κs,
     (* An atomically block can non-deterministically fail _ONLY_ if the block would not trigger UB *)
     prim_step'_safe e s g →
     base_step_atomic (Atomically (of_val vl) e) s g κs (Val (InjLV (LitV LitUnit))) s g []
.

Lemma base_step_atomic_inv e s g κs e' s' g' efs :
  base_step_atomic e s g κs e' s' g' efs →
  (∀ el e'', e ≠ Atomically el e'') →
  base_step e s g κs e' s' g' efs.
Proof.
  inversion 1; subst; eauto.
  - intros. contradiction (H2 (of_val vl) e0); auto.
  - intros. contradiction (H1 (of_val vl) e0); auto.
Qed.

(** Basic properties about the language *)
Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

Lemma fill_item_val_inv Ki v v' :
  is_Some (to_val (fill_item Ki (of_val v))) → is_Some (to_val (fill_item Ki (of_val v'))).
Proof. intros. induction Ki; simplify_option_eq; eauto. Qed.

Lemma suchThat_false state T (s1 s2: state) (v: T) :
  relation.suchThat (fun _ _ => False) s1 s2 v -> False.
Proof.
  inversion 1; auto.
Qed.

Hint Resolve suchThat_false : core.

Lemma val_base_stuck e1 σ1 g1 κ e2 σ2 g2 efs :
  base_step e1 σ1 g1 κ e2 σ2 g2 efs → to_val e1 = None.
Proof.
  rewrite /base_step; intros.
  destruct e1; auto; simpl.
  exfalso.
  simpl in H; eapply suchThat_false; eauto.
Qed.

Lemma val_base_atomic_stuck e1 σ1 g1 κ e2 σ2 g2 efs :
  base_step_atomic e1 σ1 g1 κ e2 σ2 g2 efs → to_val e1 = None.
Proof.
  inversion 1; subst; eauto using val_base_stuck.
Qed.


Ltac inv_undefined :=
  match goal with
  | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] =>
    destruct e; try (apply suchThat_false in H; contradiction)
  end.

Lemma base_ctx_step_val Ki e σ1 g1 κ e2 σ2 g2 efs :
  base_step (fill_item Ki e) σ1 g1 κ e2 σ2 g2 efs → is_Some (to_val e).
Proof.
  revert κ e2.
  induction Ki; intros;
    rewrite /base_step /= in H;
    repeat inv_undefined; eauto.
  - inversion H; subst; clear H. done.
Qed.

Lemma base_ctx_step_atomic_val Ki e σ1 g1 κ e2 σ2 g2 efs :
  base_step_atomic (fill_item Ki e) σ1 g1 κ e2 σ2 g2 efs → is_Some (to_val e).
Proof.
  inversion 1; subst; eauto using base_ctx_step_val.
  - destruct Ki; simpl in H0; try solve [ inversion H0 ].
    inversion H0. subst. eauto.
  - destruct Ki; simpl in H0; try solve [ inversion H0 ].
    inversion H0. subst. eauto.
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof using ext.
  clear ffi_semantics ffi.
  revert Ki1. induction Ki2, Ki1; naive_solver eauto with f_equal.
Qed.

Lemma alloc_fresh v (n: u64) σ g :
  let l := fresh_locs (dom σ.(heap)) in
  (0 < uint.Z n)%Z →
  base_step_atomic (AllocN ((Val $ LitV $ LitInt $ n)) (Val v)) σ g []
            (Val $ LitV $ LitLoc l) (state_init_heap l (uint.Z n) v σ) g [].
Proof.
  intros.
  constructor 1.
  rewrite /base_step /=.
  monad_simpl.
  eapply relation.bind_runs with (σ,g) l.
  { econstructor.
    apply fresh_locs_isFresh.
  }
  monad_simpl.
Qed.

Lemma arbitrary_int_step σ g :
  base_step_atomic (ArbitraryInt) σ g []
            (Val $ LitV $ LitInt $ W64 0) σ g [].
Proof.
  intros.
  constructor 1.
  rewrite /base_step /=.
  monad_simpl.
  eapply relation.bind_runs; [ | monad_simpl ].
  constructor; auto.
Qed.

Lemma new_proph_id_fresh σ g :
  let p := fresh g.(used_proph_id) in
  base_step_atomic NewProph σ g [] (Val $ LitV $ LitProphecy p) σ (set used_proph_id ({[ p ]} ∪.) g) [].
Proof.
  intro p.
  constructor 1.
  rewrite /base_step /=.
  monad_simpl.
  eapply relation.bind_runs with (σ,g) p.
  { econstructor.
    apply is_fresh. }
  monad_simpl.
Qed.

Lemma goose_lang_mixin : EctxiLanguageMixin of_val to_val fill_item base_step_atomic.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_base_atomic_stuck,
    fill_item_val, fill_item_val_inv, fill_item_no_val_inj, base_ctx_step_atomic_val.
Qed.

End external.

Global Notation zero_val := zero_val_def.

(** Language *)

Arguments ffi_semantics ext ffi : clear implicits.
Arguments goose_lang_mixin {ext} {ffi} ffi_semantics.

Section goose.
  Context {ext: ffi_syntax} {ffi: ffi_model}
          {ffi_semantics: ffi_semantics ext ffi}.
  Canonical Structure goose_ectxi_lang := (EctxiLanguage (goose_lang_mixin ffi_semantics)).
  Canonical Structure goose_ectx_lang := (EctxLanguageOfEctxi goose_ectxi_lang).
  Canonical Structure goose_lang := (LanguageOfEctx goose_ectx_lang).
  Canonical Structure goose_crash_lang : crash_semantics goose_lang :=
    {| crash_prim_step := goose_crash |}.

(* The following lemma is not provable using the axioms of [ectxi_language].
The proof requires a case analysis over context items ([destruct i] on the
last line), which in all cases yields a non-value. To prove this lemma for
[ectxi_language] in general, we would require that a term of the form
[fill_item i e] is never a value. *)
Lemma to_val_fill_some K e v : to_val (fill K e) = Some v → K = [] ∧ e = Val v.
Proof.
  intro H. destruct K as [|Ki K]; first by apply of_to_val in H. exfalso.
  assert (to_val e ≠ None) as He.
  { intro A. by rewrite fill_not_val in H. }
  assert (∃ w, e = Val w) as [w ->].
  { destruct e; try done; eauto. }
  assert (to_val (fill (Ki :: K) (Val w)) = None).
  { destruct Ki; simpl; apply fill_not_val; done. }
  by simplify_eq.
Qed.

Lemma prim_step_to_val_is_base_step e σ1 g1 κs w σ2 g2 efs :
  prim_step e σ1 g1 κs (Val w) σ2 g2 efs → base_step_atomic (ffi_semantics:=ffi_semantics) e σ1 g1 κs (Val w) σ2 g2 efs.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some w) as H3; first by rewrite -H2.
  apply to_val_fill_some in H3 as [-> ->]. subst e. done.
Qed.

Lemma base_prim_step_trans e σ g κ e' σ' g' efs :
  base_step e σ g κ e' σ' g' efs →
  ectx_language.prim_step e σ g κ e' σ' g' efs.
Proof.
  intros.
  apply base_prim_step. apply base_step_trans.
  auto.
Qed.

Lemma base_prim_step_trans' e σ g κ e' σ' g' efs :
  base_step e σ g κ e' σ' g' efs →
  prim_step' e σ g κ e' σ' g' efs.
Proof. apply Ectx_step' with empty_ectx; by rewrite ?fill_empty. Qed.

Definition base_reducible' (e : expr) (σ : state) (g : global_state) :=
  ∃ κ e' σ' g' efs, base_step e σ g κ e' σ' g' efs.
Definition base_irreducible' (e : expr) (σ : state) (g : global_state) :=
  ∀ κ e' σ' g' efs, ¬base_step e σ g κ e' σ' g' efs.
Definition reducible' (e : expr) (σ : state) (g : global_state) :=
  ∃ κ e' σ' g' efs, prim_step' e σ g κ e' σ' g' efs.

Lemma prim_base_reducible' e σ g :
  reducible' e σ g → sub_redexes_are_values e → base_reducible' e σ g.
Proof.
  intros (κ&e'&σ'&g'&efs&[K e1' e2' -> -> Hstep]) Hsub.
  assert (K = empty_ectx).
  { apply val_base_stuck in Hstep.
    eapply Hsub; eauto.
  }
  subst. rewrite //= /base_reducible. econstructor; eauto.
Qed.

Lemma not_reducible' e σ g : ¬reducible' e σ g ↔ irreducible' e σ g.
Proof. unfold reducible', irreducible'. naive_solver. Qed.
Lemma not_base_reducible' e σ g : ¬base_reducible' e σ g ↔ base_irreducible' e σ g.
Proof. unfold base_reducible', base_irreducible'. naive_solver. Qed.

Lemma prim_base_irreducible' e σ g :
  base_irreducible' e σ g → sub_redexes_are_values e → irreducible' e σ g.
Proof.
  rewrite -not_reducible' -not_base_reducible'; eauto using prim_base_reducible'.
Qed.

Class LanguageCtx' (K : expr → expr) : Prop :=
  { fill_not_val' : ∀ e, to_val e = None → to_val (K e) = None;
    fill_step' : ∀ e1 σ1 g1 κ e2 σ2 g2 efs,
                  prim_step' e1 σ1 g1 κ e2 σ2 g2 efs → prim_step' (K e1) σ1 g1 κ (K e2) σ2 g2 efs;
    fill_step_inv' e1' σ1 g1 κ e2 σ2 g2 efs :
      to_val e1' = None → prim_step' (K e1') σ1 g1 κ e2 σ2 g2 efs →
      ∃ e2', e2 = K e2' ∧ prim_step' e1' σ1 g1 κ e2' σ2 g2 efs
  }.

Lemma fill_comp' K1 K2 e : fill' K1 (fill' K2 e) = fill' (comp_ectx K1 K2) e.
Proof.
  rewrite /fill'.
  pose proof (fill_comp (Λ := goose_ectx_lang)).
  rewrite /ectx_language.fill//=/fill in H.
  eapply H.
Qed.

Lemma base_redex_unique K K' e e' σ g :
  fill' K e = fill' K' e' →
  base_reducible e σ g →
  base_reducible e' σ g →
  K = K' ∧ e = e'.
Proof.
  intros Heq (κ & e2 & σ2 & g2 & efs & Hred) (κ' & e2' & σ2' & g2' & efs' & Hred').
  edestruct (step_by_val K' K e' e) as [K'' HK];
    [by eauto using ectx_language.val_base_stuck..|].
  subst K. move: Heq. rewrite -fill_comp'. intros <-%(inj (fill _)).
  destruct (ectx_language.base_ctx_step_val _ _ _ _ _ _ _ _ _ Hred') as [[]%not_eq_None_Some|HK''].
  { by eapply ectx_language.val_base_stuck. }
  subst. rewrite //=.
Qed.

Global Instance ectx_lang_ctx' K : LanguageCtx' (fill K).
Proof.
  split; simpl.
  - intros. eapply fill_not_val; eauto.
  - intros ???????? [K' e1' e2' Heq1 Heq2 Hstep].
    by exists (comp_ectx K K') e1' e2'; rewrite ?Heq1 ?Heq2 ?fill_comp.
  - intros e1 σ1 g1 κ e2 σ2 g2 efs Hnval [K'' e1'' e2'' Heq1 -> Hstep].
    destruct (step_by_val K K'' e1 e1'' σ1 g1 κ e2'' σ2 g2 efs) as [K' ->]; eauto.
    { econstructor. eauto. }
    rewrite -fill_comp' in Heq1; apply (inj (fill _)) in Heq1.
    exists (fill K' e2''); rewrite -fill_comp'; split; auto.
    econstructor; eauto.
Qed.

Instance id_ctx' : LanguageCtx' (fun x => x).
Proof. split; intuition eauto. Qed.

Instance comp_ctx' K K':
  LanguageCtx' K →
  LanguageCtx' K' →
  LanguageCtx' (λ x, K' (K x)).
Proof.
  intros Hctx Hctx'.
  split; intros.
  - by do 2 apply fill_not_val'.
  - by do 2 apply fill_step'.
  - edestruct (@fill_step_inv' _ Hctx' (K e1')); eauto; intuition.
    { apply fill_not_val'; auto. }
    subst.
    edestruct (@fill_step_inv' _ Hctx); eauto; intuition.
    subst.
    eauto.
Qed.

Lemma stuck'_fill K `{Hctx: LanguageCtx' K}  e σ g :
  stuck' e σ g → stuck' (K e) σ g.
Proof.
  intros (Hnval&Hirred). split.
  - by apply fill_not_val'.
  - move:Hirred. rewrite -!not_reducible'.
    intros Hnred Hred.
    apply Hnred.
    destruct Hred as (e'&σ'&g'&k&efs&Hstep); unfold reducible'.
    apply fill_step_inv' in Hstep; eauto.
    naive_solver.
Qed.

Definition trace_observable e r σ g tr :=
  ∃ σ2 g2 t2 stat, erased_rsteps (CS:=goose_crash_lang) r ([e], (σ, g)) (t2, (σ2, g2)) stat ∧ σ2.(trace) = tr.

Definition trace_prefix (tr: Trace) (tr': Trace) : Prop :=
  prefix tr tr'.

Lemma ExternalOp_fill_inv K o e1 e2:
  ExternalOp o e1 = fill K e2 →
  (ExternalOp o e1 = e2 ∨ ∃ K1 K2, K = K1 ++ K2 ∧ e1 = fill K1 e2).
Proof.
  revert o e1 e2.
  induction K => o e1 e2.
  - eauto.
  - intros [Heq|Happ]%IHK.
    * destruct a; simpl in Heq; try congruence.
      inversion Heq; subst. right.
      exists [], (ExternalOpCtx op :: K) => //=.
    * destruct Happ as (K1&K2&->&Heq).
      right. exists (a :: K1), K2; eauto.
Qed.

Lemma ExternalOp_fill_item_inv Ki o e1 e2:
  ExternalOp o e1 = fill_item Ki e2 →
  e1 = e2.
Proof. destruct Ki => //=; congruence. Qed.

Lemma Panic_fill_item_inv Ki msg e:
  Primitive0 (PanicOp msg) = fill_item Ki e →
  False.
Proof. destruct Ki => //=. Qed.

Lemma Var_fill_item_inv Ki x e:
  Var x = fill_item Ki e →
  False.
Proof. destruct Ki => //=. Qed.

Lemma ExternalOp_sub_redexes o e:
  is_Some (to_val e) →
  sub_redexes_are_values (ExternalOp o e).
Proof.
  intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
  apply ExternalOp_fill_item_inv in Heq; subst; auto.
Qed.

Lemma Var_sub_redexes x:
  sub_redexes_are_values (Var x).
Proof.
  intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
  apply Var_fill_item_inv in Heq; subst; auto.
  exfalso; eauto.
Qed.

Lemma stuck_ExternalOp' σ g o e:
  is_Some (to_val e) →
  base_irreducible' (ExternalOp o e) σ g →
  stuck' (ExternalOp o e) σ g.
Proof.
  intros Hval Hirred. split; first done.
  apply prim_base_irreducible'; auto. apply ExternalOp_sub_redexes; eauto.
Qed.

Lemma stuck_Var σ g x :
  stuck (Var x) σ g.
Proof.
  split; first done.
  apply prim_base_irreducible; auto.
  { inversion 1. inversion H0; eauto. }
  { apply Var_sub_redexes; eauto. }
Qed.

Lemma stuck_ExternalOp σ g o e:
  is_Some (to_val e) →
  base_irreducible (ExternalOp o e) σ g →
  stuck (ExternalOp o e) σ g.
Proof.
  intros Hval Hirred. split; first done.
  apply prim_base_irreducible; auto. apply ExternalOp_sub_redexes; eauto.
Qed.

Lemma stuck_Panic' σ g msg:
  stuck' (Primitive0 (PanicOp msg)) σ g.
Proof.
  split; first done.
  apply prim_base_irreducible'; auto.
  * inversion 1; subst; eauto.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    apply Panic_fill_item_inv in Heq; subst; auto; by exfalso.
Qed.

Lemma stuck_Panic σ g msg:
  stuck (Primitive0 (PanicOp msg)) σ g.
Proof.
  split; first done.
  apply prim_base_irreducible; auto.
  * inversion 1; subst; eauto.
    inversion H0; auto.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    apply Panic_fill_item_inv in Heq; subst; auto; by exfalso.
Qed.

Lemma atomically_not_stuck_body_safe (l: val) e σ g :
  ¬ stuck (Atomically (of_val l) e) σ g →
  prim_step'_safe e σ g.
Proof.
  intros Hnstuck ??? Hrtc Hstuck.
  apply Hnstuck.
  split; first done.
  apply prim_base_irreducible; last first.
  { intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e0' Heq.
    assert (of_val l = e0').
    { move: Heq. destruct Ki => //=; congruence. }
    naive_solver.
  }
  intros ????? Hstep.
  inversion Hstep; subst.
  * inversion H; eauto.
  * match goal with
    | [ H: prim_step'_safe _ _ _ |- _ ] => eapply H
    end; try eapply Hrtc; eauto.
  * match goal with
    | [ H: prim_step'_safe _ _ _ |- _ ] => eapply H
    end; eauto.
Qed.

Definition null_non_alloc {V} (h : gmap loc V) :=
  ∀ off, h !! (addr_plus_off null off) = None.

Definition neg_non_alloc {V} (h : gmap loc V) :=
  ∀ l, is_Some (h !! l) → 0 < loc_car l.

Lemma fresh_alloc_equiv_null_non_alloc σ v:
  null_non_alloc (<[fresh_locs (dom σ.(heap)):=v]> σ.(heap)) ↔
  null_non_alloc (σ.(heap)).
Proof.
  split.
  - rewrite /null_non_alloc => Hn off. etransitivity; last eapply (Hn off).
    rewrite lookup_insert_ne; first done.
    eapply plus_off_preserves_non_null, addr_base_non_null_offset; eauto.
    eapply isFresh_not_null. eapply (fresh_locs_isFresh (_,inhabitant)).
  - rewrite /null_non_alloc => Hn off. etransitivity; last eapply (Hn off).
    rewrite lookup_insert_ne; first done.
    eapply plus_off_preserves_non_null, addr_base_non_null_offset; eauto.
    eapply isFresh_not_null. eapply (fresh_locs_isFresh (_,inhabitant)).
Qed.

Lemma upd_equiv_null_non_alloc σ l v:
  is_Some (heap σ !! l) →
  null_non_alloc (<[l:=v]> σ.(heap)) ↔
  null_non_alloc (σ.(heap)).
Proof.
  intros Hsome.
  split.
  - rewrite /null_non_alloc => Hn off. specialize (Hn off).
    apply lookup_insert_None in Hn as (?&?); eauto.
  - rewrite /null_non_alloc => Hn off.
    apply lookup_insert_None; split; eauto.
    intros Heq. subst. specialize (Hn off). destruct Hsome as (?&?); congruence.
Qed.

End goose.

Notation LetCtx x e2 := (AppRCtx (LamV x e2)) (only parsing).
Notation SeqCtx e2 := (LetCtx BAnon e2) (only parsing).
