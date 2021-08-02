From Coq Require Import Program.Equality.
From RecordUpdate Require Import RecordSet.
From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From Perennial.program_logic Require Export language ectx_language ectxi_language.
From Perennial.Helpers Require Import CountableTactics.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_logic Require Export crash_lang.
From Perennial.goose_lang Require Export locations.
From Perennial Require Export Helpers.Integers.
Set Default Proof Using "Type".

(** GooseLang, an adaptation of HeapLang with extensions to model Go, including
support for a customizable "FFI" (foreign-function interface) for new primitive
operations and crash semantics for foreign operations. See goose_lang/ffi/disk.v
for our main FFI example.

- Unlike HeapLang, we keep a left-to-right evaluation order to match Go and
  because curried functions no longer arise.
- Some support for prophecy variables is retained in case we need it later, but we have no way of inserting these from the source code using Goose and haven't developed reasoning principles

*)

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module goose_lang.

(** Expressions and vals. *)
Definition proph_id := positive.

Class ffi_syntax :=
  mkExtOp {
      ffi_opcode: Set;
      ffi_opcode_eq_dec :> EqDecision ffi_opcode;
      ffi_opcode_countable :> Countable ffi_opcode;
      ffi_val: Type;
      ffi_val_eq_dec :> EqDecision ffi_val;
      ffi_val_countable :> Countable ffi_val;
    }.

Class ffi_model :=
  mkFfiModel {
      ffi_state : Type;
      ffi_global_state : Type;
      ffi_state_inhabited :> Inhabited ffi_state;
      ffi_global_state_inhabited :> Inhabited ffi_global_state;
    }.

Section external.

(* these are codes for external operations (which all take a single val as an
   argument and evaluate to a value) and data for external values *)
Context {ext : ffi_syntax}.

(** We have a notion of "poison" as a variant of unit that may not be compared
with anything. This is useful for erasure proofs: if we erased things to unit,
[<erased> == unit] would evaluate to true after erasure, changing program
behavior. So we erase to the poison value instead, making sure that no legal
comparisons could be affected. *)
Inductive base_lit : Type :=
  | LitInt (n : u64) | LitInt32 (n : u32) | LitBool (b : bool) | LitByte (n : u8)
  | LitString (s : string) | LitUnit | LitPoison
  | LitLoc (l : loc) | LitProphecy (p: proph_id).
Inductive un_op : Set :=
  (* TODO: operation to take length of string *)
  | NegOp | MinusUnOp | ToUInt64Op | ToUInt32Op | ToUInt8Op | ToStringOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp (k:Z) (* Pointer offset *)
.

Inductive prim_op0 :=
  (* a stuck expression, to represent undefined behavior *)
| PanicOp (s: string)
  (* non-deterministically pick an integer *)
| ArbitraryIntOp
.

Inductive prim_op1 :=
  | PrepareWriteOp (* loc *)
  (* non-atomic loads (which conflict with stores) *)
  | StartReadOp (* loc *)
  | FinishReadOp (* loc *)
  (* atomic loads (which still conflict with non-atomic stores) *)
  | LoadOp
  | InputOp
  | OutputOp
.


Inductive prim_op2 :=
 | AllocNOp (* array length (positive number), initial value *)
 | FinishStoreOp (* pointer, value *)
.

Inductive arity : Set := args0 | args1 | args2.
Definition prim_op (ar:arity) : Set :=
  match ar with
  | args0 => prim_op0
  | args1 => prim_op1
  | args2 => prim_op2
  end.

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
  | Resolve (e0 : expr) (e1 : expr) (e2 : expr) (* wrapped expr, proph, val *)
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
.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation Panic s := (Primitive0 (PanicOp s)).
Notation ArbitraryInt := (Primitive0 ArbitraryIntOp).
Notation AllocN := (Primitive2 AllocNOp).
Notation PrepareWrite := (Primitive1 PrepareWriteOp).
Notation FinishStore := (Primitive2 FinishStoreOp).
Notation StartRead := (Primitive1 StartReadOp).
Notation FinishRead := (Primitive1 FinishReadOp).
Notation Load := (Primitive1 LoadOp).
Notation Input := (Primitive1 InputOp).
Notation Output := (Primitive1 OutputOp).

Fixpoint flatten_struct (v: val) : list val :=
  match v with
  | PairV v1 v2 => flatten_struct v1 ++ flatten_struct v2
  | LitV LitUnit => []
  | _ => [v]
  end.

Context {ffi : ffi_model}.

Inductive naMode :=
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

(** The state: heaps of vals. *)
Record state : Type := {
  heap: gmap loc (nonAtomic val);
  world: ffi_state;
  trace: Trace;
  oracle: Oracle;
}.
Definition global_state : Type := ffi_global_state.

Global Instance eta_state : Settable _ := settable! Build_state <heap; world; trace; oracle>.

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
    ffi_step : ffi_opcode -> val -> transition (state*global_state) val;
    ffi_crash_step : ffi_state -> ffi_state -> Prop;
  }.
Context {ffi_semantics: ffi_semantics}.

Inductive goose_crash : state -> state -> Prop :=
  | GooseCrash σ w w' :
     w = σ.(world) ->
     ffi_crash_step w w' ->
     goose_crash σ (set trace add_crash (set world (fun _ => w') (set heap (fun _ => ∅) σ)))
.


(** An observation associates a prophecy variable (identifier) to a pair of
values. The first value is the one that was returned by the (atomic) operation
during which the prophecy resolution happened (typically, a boolean when the
wrapped operation is a CmpXchg). The second value is the one that the prophecy
variable was actually resolved to. *)
Definition observation : Type := proph_id * (val * val).

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

(** We assume the following encoding of values to 64-bit words: The least 3
significant bits of every word are a "tag", and we have 61 bits of payload,
which is enough if all pointers are 8-byte-aligned (common on 64bit
architectures). The tags have the following meaning:

0: Payload is the data for a LitV (LitInt _).
1: Payload is the data for a InjLV (LitV (LitInt _)).
2: Payload is the data for a InjRV (LitV (LitInt _)).
3: Payload is the data for a LitV (LitLoc _).
4: Payload is the data for a InjLV (LitV (LitLoc _)).
4: Payload is the data for a InjRV (LitV (LitLoc _)).
6: Payload is one of the following finitely many values, which 61 bits are more
   than enough to encode:
   LitV LitUnit, InjLV (LitV LitUnit), InjRV (LitV LitUnit),
   LitV (LitBool _), InjLV (LitV (LitBool _)), InjRV (LitV (LitBool _)).
7: Value is boxed, i.e., payload is a pointer to some read-only memory area on
   the heap which stores whether this is a RecV, PairV, InjLV or InjRV and the
   relevant data for those cases. However, the boxed representation is never
   used if any of the above representations could be used.

Ignoring (as usual) the fact that we have to fit the infinite Z/loc into 61
bits, this means every value is machine-word-sized and can hence be atomically
read and written.  Also notice that the sets of boxed and unboxed values are
disjoint. *)
Definition lit_is_unboxed (l: base_lit) : Prop :=
  match l with
  (** Disallow comparing (erased) prophecies with (erased) prophecies, by
  considering them boxed. *)
  | LitProphecy _ | LitPoison => False
  | _ => True
  end.
Definition val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV l => lit_is_unboxed l
  | InjLV (LitV l) => lit_is_unboxed l
  | InjRV (LitV l) => lit_is_unboxed l
  | _ => False
  end.

Global Instance lit_is_unboxed_dec l : Decision (lit_is_unboxed l).
Proof. destruct l; simpl; exact (decide _). Defined.
Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
Proof. destruct v as [ | | | [] | [] | ]; simpl; exact (decide _). Defined.

(** We just compare the word-sized representation of two values, without looking
into boxed data.  This works out fine if at least one of the to-be-compared
values is unboxed (exploiting the fact that an unboxed and a boxed value can
never be equal because these are disjoint sets). *)
Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Global Arguments vals_compare_safe !_ !_ /.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. refine (
           fun e1 e2 =>
             match e1, e2 with
             | LitInt x, LitInt x' => cast_if (decide (x = x'))
             | LitInt32 x, LitInt32 x' => cast_if (decide (x = x'))
             | LitBool x, LitBool x' => cast_if (decide (x = x'))
             | LitByte x, LitByte x' => cast_if (decide (x = x'))
             | LitString x, LitString x' => cast_if (decide (x = x'))
             | LitUnit, LitUnit => left _
             | LitPoison, LitPoison => left _
             | LitLoc l, LitLoc l' => cast_if (decide (l = l'))
             | LitProphecy i, LitProphecy i' => cast_if (decide (i = i'))
             | _ , _ => right _
             end); abstract intuition congruence.
Defined.
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
Global Instance expr_eq_dec : EqDecision expr.
Proof using ext.
  clear ffi_semantics ffi.
  refine (
      fix go (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
      match e1, e2 with
      | Val v, Val v' => cast_if (decide (v = v'))
      | Var x, Var x' => cast_if (decide (x = x'))
      | Rec f x e, Rec f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
      | App e1 e2, App e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | Primitive0 op, Primitive0 op' => cast_if (decide (op = op'))
      | Primitive1 op e, Primitive1 op' e' =>
        cast_if_and (decide (op = op')) (decide (e = e'))
      | Primitive2 op e1 e2, Primitive2 op' e1' e2' =>
        cast_if_and3 (decide (op = op')) (decide (e1 = e1')) (decide (e2 = e2'))
      (* | Primitive3 op e0 e1 e2, Primitive3 op' e0' e1' e2' =>
        cast_if_and4 (decide (op = op')) (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2')) *)
      | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
      | BinOp o e1 e2, BinOp o' e1' e2' =>
        cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
      | If e0 e1 e2, If e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
      | Pair e1 e2, Pair e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | Fst e, Fst e' => cast_if (decide (e = e'))
      | Snd e, Snd e' => cast_if (decide (e = e'))
      | InjL e, InjL e' => cast_if (decide (e = e'))
      | InjR e, InjR e' => cast_if (decide (e = e'))
      | Case e0 e1 e2, Case e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
      | Fork e, Fork e' => cast_if (decide (e = e'))
      | Atomically el e, Atomically el' e' => cast_if_and (decide (el = el')) (decide (e = e'))
      | ExternalOp op e, ExternalOp op' e' => cast_if_and (decide (op = op')) (decide (e = e'))
      | CmpXchg e0 e1 e2, CmpXchg e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
      | NewProph, NewProph => left _
      | Resolve e0 e1 e2, Resolve e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
      | _, _ => right _
      end
          with gov (v1 v2 : val) {struct v1} : Decision (v1 = v2) :=
      match v1, v2 with
      | LitV l, LitV l' => cast_if (decide (l = l'))
      | RecV f x e, RecV f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
      | PairV e1 e2, PairV e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | InjLV e, InjLV e' => cast_if (decide (e = e'))
      | InjRV e, InjRV e' => cast_if (decide (e = e'))
      | ExtV ev, ExtV ev' => cast_if (decide (ev = ev'))
      | _, _ => right _
      end
        for go); try (clear go gov; abstract intuition congruence).
Defined.
Global Instance val_eq_dec : EqDecision val.
Proof using ext.
  clear ffi_semantics ffi.
  refine
    (fix go (v1 v2:val) : Decision (v1 = v2) :=
     match v1, v2 with
     | LitV l, LitV l' => cast_if (decide (l = l'))
     | RecV f x e, RecV f' x' e' =>
       cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | PairV e1 e2, PairV e1' e2' =>
       cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | InjLV e, InjLV e' => cast_if (decide (e = e'))
     | InjRV e, InjRV e' => cast_if (decide (e = e'))
      | ExtV ev, ExtV ev' => cast_if (decide (ev = ev'))
     | _, _ => right _
     end); try abstract intuition congruence.
Defined.

Definition enc_base_lit :=
(λ l, match l with
  | LitInt n => (inl (inl (inl (inl n))), None)
  | LitInt32 n => (inl (inl (inl (inr n))), None)
  | LitByte n => (inl (inl (inr n)), None)
  | LitBool b => (inl (inr b), None)
  | LitUnit => (inr (inl false), None)
  | LitString s => (inr (inr (inr s)), None)
  | LitPoison => (inr (inl true), None)
  | LitLoc l => (inr (inr (inl l)), None)
  | LitProphecy p => (inr (inl false), Some p)
  end).

Definition dec_base_lit :=
(λ l, match l with
  | (inl (inl (inl (inl n))), None) => LitInt n
  | (inl (inl (inl (inr n))), None) => LitInt32 n
  | (inl (inl (inr n)), None) => LitByte n
  | (inl (inr b), None) => LitBool b
  | (inr (inl false), None) => LitUnit
  | (inr (inr (inr s)), None) => LitString s
  | (inr (inl true), None) => LitPoison
  | (inr (inr (inl l)), None) => LitLoc l
  | (_, Some p) => LitProphecy p
  end).

Definition base_lit_enc_retract : forall l, dec_base_lit (enc_base_lit l) = l.
Proof.
  by intros [].
Qed.

Global Instance base_lit_countable : Countable base_lit :=
  inj_countable' enc_base_lit dec_base_lit base_lit_enc_retract.

Global Instance un_op_finite : Countable un_op.
Proof.
  solve_countable un_op_rec 15%nat.
Qed.

Global Instance bin_op_countable : Countable bin_op.
Proof.
  refine (inj_countable' (λ op, match op with
                                | PlusOp => inl 0
                                | MinusOp => inl 1
                                | MultOp => inl 2
                                | QuotOp => inl 3
                                | RemOp => inl 4
                                | AndOp => inl 5
                                | OrOp => inl 6
                                | XorOp => inl 7
                                | ShiftLOp => inl 8
                                | ShiftROp => inl 9
                                | LeOp => inl 10
                                | LtOp => inl 11
                                | EqOp => inl 12
                                | OffsetOp k => inr k
                                end)
                         (λ x, match x with
                               | inl 0 => _
                               | inl 1 => _
                               | inl 2 => _
                               | inl 3 => _
                               | inl 4 => _
                               | inl 5 => _
                               | inl 6 => _
                               | inl 7 => _
                               | inl 8 => _
                               | inl 9 => _
                               | inl 10 => _
                               | inl 11 => _
                               | inl 12 => _
                               | inl _ => PlusOp
                               | inr k => OffsetOp k
                               end) _); by intros [].
Qed.

Instance prim_op0_countable : Countable prim_op0.
Proof.
  refine (inj_countable' (fun op => match op with
                                    | PanicOp s => Some s
                                    | ArbitraryIntOp => None
                                    end)
         (fun v => match v with
                   | Some s => PanicOp s
                   | None => ArbitraryIntOp
                   end) _); by intros [].
Qed.

Instance prim_op1_countable : Countable prim_op1.
Proof. solve_countable prim_op1_rec 7%nat. Qed.

Instance prim_op2_countable : Countable prim_op2.
Proof. solve_countable prim_op2_rec 4%nat. Qed.

Definition prim_op' : Set := prim_op0 + prim_op1 + prim_op2.

Definition a_prim_op {ar} (op: prim_op ar) : prim_op'.
  rewrite /prim_op'.
  destruct ar; simpl in op; eauto.
Defined.

(** For the proof of [Countable expr], we encode [expr] as a [genTree] with some
countable type at the leaves. [basic_type] is what we use as that leaf type. *)
Inductive basic_type :=
  | stringVal (s:string)
  | binderVal (b:binder)
  | intVal (z:u64)
  | litVal (l: base_lit)
  | un_opVal (op:un_op)
  | bin_opVal (op:bin_op)
  | primOpVal (op:prim_op')
  | externOp (op:ffi_opcode)
  | externVal (ev:ffi_val)
.

Instance basic_type_eq_dec : EqDecision basic_type.
Proof. solve_decision. Defined.
Instance basic_type_countable : Countable basic_type.
Proof.
  refine (inj_countable' (λ x, match x with
                              | stringVal s => inl s
                              | binderVal b => inr (inl b)
                              | intVal z => inr (inr (inl z))
                              | litVal l => inr (inr (inr (inl l)))
                              | un_opVal op => inr (inr (inr (inr (inl op))))
                              | bin_opVal op => inr (inr (inr (inr (inr (inl op)))))
                              | primOpVal op => inr (inr (inr (inr (inr (inr (inl op))))))
                              | externOp op => inr (inr (inr (inr (inr (inr (inr (inl op)))))))
                              | externVal k => inr (inr (inr (inr (inr (inr (inr (inr k)))))))
                              end)
                         (λ x, match x with
                              | inl s => stringVal s
                              | inr (inl b) => binderVal b
                              | inr (inr (inl z)) => intVal z
                              | inr (inr (inr (inl l))) => litVal l
                              | inr (inr (inr (inr (inl op)))) => un_opVal op
                              | inr (inr (inr (inr (inr (inl op))))) => bin_opVal op
                              | inr (inr (inr (inr (inr (inr (inl op)))))) => primOpVal op
                              | inr (inr (inr (inr (inr (inr (inr (inl op))))))) => externOp op
                              | inr (inr (inr (inr (inr (inr (inr (inr k))))))) => externVal k
                               end) _); by intros [].
Qed.

Definition to_prim_op : {f: forall ar (op: prim_op'), prim_op ar |
                         forall ar op, f ar (a_prim_op op) = op}.
  unshelve refine (exist _ (fun ar op => _) _);
    [ (* partially construct f as a match statement *)
      destruct ar; destruct op as [[|]|] |
      (* solve equality cases by unification *)
      destruct ar, op; simpl; eauto
    ];
    (* solve default cases with an arbitrary value *)
    solve [ constructor; auto using "" ]
  .
(* intentionally opaque since the type signature gives the only needed
correctness condition *)
Qed.

Definition to_prim_op_correct := proj2_sig to_prim_op.

Global Instance expr_countable : Countable expr.
Proof using ext.
  clear ffi_semantics ffi.
 set (enc :=
   fix go e :=
     match e with
     | Val v => GenNode 0 [gov v]
     | Var x => GenLeaf (stringVal x)
     | Rec f x e => GenNode 1 [GenLeaf $ binderVal f; GenLeaf $ binderVal x; go e]
     | App e1 e2 => GenNode 2 [go e1; go e2]
     | Primitive0 op => GenNode 21 [GenLeaf $ primOpVal $ a_prim_op op]
     | Primitive1 op e => GenNode 22 [GenLeaf $ primOpVal $ a_prim_op op; go e]
     | Primitive2 op e1 e2 => GenNode 23 [GenLeaf $ primOpVal $ a_prim_op op; go e1; go e2]
     (* | Primitive3 op e0 e1 e2 => GenNode 24 [GenLeaf $ primOpVal $ a_prim_op op; go e0; go e1; go e2] *)
     | UnOp op e => GenNode 3 [GenLeaf $ un_opVal op; go e]
     | BinOp op e1 e2 => GenNode 4 [GenLeaf $ bin_opVal op; go e1; go e2]
     | If e0 e1 e2 => GenNode 5 [go e0; go e1; go e2]
     | Pair e1 e2 => GenNode 6 [go e1; go e2]
     | Fst e => GenNode 7 [go e]
     | Snd e => GenNode 8 [go e]
     | InjL e => GenNode 9 [go e]
     | InjR e => GenNode 10 [go e]
     | Case e0 e1 e2 => GenNode 11 [go e0; go e1; go e2]
     | Fork e => GenNode 12 [go e]
     | Atomically el e => GenNode 13 [go el; go e]
     | ExternalOp op e => GenNode 20 [GenLeaf $ externOp op; go e]
     | CmpXchg e0 e1 e2 => GenNode 16 [go e0; go e1; go e2]
     | NewProph => GenNode 18 []
     | Resolve e0 e1 e2 => GenNode 19 [go e0; go e1; go e2]
     end
   with gov v :=
     match v with
     | LitV l => GenLeaf $ litVal l
     | RecV f x e =>
        GenNode 0 [GenLeaf $ binderVal f; GenLeaf $ binderVal x; go e]
     | PairV v1 v2 => GenNode 1 [gov v1; gov v2]
     | InjLV v => GenNode 2 [gov v]
     | InjRV v => GenNode 3 [gov v]
     | ExtV ev => GenNode 4 [GenLeaf $ externVal ev]
     end
   for go).
 set (dec :=
   fix go e :=
     match e with
     | GenNode 0 [v] => Val (gov v)
     | GenLeaf (stringVal x) => Var x
     | GenNode 1 [GenLeaf (binderVal f); GenLeaf (binderVal x); e] => Rec f x (go e)
     | GenNode 2 [e1; e2] => App (go e1) (go e2)
     | GenNode 21 [GenLeaf (primOpVal op)] => Primitive0 (`to_prim_op args0 op)
     | GenNode 22 [GenLeaf (primOpVal op); e] => Primitive1 (`to_prim_op args1 op) (go e)
     | GenNode 23 [GenLeaf (primOpVal op); e1; e2] => Primitive2 (`to_prim_op args2 op) (go e1) (go e2)
     (* | GenNode 24 [GenLeaf (primOpVal op); e0; e1; e2] => Primitive3 (`to_prim_op args3 op) (go e0) (go e1) (go e2) *)
     | GenNode 3 [GenLeaf (un_opVal op); e] => UnOp op (go e)
     | GenNode 4 [GenLeaf (bin_opVal op); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 5 [e0; e1; e2] => If (go e0) (go e1) (go e2)
     | GenNode 6 [e1; e2] => Pair (go e1) (go e2)
     | GenNode 7 [e] => Fst (go e)
     | GenNode 8 [e] => Snd (go e)
     | GenNode 9 [e] => InjL (go e)
     | GenNode 10 [e] => InjR (go e)
     | GenNode 11 [e0; e1; e2] => Case (go e0) (go e1) (go e2)
     | GenNode 12 [e] => Fork (go e)
     | GenNode 13 [el; e] => Atomically (go el) (go e)
     | GenNode 20 [GenLeaf (externOp op); e] => ExternalOp op (go e)
     | GenNode 16 [e0; e1; e2] => CmpXchg (go e0) (go e1) (go e2)
     | GenNode 18 [] => NewProph
     | GenNode 19 [e0; e1; e2] => Resolve (go e0) (go e1) (go e2)
     | _ => Val $ LitV LitUnit (* dummy *)
     end
   with gov v :=
     match v with
     | GenLeaf (litVal l) => LitV l
     | GenNode 0 [GenLeaf (binderVal f); GenLeaf (binderVal x); e] => RecV f x (go e)
     | GenNode 1 [v1; v2] => PairV (gov v1) (gov v2)
     | GenNode 2 [v] => InjLV (gov v)
     | GenNode 3 [v] => InjRV (gov v)
     | GenNode 4 [GenLeaf (externVal ev)] => ExtV ev
     | _ => LitV LitUnit (* dummy *)
     end
   for go).
 refine (inj_countable' enc dec _).
 refine (fix go (e : expr) {struct e} := _ with gov (v : val) {struct v} := _ for go).
  - destruct e as [v| | | | | | | | | | | | | | | | | | | | |]; simpl; f_equal;
      rewrite ?to_prim_op_correct;
      [exact (gov v)|done..].
 - destruct v; by f_equal.
Qed.
Global Instance val_countable : Countable val.
Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

Global Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant; world := inhabitant; trace := inhabitant; oracle := inhabitant; |}.
Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

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
  | ResolveLCtx (ctx : ectx_item) (v1 : val) (v2 : val)
  | ResolveMCtx (e0 : expr) (v2 : val)
  | ResolveRCtx (e0 : expr) (e1 : expr)
  | AtomicallyCtx (e0 : expr).

(** Contextual closure will only reduce [e] in [Resolve e (Val _) (Val _)] if
the local context of [e] is non-empty. As a consequence, the first argument of
[Resolve] is not completely evaluated (down to a value) by contextual closure:
no head steps (i.e., surface reductions) are taken. This means that contextual
closure will reduce [Resolve (CmpXchg #l #n (#n + #1)) #p #v] into [Resolve
(CmpXchg #l #n #(n+1)) #p #v], but it cannot context-step any further. *)

Fixpoint fill_item (Ki : ectx_item) (e : expr) : expr :=
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
  (* | Primitive3LCtx op e1 e2 => Primitive3 op e e1 e2
  | Primitive3MCtx op v0 e1 => Primitive3 op (Val v0) e e1
  | Primitive3RCtx op v0 v1 => Primitive3 op (Val v0) (Val v1) e *)
  | ExternalOpCtx op => ExternalOp op e
  | CmpXchgLCtx e1 e2 => CmpXchg e e1 e2
  | CmpXchgMCtx v0 e2 => CmpXchg (Val v0) e e2
  | CmpXchgRCtx v0 v1 => CmpXchg (Val v0) (Val v1) e
  | ResolveLCtx K v1 v2 => Resolve (fill_item K e) (Val v1) (Val v2)
  | ResolveMCtx ex v2 => Resolve ex e (Val v2)
  | ResolveRCtx ex e1 => Resolve ex e1 e
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
  | Resolve ex e1 e2 => Resolve (subst x v ex) (subst x v e1) (subst x v e2)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (word.not n)
  | NegOp, LitV (LitInt32 n) => Some $ LitV $ LitInt32 (word.not n)
  | NegOp, LitV (LitByte n) => Some $ LitV $ LitByte (word.not n)
  | ToUInt64Op, LitV (LitInt v) => Some $ LitV $ LitInt v
  | ToUInt64Op, LitV (LitInt32 v) => Some $ LitV $ LitInt (u32_to_u64 v)
  | ToUInt64Op, LitV (LitByte v) => Some $ LitV $ LitInt (u8_to_u64 v)
  | ToUInt32Op, LitV (LitInt v) => Some $ LitV $ LitInt32 (u32_from_u64 v)
  | ToUInt32Op, LitV (LitInt32 v) => Some $ LitV $ LitInt32 v
  | ToUInt32Op, LitV (LitByte v) => Some $ LitV $ LitInt32 (u8_to_u32 v)
  | ToUInt8Op, LitV (LitInt v) => Some $ LitV $ LitByte (u8_from_u64 v)
  | ToUInt8Op, LitV (LitInt32 v) => Some $ LitV $ LitByte (u8_from_u32 v)
  | ToUInt8Op, LitV (LitByte v) => Some $ LitV $ LitByte v
  | ToStringOp, LitV (LitByte v) => Some $ LitV $ LitString (u8_to_string v)
  | _, _ => None
  end.

Definition bin_op_eval_word (op : bin_op) {width} {word: Interface.word width} (n1 n2 : word) : option word :=
  match op with
  | PlusOp => Some $ word.add (word:=word) n1 n2
  | MinusOp => Some $ word.sub (word:=word) n1 n2
  | MultOp => Some $ (word.mul (word:=word) n1 n2)
  | QuotOp => Some $ (word.divu (word:=word) n1 n2)
  | RemOp => Some $ (word.modu (word:=word) n1 n2)
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

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  | OffsetOp _ => None (* Pointer arithmetic *)
  end.

Definition bin_op_eval_string (op : bin_op) (s1 s2 : string) : option base_lit :=
  match op with
  | PlusOp => Some $ LitString (s1 ++ s2)
  | _ => None
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    Some $ LitV $ LitBool $ bool_decide (v1 = v2)
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) =>
      LitV <$> ((LitInt <$> bin_op_eval_word op n1 n2)
                  ∪ (LitBool <$> bin_op_eval_compare op n1 n2))
    | LitV (LitInt32 n1), LitV (LitInt32 n2) =>
      LitV <$> ((LitInt32 <$> bin_op_eval_word op n1 n2)
                  ∪ (LitBool <$> bin_op_eval_compare op n1 n2))
    | LitV (LitByte n1), LitV (LitByte n2) =>
      LitV <$> ((LitByte <$> bin_op_eval_word op n1 n2)
                  ∪ (LitBool <$> bin_op_eval_compare op n1 n2))

    (* Shifts do not require matching bit width *)
    | LitV (LitByte n1), LitV (LitInt n2) =>
      LitV <$> (LitByte <$> bin_op_eval_shift op n1 (u8_from_u64 n2))
    | LitV (LitByte n1), LitV (LitInt32 n2) =>
      LitV <$> (LitByte <$> bin_op_eval_shift op n1 (u8_from_u32 n2))
    | LitV (LitInt32 n1), LitV (LitInt n2) =>
      LitV <$> (LitInt32 <$> bin_op_eval_shift op n1 (u32_from_u64 n2))
    | LitV (LitInt32 n1), LitV (LitByte n2) =>
      LitV <$> (LitInt32 <$> bin_op_eval_shift op n1 (u8_to_u32 n2))
    | LitV (LitInt n1), LitV (LitByte n2) =>
      LitV <$> (LitInt <$> bin_op_eval_shift op n1 (u8_to_u64 n2))
    | LitV (LitInt n1), LitV (LitInt32 n2) =>
      LitV <$> (LitInt <$> bin_op_eval_shift op n1 (u32_to_u64 n2))

    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitString s1), LitV (LitString s2) => LitV <$> bin_op_eval_string op s1 s2
    | LitV (LitLoc l), LitV (LitInt off) => match op with
                                           | OffsetOp k =>
                                             Some $ LitV $ LitLoc (l +ₗ k * (int.Z (off: u64)))
                                           | _ => None
                                           end
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
  isFresh σg (fresh_locs (dom (gset loc) σg.1.(heap))).
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
  refine (exist _ (fresh_locs (dom (gset loc) σg.1.(heap))) _).
  by apply fresh_locs_isFresh.
Defined.

Global Instance alloc_gen : GenPred loc (state*global_state) (isFresh) :=
  fun _ σ => Some (gen_isFresh σ).

(** Generate a location for a fresh block; doesn't actually insert anything into
the heap. *)
Definition allocateN : transition (state*global_state) loc :=
  suchThat (isFresh).

(*
Global Instance newProphId_gen: GenPred proph_id (state*global_state) (fun '(σ,g) p => p ∉ σ.(used_proph_id)).
Proof.
  refine (fun _ '(σ,g) => Some (exist _ (fresh σ.(used_proph_id)) _)).
  apply is_fresh.
Defined.

Definition newProphId: transition (state*global_state) proph_id :=
  suchThat (fun '(σ,g) p => p ∉ σ.(used_proph_id)).
*)

Instance gen_anyInt Σ: GenPred u64 Σ (fun _ _ => True).
  refine (fun z _ => Some (U64 z ↾ _)); auto.
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

Definition head_trans (e: expr) :
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
      (check (0 < int.Z n)%Z;;
       l ← allocateN;
       modifyσ (state_init_heap l (int.Z n) v);;
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
  | ExternalOp op (Val v) => atomically $ ffi_step op v
  | Input (Val (LitV (LitInt selv))) =>
    atomically
      (x ← reads (λ '(σ,g), σ.(oracle) σ.(trace) selv);
      modifyσ (set trace (add_event (In_ev (LitInt selv) (LitInt x))));;
      ret $ LitV $ LitInt $ x)
  | Output (Val (LitV v)) =>
    atomically
      (modifyσ (set trace (add_event (Out_ev v)));;
       ret $ LitV $ LitUnit)
  | CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2) =>
    atomically
      (nav ← reads (λ '(σ,g), σ.(heap) !! l) ≫= unwrap;
      match nav with
      | (Reading n, vl) =>
        check (vals_compare_safe vl v1);;
        when (vl = v1) (check (n = 0%nat);; modifyσ (set heap <[l:=Free v2]>));;
        ret $ PairV vl (LitV $ LitBool (bool_decide (vl = v1)))
      | _ => undefined
      end)
  | _ => undefined
  end.

Definition head_step:
    expr -> state -> global_state -> list observation -> expr -> state -> global_state -> list expr -> Prop :=
  fun e s g κs e' s' g' efs =>
      relation.denote (head_trans e) (s,g) (s',g') (κs, e', efs).

Definition fill' (K : list (ectx_item)) (e : expr) : expr := foldl (flip fill_item) e K.

Inductive prim_step' (e1 : expr) (σ1 : state) (g1 : global_state) (κ : list (observation))
    (e2 : expr) (σ2 : state) (g2 : global_state) (efs : list (expr)) : Prop :=
  Ectx_step' K e1' e2' :
    e1 = fill' K e1' → e2 = fill' K e2' →
    head_step e1' σ1 g1 κ e2' σ2 g2 efs → prim_step' e1 σ1 g1 κ e2 σ2 g2 efs.

Definition irreducible' (e : expr) (σ : state) (g : global_state) :=
  ∀ κ e' σ' g' efs, ¬prim_step' e σ g κ e' σ' g' efs.
Definition stuck' (e : expr) (σ : state) (g : global_state) :=
  to_val e = None ∧ irreducible' e σ g.

Definition prim_step'_safe e s g :=
  (∀ e' s' g', rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' []) (e, (s, g)) (e', (s', g')) →
            ¬ stuck' e' s' g').

Inductive head_step_atomic:
    expr -> state -> global_state -> list observation -> expr -> state -> global_state -> list expr -> Prop :=
 | head_step_trans : ∀ e s g κs e' s' g' efs,
     head_step e s g κs e' s' g' efs →
     head_step_atomic e s g κs e' s' g' efs
 | head_step_atomically : ∀ (vl : val) e s g κs v' s' g',
     rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' []) (e, (s, g)) (Val (InjRV v'), (s', g')) →
     prim_step'_safe e s g →
     head_step_atomic (Atomically (of_val vl) e) s g κs (Val (InjRV v')) s' g' []
 | head_step_atomically_fail : ∀ vl e s g κs,
     (* An atomically block can non-deterministically fail _ONLY_ if the block would not trigger UB *)
     prim_step'_safe e s g →
     head_step_atomic (Atomically (of_val vl) e) s g κs (Val (InjLV (LitV LitUnit))) s g []
.

Lemma head_step_atomic_inv e s g κs e' s' g' efs :
  head_step_atomic e s g κs e' s' g' efs →
  (∀ el e'', e ≠ Atomically el e'') →
  head_step e s g κs e' s' g' efs.
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

Lemma val_head_stuck e1 σ1 g1 κ e2 σ2 g2 efs :
  head_step e1 σ1 g1 κ e2 σ2 g2 efs → to_val e1 = None.
Proof.
  rewrite /head_step; intros.
  destruct e1; auto; simpl.
  exfalso.
  simpl in H; eapply suchThat_false; eauto.
Qed.

Lemma val_head_atomic_stuck e1 σ1 g1 κ e2 σ2 g2 efs :
  head_step_atomic e1 σ1 g1 κ e2 σ2 g2 efs → to_val e1 = None.
Proof.
  inversion 1; subst; eauto using val_head_stuck.
Qed.


Ltac inv_undefined :=
  match goal with
  | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] =>
    destruct e; try (apply suchThat_false in H; contradiction)
  end.

Lemma head_ctx_step_val Ki e σ1 g1 κ e2 σ2 g2 efs :
  head_step (fill_item Ki e) σ1 g1 κ e2 σ2 g2 efs → is_Some (to_val e).
Proof.
  revert κ e2.
  induction Ki; intros;
    rewrite /head_step /= in H;
    repeat inv_undefined; eauto.
  - inversion H; subst; clear H. done.
  - inversion H; subst; clear H. done.
  - inversion H; subst; clear H. done.
  - inversion H; subst; clear H. exfalso; eauto.
Qed.

Lemma head_ctx_step_atomic_val Ki e σ1 g1 κ e2 σ2 g2 efs :
  head_step_atomic (fill_item Ki e) σ1 g1 κ e2 σ2 g2 efs → is_Some (to_val e).
Proof.
  inversion 1; subst; eauto using head_ctx_step_val.
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
  let l := fresh_locs (dom (gset loc) σ.(heap)) in
  (0 < int.Z n)%Z →
  head_step_atomic (AllocN ((Val $ LitV $ LitInt $ n)) (Val v)) σ g []
            (Val $ LitV $ LitLoc l) (state_init_heap l (int.Z n) v σ) g [].
Proof.
  intros.
  constructor 1.
  rewrite /head_step /=.
  monad_simpl.
  eapply relation.bind_runs with (σ,g) l.
  { econstructor.
    apply fresh_locs_isFresh.
  }
  monad_simpl.
Qed.

Lemma arbitrary_int_step σ g :
  head_step_atomic (ArbitraryInt) σ g []
            (Val $ LitV $ LitInt $ U64 0) σ g [].
Proof.
  intros.
  constructor 1.
  rewrite /head_step /=.
  monad_simpl.
  eapply relation.bind_runs; [ | monad_simpl ].
  constructor; auto.
Qed.

(*
Lemma new_proph_id_fresh σ g :
  let p := fresh σ.(used_proph_id) in
  head_step_atomic NewProph σ g [] (Val $ LitV $ LitProphecy p) (set used_proph_id ({[ p ]} ∪.) σ) g [].
Proof.
  intro p.
  constructor 1.
  rewrite /head_step /=.
  monad_simpl.
  eapply relation.bind_runs with (σ,g) p.
  { econstructor.
    apply is_fresh. }
  monad_simpl.
Qed.
*)

Lemma goose_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step_atomic.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_atomic_stuck,
    fill_item_val, fill_item_val_inv, fill_item_no_val_inj, head_ctx_step_atomic_val.
Qed.

End external.
End goose_lang.

(** Language *)

(* Prefer goose_lang names over ectx_language names. *)
Export goose_lang.

Arguments ffi_semantics ext ffi : clear implicits.
Arguments goose_lang.goose_lang_mixin {ext} {ffi} ffi_semantics.

Section goose.
  Context {ext: ffi_syntax} {ffi: ffi_model}
          {ffi_semantics: ffi_semantics ext ffi}.
  Canonical Structure goose_ectxi_lang := (EctxiLanguage (goose_lang.goose_lang_mixin ffi_semantics)).
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

Lemma prim_step_to_val_is_head_step e σ1 g1 κs w σ2 g2 efs :
  prim_step e σ1 g1 κs (Val w) σ2 g2 efs → head_step_atomic (ffi_semantics:=ffi_semantics) e σ1 g1 κs (Val w) σ2 g2 efs.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some w) as H3; first by rewrite -H2.
  apply to_val_fill_some in H3 as [-> ->]. subst e. done.
Qed.

Lemma head_prim_step_trans e σ g κ e' σ' g' efs :
  head_step e σ g κ e' σ' g' efs →
  ectx_language.prim_step e σ g κ e' σ' g' efs.
Proof.
  intros.
  apply head_prim_step. apply head_step_trans.
  auto.
Qed.

Lemma head_prim_step_trans' e σ g κ e' σ' g' efs :
  head_step e σ g κ e' σ' g' efs →
  prim_step' e σ g κ e' σ' g' efs.
Proof. apply Ectx_step' with empty_ectx; by rewrite ?fill_empty. Qed.

Definition head_reducible' (e : expr) (σ : state) (g : global_state) :=
  ∃ κ e' σ' g' efs, head_step e σ g κ e' σ' g' efs.
Definition head_irreducible' (e : expr) (σ : state) (g : global_state) :=
  ∀ κ e' σ' g' efs, ¬head_step e σ g κ e' σ' g' efs.
Definition reducible' (e : expr) (σ : state) (g : global_state) :=
  ∃ κ e' σ' g' efs, prim_step' e σ g κ e' σ' g' efs.

Lemma prim_head_reducible' e σ g :
  reducible' e σ g → sub_redexes_are_values e → head_reducible' e σ g.
Proof.
  intros (κ&e'&σ'&g'&efs&[K e1' e2' -> -> Hstep]) Hsub.
  assert (K = empty_ectx).
  { apply val_head_stuck in Hstep.
    eapply Hsub; eauto.
  }
  subst. rewrite //= /head_reducible. econstructor; eauto.
Qed.

Lemma not_reducible' e σ g : ¬reducible' e σ g ↔ irreducible' e σ g.
Proof. unfold reducible', irreducible'. naive_solver. Qed.
Lemma not_head_reducible' e σ g : ¬head_reducible' e σ g ↔ head_irreducible' e σ g.
Proof. unfold head_reducible', head_irreducible'. naive_solver. Qed.

Lemma prim_head_irreducible' e σ g :
  head_irreducible' e σ g → sub_redexes_are_values e → irreducible' e σ g.
Proof.
  rewrite -not_reducible' -not_head_reducible'; eauto using prim_head_reducible'.
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

Lemma ExternalOp_sub_redexes o e:
  is_Some (to_val e) →
  sub_redexes_are_values (ExternalOp o e).
Proof.
  intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
  apply ExternalOp_fill_item_inv in Heq; subst; auto.
Qed.

Lemma stuck_ExternalOp' σ g o e:
  is_Some (to_val e) →
  head_irreducible' (ExternalOp o e) σ g →
  stuck' (ExternalOp o e) σ g.
Proof.
  intros Hval Hirred. split; first done.
  apply prim_head_irreducible'; auto. apply ExternalOp_sub_redexes; eauto.
Qed.

Lemma stuck_ExternalOp σ g o e:
  is_Some (to_val e) →
  head_irreducible (ExternalOp o e) σ g →
  stuck (ExternalOp o e) σ g.
Proof.
  intros Hval Hirred. split; first done.
  apply prim_head_irreducible; auto. apply ExternalOp_sub_redexes; eauto.
Qed.

Lemma stuck_Panic' σ g msg:
  stuck' (Primitive0 (PanicOp msg)) σ g.
Proof.
  split; first done.
  apply prim_head_irreducible'; auto.
  * inversion 1; subst; eauto.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    apply Panic_fill_item_inv in Heq; subst; auto; by exfalso.
Qed.

Lemma stuck_Panic σ g msg:
  stuck (Primitive0 (PanicOp msg)) σ g.
Proof.
  split; first done.
  apply prim_head_irreducible; auto.
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
  apply prim_head_irreducible; last first.
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

Lemma fresh_alloc_equiv_null_non_alloc σ v:
  null_non_alloc (<[fresh_locs (dom (gset loc) σ.(heap)):=v]> σ.(heap)) ↔
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

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation Panic s := (Primitive0 (PanicOp s)).
Notation ArbitraryInt := (Primitive0 ArbitraryIntOp).
Notation AllocN := (Primitive2 AllocNOp).
Notation PrepareWrite := (Primitive1 PrepareWriteOp).
Notation FinishStore := (Primitive2 FinishStoreOp).
Notation StartRead := (Primitive1 StartReadOp).
Notation FinishRead := (Primitive1 FinishReadOp).
Notation Load := (Primitive1 LoadOp).
Notation Input := (Primitive1 InputOp).
Notation Output := (Primitive1 OutputOp).
Notation nonAtomic T := (naMode * T)%type.
