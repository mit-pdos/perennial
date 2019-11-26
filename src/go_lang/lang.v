From Coq Require Import Program.Equality.
From RecordUpdate Require Import RecordSet.
From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From Perennial.go_lang Require Export locations.
From Perennial Require Export Helpers.Integers.
Set Default Proof Using "Type".

(** heap_lang.  A fairly simple language used for common Iris examples.

- This is a right-to-left evaluated language, like CakeML and OCaml.  The reason
  for this is that it makes curried functions usable: Given a WP for [f a b], we
  know that any effects [f] might have to not matter until after *both* [a] and
  [b] are evaluated.  With left-to-right evaluation, that triple is basically
  useless unless the user let-expands [b].

- For prophecy variables, we annotate the reduction steps with an "observation"
  and tweak adequacy such that WP knows all future observations. There is
  another possible choice: Use non-deterministic choice when creating a prophecy
  variable ([NewProph]), and when resolving it ([Resolve]) make the
  program diverge unless the variable matches. That, however, requires an
  erasure proof that this endless loop does not make specifications useless.

The expression [Resolve e p v] attaches a prophecy resolution (for prophecy
variable [p] to value [v]) to the top-level head-reduction step of [e]. The
prophecy resolution happens simultaneously with the head-step being taken.
Furthermore, it is required that the head-step produces a value (otherwise
the [Resolve] is stuck), and this value is also attached to the resolution.
A prophecy variable is thus resolved to a pair containing (1) the result
value of the wrapped expression (called [e] above), and (2) the value that
was attached by the [Resolve] (called [v] above). This allows, for example,
to distinguish a resolution originating from a successful [CmpXchg] from one
originating from a failing [CmpXchg]. For example:
 - [Resolve (CmpXchg #l #n #(n+1)) #p v] will behave as [CmpXchg #l #n #(n+1)],
   which means step to a value-boole pair [(n', b)] while updating the heap, but
   in the meantime the prophecy variable [p] will be resolved to [(n', b), v)].
 - [Resolve (! #l) #p v] will behave as [! #l], that is return the value
   [w] pointed to by [l] on the heap (assuming it was allocated properly),
   but it will additionally resolve [p] to the pair [(w,v)].

Note that the sub-expressions of [Resolve e p v] (i.e., [e], [p] and [v])
are reduced as usual, from right to left. However, the evaluation of [e]
is restricted so that the head-step to which the resolution is attached
cannot be taken by the context. For example:
 - [Resolve (CmpXchg #l #n (#n + #1)) #p v] will first be reduced (with by a
   context-step) to [Resolve (CmpXchg #l #n #(n+1) #p v], and then behave as
   described above.
 - However, [Resolve ((λ: "n", CmpXchg #l "n" ("n" + #1)) #n) #p v] is stuck.
   Indeed, it can only be evaluated using a head-step (it is a β-redex),
   but the process does not yield a value.

The mechanism described above supports nesting [Resolve] expressions to
attach several prophecy resolutions to a head-redex. *)

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module heap_lang.

(** Expressions and vals. *)
Definition proph_id := positive.

Class ext_op :=
  mkExtOp {
      external: Set;
      external_eq_dec :> EqDecision external;
      external_countable :> Countable external;
    }.

Class ffi_model :=
  mkFfiModel {
      ffi_state : Type;
      ffi_state_inhabited :> Inhabited ffi_state;
    }.

Section external.

(* these are just codes for external operations (which all take a single val as
   an argument and evaluate to a value) *)
Context {ext : ext_op}.

(** We have a notion of "poison" as a variant of unit that may not be compared
with anything. This is useful for erasure proofs: if we erased things to unit,
[<erased> == unit] would evaluate to true after erasure, changing program
behavior. So we erase to the poison value instead, making sure that no legal
comparisons could be affected. *)
Inductive base_lit : Type :=
  | LitInt (n : u64) | LitInt32 (n : u32) | LitBool (b : bool) | LitByte (n : byte) | LitString (s : string) | LitUnit | LitPoison
  | LitLoc (l : loc) | LitProphecy (p: proph_id).
Inductive un_op : Set :=
  | NegOp | MinusUnOp | ToUInt64Op.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp (* Pointer offset *)
.

Inductive arity : Set := args0 | args1 | args2.

Inductive prim_op : arity -> Set :=
  (* a stuck expression, to represent undefined behavior *)
  | PanicOp (s: string) : prim_op args0
  | AllocNOp : prim_op args2 (* array length (positive number), initial value *)
  | AllocStructOp : prim_op args1 (* struct val *)
  | StoreOp : prim_op args2 (* pointer, value *)
  | LoadOp : prim_op args1
  | EncodeInt64Op : prim_op args2 (* int, loc to store to *)
  | DecodeInt64Op : prim_op args1 (* loc to load from *)
  | EncodeInt32Op : prim_op args2 (* int, loc to store to *)
  | DecodeInt32Op : prim_op args1 (* loc to load from *)
  | ObserveOp : prim_op args1
.

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
  (* Heap-based primitives *)
  | Primitive0 (op: prim_op args0)
  | Primitive1 (op: prim_op args1) (e : expr)
  | Primitive2 (op: prim_op args2) (e1 e2 : expr)
  (* | Primitive3 (op: prim_op args3) (e0 e1 e2 : expr) *)
  | CmpXchg (e0 : expr) (e1 : expr) (e2 : expr) (* Compare-exchange *)
  (* External FFI *)
  | ExternalOp (op: external) (e: expr)
  (* Prophecy *)
  | NewProph
  | Resolve (e0 : expr) (e1 : expr) (e2 : expr) (* wrapped expr, proph, val *)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Definition Panic s := Primitive0 (PanicOp s).
Notation AllocN := (Primitive2 AllocNOp).
Notation AllocStruct := (Primitive1 AllocStructOp).
Notation Store := (Primitive2 StoreOp).
Notation Load := (Primitive1 LoadOp).
Notation EncodeInt64 := (Primitive2 EncodeInt64Op).
Notation DecodeInt64 := (Primitive1 DecodeInt64Op).
Notation EncodeInt32 := (Primitive2 EncodeInt32Op).
Notation DecodeInt32 := (Primitive1 DecodeInt32Op).
Notation Observe := (Primitive1 ObserveOp).

Fixpoint flatten_struct (v: val) : list val :=
  match v with
  | PairV v1 v2 => flatten_struct v1 ++ flatten_struct v2
  | _ => [v]
  end.

Context {ffi : ffi_model}.

(** The state: heaps of vals. *)
Record state : Type := {
  heap: gmap loc val;
  world: ffi_state;
  trace: list val;
  used_proph_id: gset proph_id;
}.

Global Instance eta_state : Settable _ := settable! Build_state <heap; world; trace; used_proph_id>.

(* Note that ext_step takes a val, which is itself parameterized by the
external type, so the semantics of external operations depend on a definition of
the syntax of heap_lang. Similarly, it "returns" an expression, the result of
evaluating the external operation.

It also takes an entire state record, which is also parameterized by ffi_state,
since external operations can read and modify the heap.

(this makes sense because the FFI semantics has to pull out arguments from a
heap_lang val, and it must produce a return value in expr)

we produce a val to make external operations atomic
 *)
Class ext_semantics :=
  {
    ext_step : external -> val -> state -> val -> state -> Prop;
  }.

Class ext_interprable :=
  {
    (* fuel, operation, command, starting state, returns ending state *)
    ext_interpret : nat -> external -> val -> state -> option state;
  }.
Context {ffi_semantics: ext_semantics}.

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
Proof. destruct v as [ | | | [] | [] ]; simpl; exact (decide _). Defined.

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
Global Instance prim_op_eq_dec ar : EqDecision (prim_op ar).
Proof.
  hnf; intros; hnf.
  (* TODO: there's probably a very simple proof directly using a dependent
  pattern match *)
  destruct x; dependent destruction y; eauto.
  destruct (decide (s = s0));
    [ subst; left | right; inversion 1]; done.
Defined.
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
     | _, _ => right _
     end); try abstract intuition congruence.
Defined.

Global Instance base_lit_countable : Countable base_lit.
Proof.
 refine (inj_countable' (λ l, match l with
  | LitInt n => (inl (inl (inl (inl n))), None)
  | LitInt32 n => (inl (inl (inl (inr n))), None)
  | LitByte n => (inl (inl (inr n)), None)
  | LitBool b => (inl (inr b), None)
  | LitUnit => (inr (inl false), None)
  | LitString s => (inr (inr (inr s)), None)
  | LitPoison => (inr (inl true), None)
  | LitLoc l => (inr (inr (inl l)), None)
  | LitProphecy p => (inr (inl false), Some p)
  end) (λ l, match l with
  | (inl (inl (inl (inl n))), None) => LitInt n
  | (inl (inl (inl (inr n))), None) => LitInt32 n
  | (inl (inl (inr n)), None) => LitByte n
  | (inl (inr b), None) => LitBool b
  | (inr (inl false), None) => LitUnit
  | (inr (inr (inr s)), None) => LitString s
  | (inr (inl true), None) => LitPoison
  | (inr (inr (inl l)), None) => LitLoc l
  | (_, Some p) => LitProphecy p
  end) _); by intros [].
Qed.
Global Instance un_op_finite : Countable un_op.
Proof.
 refine (inj_countable' (λ op, match op with NegOp => 0 | MinusUnOp => 1 | ToUInt64Op => 2 end)
  (λ n, match n with 0 => NegOp | 1 => MinusUnOp | _ => ToUInt64Op end) _); by intros [].
Qed.
Global Instance bin_op_countable : Countable bin_op.
Proof.
 refine (inj_countable' (λ op, match op with
  | PlusOp => 0 | MinusOp => 1 | MultOp => 2 | QuotOp => 3 | RemOp => 4
  | AndOp => 5 | OrOp => 6 | XorOp => 7 | ShiftLOp => 8 | ShiftROp => 9
  | LeOp => 10 | LtOp => 11 | EqOp => 12 | OffsetOp => 13
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | 12 => EqOp | _ => OffsetOp
  end) _); by intros [].
Qed.

Inductive prim_op' := | a_prim_op {ar} (op: prim_op ar).
Instance prim_op_prim_op'_iso ar : Inj eq eq (@a_prim_op ar).
Proof.
  hnf; intros.
  inversion H.
  apply Eqdep_dec.inj_pair2_eq_dec; auto.
  intros x0 y0; destruct (decide (x0 = y0)); auto.
Qed.
Instance prim_op'_eq_dec : EqDecision prim_op'.
hnf; intros; hnf.
destruct x as [ar op], y as [ar' op'].
destruct (decide (ar = ar')); subst.
- destruct (decide (op = op')); subst; auto.
  right; intro.
  apply prim_op_prim_op'_iso in H; auto.
- right.
  inversion 1; auto.
Qed.

Global Instance prim_op'_countable : Countable prim_op'.
Proof.
  refine (inj_countable' (λ op, let 'a_prim_op op := op in
                                match op with
                                | PanicOp s => inl s
                                | AllocNOp => inr 0
                                | AllocStructOp => inr 7
                                | StoreOp => inr 1
                                | LoadOp => inr 2
                                | EncodeInt64Op => inr 5
                                | DecodeInt64Op => inr 6
                                | EncodeInt32Op => inr 8
                                | DecodeInt32Op => inr 9
                                | ObserveOp => inr 10
                                end)
                         (λ v, match v with
                               | inl s => a_prim_op (PanicOp s)
                               | inr 0 => a_prim_op AllocNOp
                               | inr 7 => a_prim_op AllocStructOp
                               | inr 1 => a_prim_op StoreOp
                               | inr 2 => a_prim_op LoadOp
                               | inr 5 => a_prim_op EncodeInt64Op
                               | inr 6 => a_prim_op DecodeInt64Op
                               | inr 8 => a_prim_op EncodeInt32Op
                               | inr 9 => a_prim_op DecodeInt32Op
                               | inr _ => a_prim_op ObserveOp
                               end) _); by intros [_ []].
Qed.

Inductive basic_type :=
  | stringVal (s:string)
  | binderVal (b:binder)
  | intVal (z:u64)
  | litVal (l: base_lit)
  | un_opVal (op:un_op)
  | bin_opVal (op:bin_op)
  | primOpVal (op:prim_op')
  | externOp (op:external)
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
                              | externOp op => inr (inr (inr (inr (inr (inr (inr op))))))
                              end)
                         (λ x, match x with
                              | inl s => stringVal s
                              | inr (inl b) => binderVal b
                              | inr (inr (inl z)) => intVal z
                              | inr (inr (inr (inl l))) => litVal l
                              | inr (inr (inr (inr (inl op)))) => un_opVal op
                              | inr (inr (inr (inr (inr (inl op))))) => bin_opVal op
                              | inr (inr (inr (inr (inr (inr (inl op)))))) => primOpVal op
                              | inr (inr (inr (inr (inr (inr (inr op)))))) => externOp op
                               end) _); by intros [].
Qed.

Definition to_prim_op : {f: forall ar (op: prim_op'), prim_op ar |
                         forall ar op, f ar (a_prim_op op) = op}.
  unshelve refine (exist _
                         (fun (ar: arity) '(a_prim_op op) =>
                            ltac:(destruct ar, op)) _);
    (* solve equality cases by unification *)
    [..|destruct op; eauto];
    (* solve default cases with an arbitrary value *)
    solve [ constructor; auto using "" ].
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
     | _ => LitV LitUnit (* dummy *)
     end
   for go).
 refine (inj_countable' enc dec _).
 refine (fix go (e : expr) {struct e} := _ with gov (v : val) {struct v} := _ for go).
  - destruct e as [v| | | | | | | | | | | | | | | | | | | |]; simpl; f_equal;
      rewrite ?to_prim_op_correct;
      [exact (gov v)|done..].
 - destruct v; by f_equal.
Qed.
Global Instance val_countable : Countable val.
Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

Global Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant; world := inhabitant; trace := inhabitant; used_proph_id := inhabitant |}.
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
  | Primitive2LCtx (op: prim_op args2) (v2 : val)
  | Primitive2RCtx (op: prim_op args2) (e1 : expr)
  (* | Primitive3LCtx (op: prim_op args3) (e1 : expr) (e2 : expr)
  | Primitive3MCtx (op: prim_op args3) (v0 : val) (e2 : expr)
  | Primitive3RCtx (op: prim_op args3) (v0 : val) (v1 : val) *)
  | ExternalOpCtx (op : external)
  | CmpXchgLCtx (e1 : expr) (e2 : expr)
  | CmpXchgMCtx (v1 : val) (e2 : expr)
  | CmpXchgRCtx (v1 : val) (v2 : val)
  | ResolveLCtx (ctx : ectx_item) (v1 : val) (v2 : val)
  | ResolveMCtx (e0 : expr) (v2 : val)
  | ResolveRCtx (e0 : expr) (e1 : expr).

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
  | Primitive2LCtx op v2 => Primitive2 op e (Val v2)
  | Primitive2RCtx op e1 => Primitive2 op e1 e
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
  | ToUInt64Op, LitV (LitInt32 v) => Some $ LitV $ LitInt (u32_to_u64 v)
  | ToUInt64Op, LitV (LitInt v) => Some $ LitV $ LitInt v
  (* | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Word.wnot n) *)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : u64) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (word.add (word:=u64_instance.u64_word) n1 n2)
  | MinusOp => Some $ LitInt (word.sub (word:=u64_instance.u64_word) n1 n2)
  | MultOp => Some $ LitInt (word.mul (word:=u64_instance.u64_word) n1 n2)
  | QuotOp => Some $ LitInt (word.divu (word:=u64_instance.u64_word) n1 n2)
  | RemOp => Some $ LitInt (word.modu (word:=u64_instance.u64_word) n1 n2)
  | AndOp => Some $ LitInt (word.and (word:=u64_instance.u64_word) n1 n2)
  | OrOp => Some $ LitInt (word.or (word:=u64_instance.u64_word) n1 n2)
  | XorOp => Some $ LitInt (word.xor (word:=u64_instance.u64_word) n1 n2)
  | ShiftLOp => Some $ LitInt (word.slu (word:=u64_instance.u64_word) n1 n2)
  | ShiftROp => Some $ LitInt (word.sru (word:=u64_instance.u64_word) n1 n2)
  | LeOp => Some $ LitBool (word.ltu n1 n2)
  | LtOp => Some $ LitBool (word.ltu n1 n2)
  | EqOp => Some $ LitBool (word.eqb n2 n2)
  | OffsetOp => None (* Pointer arithmetic *)
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
  | OffsetOp => None (* Pointer arithmetic *)
  end.

Definition bin_op_eval_string (op : bin_op) (s1 s2 : string) : option base_lit :=
  match op with
  | PlusOp => Some $ LitString (s1 ++ s2)
  | _ => None
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    (* Crucially, this compares the same way as [CmpXchg]! *)
    if decide (vals_compare_safe v1 v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitString s1), LitV (LitString s2) => LitV <$> bin_op_eval_string op s1 s2
    | LitV (LitLoc l), LitV (LitInt off) => Some $ LitV $ LitLoc (l +ₗ int.val off)
    | _, _ => None
    end.

Fixpoint heap_array (l : loc) (vs : list val) : gmap loc val :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := v]}.
Proof. by rewrite /heap_array right_id. Qed.

Open Scope Z.

Lemma heap_array_lookup l vs w k :
  heap_array l vs !! k = Some w ↔
  ∃ j, 0 ≤ j ∧ k = l +ₗ j ∧ vs !! (Z.to_nat j) = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ->] | (Hl & j & ? & -> & ?)].
    { exists 0. rewrite loc_add_0. naive_solver lia. }
    exists (1 + j). rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & ? & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite loc_add_0; eauto. }
    right. split.
    { rewrite -{1}(loc_add_0 l). intros ?%(inj _); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    exists (j - 1). rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc val) (l : loc) (vs : list val) :
  (∀ i, (0 ≤ i) → (i < length vs) → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&?&->&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

Close Scope Z.

Definition state_insert_list (l: loc) (vs: list val) (σ: state): state :=
  set heap (λ h, heap_array l vs ∪ h) σ.

(* [h] is added on the right here to make [state_init_heap_singleton] true. *)
Definition state_init_heap (l : loc) (n : Z) (v : val) (σ : state) : state :=
  state_insert_list l (replicate (Z.to_nat n) v) σ.

Lemma state_init_heap_singleton l v σ :
  state_init_heap l 1 v σ = set heap <[l:=v]> σ.
Proof.
  destruct σ as [h p]. rewrite /state_init_heap /state_insert_list /set /=. f_equiv.
  rewrite right_id insert_union_singleton_l. done.
Qed.

Definition byte_vals : list byte -> list val :=
   fmap (λ b, LitV (LitByte b)).

Theorem byte_vals_length bs : length (byte_vals bs) = length bs.
Proof.
  rewrite /byte_vals fmap_length //.
Qed.

Inductive head_step : expr → state → list observation → expr → state → list expr → Prop :=
  | RecS f x e σ :
     head_step (Rec f x e) σ [] (Val $ RecV f x e) σ []
  | PairS v1 v2 σ :
     head_step (Pair (Val v1) (Val v2)) σ [] (Val $ PairV v1 v2) σ []
  | InjLS v σ :
     head_step (InjL $ Val v) σ [] (Val $ InjLV v) σ []
  | InjRS v σ :
     head_step (InjR $ Val v) σ [] (Val $ InjRV v) σ []
  | BetaS f x e1 v2 e' σ :
     e' = subst' x v2 (subst' f (RecV f x e1) e1) →
     head_step (App (Val $ RecV f x e1) (Val v2)) σ [] e' σ []
  | UnOpS op v v' σ :
     un_op_eval op v = Some v' →
     head_step (UnOp op (Val v)) σ [] (Val v') σ []
  | BinOpS op v1 v2 v' σ :
     bin_op_eval op v1 v2 = Some v' →
     head_step (BinOp op (Val v1) (Val v2)) σ [] (Val v') σ []
  | IfTrueS e1 e2 σ :
     head_step (If (Val $ LitV $ LitBool true) e1 e2) σ [] e1 σ []
  | IfFalseS e1 e2 σ :
     head_step (If (Val $ LitV $ LitBool false) e1 e2) σ [] e2 σ []
  | FstS v1 v2 σ :
     head_step (Fst (Val $ PairV v1 v2)) σ [] (Val v1) σ []
  | SndS v1 v2 σ :
     head_step (Snd (Val $ PairV v1 v2)) σ [] (Val v2) σ []
  | CaseLS v e1 e2 σ :
     head_step (Case (Val $ InjLV v) e1 e2) σ [] (App e1 (Val v)) σ []
  | CaseRS v e1 e2 σ :
     head_step (Case (Val $ InjRV v) e1 e2) σ [] (App e2 (Val v)) σ []
  | ForkS e σ:
     head_step (Fork e) σ [] (Val $ LitV LitUnit) σ [e]
  | AllocNS (n: u64) v σ l :
     (0 < int.val n)%Z →
     (∀ i, 0 ≤ i → i < int.val n → σ.(heap) !! (l +ₗ i) = None)%Z →
     head_step (AllocN (Val $ LitV $ LitInt n) (Val v)) σ
               []
               (Val $ LitV $ LitLoc l) (state_init_heap l (int.val n) v σ)
               []
  | AllocStructS v σ l :
     (∀ i, 0 ≤ i → i < length (flatten_struct v) → σ.(heap) !! (l +ₗ i) = None)%Z →
     head_step (AllocStruct (Val v)) σ
               []
               (Val $ LitV $ LitLoc l) (state_insert_list l (flatten_struct v) σ)
               []
  | LoadS l v σ :
     σ.(heap) !! l = Some v →
     head_step (Load (Val $ LitV $ LitLoc l)) σ [] (of_val v) σ []
  | StoreS l v σ :
     is_Some (σ.(heap) !! l) →
     head_step (Store (Val $ LitV $ LitLoc l) (Val v)) σ
               []
               (Val $ LitV LitUnit) (set heap <[l:=v]> σ)
               []
  | ExternalS op v σ v' σ' :
     ext_step op v σ v' σ' ->
     head_step (ExternalOp op (Val v)) σ
               []
               (Val v') σ'
               []
  | ObserveS v σ :
     head_step (Observe (Val v)) σ
               []
               (Val $ LitV LitUnit) (set trace (fun tr => tr ++ [v]) σ)
               []
  | EncodeInt64S v l σ :
     (forall i, (i < 8)%nat -> is_Some (σ.(heap) !! (l +ₗ i))) ->
     head_step (EncodeInt64 (Val $ LitV $ LitInt v) (Val $ LitV $ LitLoc l)) σ
               []
               (Val $ LitV LitUnit) (state_insert_list l (byte_vals $ u64_le v) σ)
               []
  | DecodeInt64S l vs σ :
     (forall i, (i < 8)%nat -> σ.(heap) !! (l +ₗ i) = byte_vals vs !! i) ->
     head_step (DecodeInt64 (Val $ LitV $ LitLoc l)) σ
               []
               (Val $ LitV $ LitInt (le_to_u64 vs)) σ
               []
  | EncodeInt32S v l σ :
     (forall i, (i < 4)%nat -> is_Some (σ.(heap) !! (l +ₗ i))) ->
     head_step (EncodeInt32 (Val $ LitV $ LitInt32 v) (Val $ LitV $ LitLoc l)) σ
               []
               (Val $ LitV LitUnit) (state_insert_list l (byte_vals $ u32_le v) σ)
               []
  | DecodeInt32S l vs σ :
     (forall i, (i < 8)%nat -> σ.(heap) !! (l +ₗ i) = byte_vals vs !! i) ->
     head_step (DecodeInt32 (Val $ LitV $ LitLoc l)) σ
               []
               (Val $ LitV $ LitInt32 (le_to_u32 vs)) σ
               []
  | CmpXchgS l v1 v2 vl σ b :
     σ.(heap) !! l = Some vl →
     (* Crucially, this compares the same way as [EqOp]! *)
     vals_compare_safe vl v1 →
     b = bool_decide (vl = v1) →
     head_step (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) σ
               []
               (Val $ PairV vl (LitV $ LitBool b)) (if b then set heap <[l:=v2]> σ else σ)
               []
  | NewProphS σ p :
     p ∉ σ.(used_proph_id) →
     head_step NewProph σ
               []
               (Val $ LitV $ LitProphecy p) (set used_proph_id ({[ p ]} ∪.) σ)
               []
  | ResolveS p v e σ w σ' κs ts :
     head_step e σ κs (Val v) σ' ts →
     head_step (Resolve e (Val $ LitV $ LitProphecy p) (Val w)) σ
               (κs ++ [(p, (v, w))]) (Val v) σ' ts.

(** Basic properties about the language *)
Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof. revert κ e2. induction Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof using ext. clear ffi_semantics ffi.
       revert Ki1. induction Ki2, Ki1; naive_solver eauto with f_equal. Qed.

Lemma alloc_fresh v (n: u64) σ :
  let l := fresh_locs (dom (gset loc) σ.(heap)) in
  (0 < int.val n)%Z →
  head_step (AllocN ((Val $ LitV $ LitInt $ n)) (Val v)) σ []
            (Val $ LitV $ LitLoc l) (state_init_heap l (int.val n) v σ) [].
Proof.
  intros.
  apply AllocNS; first done.
  intros. apply (not_elem_of_dom (D := gset loc)).
  by apply fresh_locs_fresh.
Qed.

Lemma new_proph_id_fresh σ :
  let p := fresh σ.(used_proph_id) in
  head_step NewProph σ [] (Val $ LitV $ LitProphecy p) (set used_proph_id ({[ p ]} ∪.) σ) [].
Proof. constructor. apply is_fresh. Qed.

Lemma heap_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.
End external.
End heap_lang.

(** Language *)

(* Prefer heap_lang names over ectx_language names. *)
Export heap_lang.

Arguments ext_semantics ext ffi : clear implicits.
Arguments heap_lang.heap_lang_mixin {ext} {ffi} ffi_semantics.

Section go_lang.
  Context {ext: ext_op} {ffi: ffi_model}
          {ffi_semantics: ext_semantics ext ffi}.
  Canonical Structure heap_ectxi_lang := (EctxiLanguage (heap_lang.heap_lang_mixin ffi_semantics)).
  Canonical Structure heap_ectx_lang := (EctxLanguageOfEctxi heap_ectxi_lang).
  Canonical Structure heap_lang := (LanguageOfEctx heap_ectx_lang).

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

Lemma prim_step_to_val_is_head_step e σ1 κs w σ2 efs :
  prim_step e σ1 κs (Val w) σ2 efs → head_step (ffi_semantics:=ffi_semantics) e σ1 κs (Val w) σ2 efs.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some w) as H3; first by rewrite -H2.
  apply to_val_fill_some in H3 as [-> ->]. subst e. done.
Qed.

Lemma irreducible_resolve e v1 v2 σ :
  irreducible e σ → irreducible (Resolve e (Val v1) (Val v2)) σ.
Proof.
  intros H κs ** [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind; simpl in Hfill.
  - subst e1'. inversion step. eapply H. by apply head_prim_step.
  - rewrite fill_app /= in Hfill.
    destruct K; (inversion Hfill; subst; clear Hfill; try
      match goal with | H : Val ?v = fill Ks ?e |- _ =>
        (assert (to_val (fill Ks e) = Some v) as HEq by rewrite -H //);
        apply to_val_fill_some in HEq; destruct HEq as [-> ->]; inversion step
      end).
    apply (H κs (fill_item K (foldl (flip fill_item) e2' Ks)) σ' efs).
    econstructor 1 with (K := Ks ++ [K]); last done; simpl; by rewrite fill_app.
Qed.

End go_lang.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation AllocN := (Primitive2 AllocNOp).
Notation AllocStruct := (Primitive1 AllocStructOp).
Notation Store := (Primitive2 StoreOp).
Notation Load := (Primitive1 LoadOp).
Notation EncodeInt64 := (Primitive2 EncodeInt64Op).
Notation DecodeInt64 := (Primitive1 DecodeInt64Op).
Notation EncodeInt32 := (Primitive2 EncodeInt32Op).
Notation DecodeInt32 := (Primitive1 DecodeInt32Op).
Notation Observe := (Primitive1 ObserveOp).
