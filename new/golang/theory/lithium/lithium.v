From Perennial.goose_lang Require Import notation.
From Coq Require Import ssreflect.
From New.golang.defn Require Import typing.
From New.golang.theory Require Import proofmode globals pkg loop chan.
From New.golang.theory Require Import mem.
From Perennial Require Import base.

From New.proof Require Import std.

From lithium Require Import hooks all.

Set Default Proof Using "Type".

(** * Definitions of Lithium functions *)
(** First, we define the Lithium functions that we will use later. *)
Section definitions.
  Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!goGlobalsGS Σ}.

  Definition expr_ok (e : expr) (G : val → iProp Σ) : iProp Σ :=
    WP e {{ G }}.

  Definition binop_ok (op : bin_op) (v1 v2 : val) (G : val → iProp Σ) : iProp Σ :=
    WP BinOp op v1 v2 {{ G }}.

  Definition unop_ok (op : un_op) (v : val) (G : val → iProp Σ) : iProp Σ :=
    WP UnOp op v {{ G }}.

  Definition if_ok (v : val) (G1 G2 : iProp Σ) : iProp Σ :=
    ∃ b : bool, ⌜v = #b⌝ ∗ if b then G1 else G2.
End definitions.

(** * Boilerplate for setup *)
(** The following code is necessary to register the Lithium functions.
You can ignore it for the purposes of this tutorial. *)
Section setup.
  Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!goGlobalsGS Σ}.

  Class ExprOk (e : expr) : Type :=
    expr_ok_proof G : iProp_to_Prop (expr_ok e G).
  Class BinopOk (op : bin_op) (v1 v2 : val) : Type :=
    binop_ok_proof G : iProp_to_Prop (binop_ok op v1 v2 G).
  Class UnopOk (op : un_op) (v : val) : Type :=
    unop_ok_proof G : iProp_to_Prop (unop_ok op v G).
  Class IfOk (v : val) : Type :=
    if_ok_proof G1 G2 : iProp_to_Prop (Σ:=Σ) (if_ok v G1 G2).
End setup.

Ltac generate_i2p_instance_to_tc_hook arg c ::=
  lazymatch c with
  | expr_ok ?x1 => constr:(ExprOk x1)
  | binop_ok ?x1 ?x2 ?x3 => constr:(BinopOk x1 x2 x3)
  | unop_ok ?x1 ?x2 => constr:(UnopOk x1 x2)
  | if_ok ?x1 => constr:(IfOk x1)
  end.
Ltac liExtensible_to_i2p_hook P bind cont ::=
  lazymatch P with
  | expr_ok ?e ?G =>
      cont uconstr:(((_ : ExprOk _) _))
  | binop_ok ?op ?v1 ?v2 ?G =>
      cont uconstr:(((_ : BinopOk _ _ _) _))
  | unop_ok ?op ?v ?G =>
      cont uconstr:(((_ : UnopOk _ _) _))
  | if_ok ?v ?G1 ?G2 =>
      cont uconstr:(((_ : IfOk _) _ _))
  end.

Ltac liToSyntax_hook ::=
  change (expr_ok ?x1) with (li.bind1 (expr_ok x1));
  change (binop_ok ?x1 ?x2 ?x3) with (li.bind1 (binop_ok x1 x2 x3));
  change (unop_ok ?x1 ?x2) with (li.bind1 (unop_ok x1 x2)).

Ltac can_solve_hook ::= done.

Ltac liTStep :=
 liEnsureInvariant;
 first [
 liStep
]; liSimpl.

Ltac liTUnfold :=
  liFromSyntax; unfold expr_ok, binop_ok, unop_ok, if_ok.


(** * Tutorial *)
(** This is the start of the actual tutorial. *)
Section proofs.
  Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!goGlobalsGS Σ}.

  (** For explanation, see the corresponding sections of the "Lithium
  by Example" chapter in Michael Sammler's dissertation. *)

  (** ** 1. Lithium basics *)
  Definition assert_two : expr :=
    let: "x" := #(W64 1) in
    let: "y" := "x" + #(W64 1) in
    std.Assert ("y" = #(W64 2)).

  Lemma assert_two_correct :
    ⊢ [{
      _ ← {expr_ok assert_two};
      done
    }  ].
  Proof.
    (** Prepare goal and unfold assert_two. *)
    iStartProof. unfold assert_two.
    (** Run Lithium. *)
    repeat liTStep; liShow.
    (** No progress since we have not defined the Lithium function [expr_ok] yet. *)
  Abort.

  (** Basic rules for [expr_ok] and [binop_ok]. *)
  Lemma expr_let x e1 e2 G :
    expr_ok (Let x e1 e2) G :-
      v1 ← {expr_ok e1};
      v2 ← {expr_ok (subst' x v1 e2)};
      return G v2.
  Proof.
    liTUnfold. iIntros "HWP". wp_bind (e1).
    iApply (wp_wand with "HWP"). iIntros (?) "HWP".
    by wp_pures.
  Qed.
  Definition expr_let_inst := [instance expr_let].
  Global Existing Instance expr_let_inst | 2.

  Lemma expr_val v G :
    expr_ok (Val v) G :- return G v.
  Proof. liTUnfold. iIntros "HG". by wp_pures. Qed.
  Definition expr_val_inst := [instance expr_val].
  Global Existing Instance expr_val_inst.

  Lemma expr_binop op e1 e2 G :
    expr_ok (BinOp op e1 e2) G :-
      v1 ← {expr_ok e1};
      v2 ← {expr_ok e2};
      v  ← {binop_ok op v1 v2};
      return G v.
  Proof.
    liTUnfold. iIntros "HWP". wp_bind (e1).
    iApply (wp_wand with "HWP"). iIntros (?) "HWP".
    wp_bind (e2).
    iApply (wp_wand with "HWP"). by iIntros (?) "HWP".
  Qed.
  Definition expr_binop_inst := [instance expr_binop].
  Global Existing Instance expr_binop_inst.

  Lemma binop_plus_int_int (n1 n2 : w64) G :
    binop_ok PlusOp #n1 #n2 G :-
      return G #(word.add n1 n2).
  Proof. liTUnfold. iIntros "HG". by wp_pures. Qed.
  Definition binop_plus_int_int_inst := [instance binop_plus_int_int].
  Global Existing Instance binop_plus_int_int_inst.
  Lemma binop_minus_int_int (n1 n2 : w64) G :
    binop_ok MinusOp #n1 #n2 G :-
      return G #(word.sub n1 n2).
  Proof. liTUnfold. iIntros "HG". by wp_pures. Qed.
  Definition binop_minus_int_int_inst := [instance binop_minus_int_int].
  Global Existing Instance binop_minus_int_int_inst.
  Lemma binop_eq_int_int (n1 n2 : w64) G :
    binop_ok EqOp #n1 #n2 G :-
      return G #(bool_decide (n1 = n2)).
  Proof. liTUnfold. iIntros "HG". by wp_pures. Qed.
  Definition binop_eq_int_int_inst := [instance binop_eq_int_int].
  Global Existing Instance binop_eq_int_int_inst.

  Lemma expr_assert e G :
    expr_ok (std.Assert e) G :-
      v ← {expr_ok e};
      exhale ⌜v = #true⌝;
      return G #().
  Proof.
    liTUnfold. iIntros "HWP". wp_bind (e).
    iApply (wp_wand with "HWP"). iIntros (?) "[-> HWP]".
  Admitted.
  Definition expr_assert_inst := [instance expr_assert].
  Global Existing Instance expr_assert_inst.

  (** Now Lithium automatically verifies [assert_two]! *)
  Lemma assert_two_correct :
    ⊢ [{
      _ ← {expr_ok assert_two};
      done
    } ].
  Proof.
    iStartProof. unfold assert_two.
    repeat liTStep; liShow.
  Qed.
End proofs.
