From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Export loop.
From New.golang.theory Require Import exception typing.
From iris_named_props Require Export named_props.
From Perennial Require Import base.

Set Default Proof Using "Type".

(* See the documentation for the tactic [wp_for] below for an idea of the
exported interface of this file. *)

Section wps.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance pure_continue_val (v1 : val) :
  PureWp True (exception_seq v1 (continue_val)) (continue_val).
Proof.
  rewrite exception_seq_unseal continue_val_unseal.
  intros ?????. iIntros "Hwp".
  wp_call_lc "?". by iApply "Hwp".
Qed.

Global Instance pure_break_val (v1 : val) : PureWp True (exception_seq v1 (break_val)) (break_val).
Proof.
  rewrite exception_seq_unseal break_val_unseal.
  intros ?????. iIntros "Hwp".
  wp_call_lc "?". by iApply "Hwp".
Qed.

Global Instance pure_do_continue_val : PureWp True (continue: #()) (continue_val).
Proof.
  rewrite do_continue_unseal continue_val_unseal.
  intros ?????. iIntros "Hwp".
  wp_call_lc "?". by iApply "Hwp".
Qed.

Global Instance pure_do_break_val : PureWp True (break: #()) (break_val).
Proof.
  rewrite do_break_unseal break_val_unseal.
  intros ?????. iIntros "Hwp".
  wp_call_lc "?". by iApply "Hwp".
Qed.

(* Sealed - use the wp_for_post_ lemmas below to prove this. *)
Definition for_postcondition_def stk E (post : val) P Φ bv : iProp Σ :=
            ⌜ bv = continue_val ⌝ ∗ WP post #() @ stk; E {{ _, P }} ∨
            (∃ v, ⌜ bv = execute_val v ⌝ ∗ WP post #() @ stk; E {{ _, P }}) ∨
            ⌜ bv = break_val ⌝ ∗ Φ (execute_val #()) ∨
            (∃ v, ⌜ bv = return_val v ⌝ ∗ Φ bv).
Program Definition for_postcondition := sealed @for_postcondition_def.
Definition for_postcondition_unseal : for_postcondition = _ := seal_eq _.

Lemma wp_for P stk E (cond body post : val) Φ :
  P -∗
  □ (P -∗
     WP cond #() @ stk ; E {{ v, if decide (v = #true) then
                                   WP body #() @ stk ; E {{ for_postcondition stk E post P Φ }}
                                 else if decide (v = #false) then
                                        Φ (execute_val #())
                                      else False
                           }}
    ) -∗
  WP (for: cond; post := body) @ stk ; E {{ Φ }}.
Proof.
  iIntros "HP #Hloop".
  rewrite do_for_unseal.
  rewrite for_postcondition_unseal.
  iLöb as "IH".
  wp_call.
  iDestruct ("Hloop" with "HP") as "Hloop1".
  wp_bind (cond #()).
  wp_apply (wp_wand with "Hloop1").
  iIntros (c) "Hbody".
  destruct (decide _).
  - subst. wp_pures.
    wp_apply (wp_wand with "Hbody").
    iIntros (bc) "Hb". (* "[[% HP] | [[% HP] | [[% HΦ] | HΦ]]]". *)
    iDestruct "Hb" as "[[% HP]|Hb]".
    { (* body terminates with "continue" *)
      subst. wp_pures. rewrite continue_val_unseal.
      wp_pures.
      wp_apply (wp_wand with "HP").
      iIntros (?) "HP".
      iSpecialize ("IH" with "HP").
      wp_pures.
      wp_apply (wp_wand with "IH").
      iIntros (?) "HΦ".
      wp_pures.
      done.
    }
    iDestruct "Hb" as "[[% [% HP]]|Hb]".
    { (* body terminates with "execute" *)
      subst. rewrite execute_val_unseal. wp_pures. (* FIXME: don't unfold [do:] here *)
      wp_apply (wp_wand with "HP").
      iIntros (?) "HP".
      iSpecialize ("IH" with "HP").
      wp_pures.
      wp_apply (wp_wand with "IH").
      iIntros (?) "HΦ".
      wp_pures.
      done.
    }
    iDestruct "Hb" as "[[% HP]|Hb]".
    { (* body terminates with "break" *)
      subst. rewrite break_val_unseal. wp_pures.
      by iFrame.
    }
    iDestruct "Hb" as (?) "[% HΦ]".
    { (* body terminates with other error code *)
      subst. rewrite return_val_unseal. wp_pures. done.
    }
  - destruct (decide _); subst.
    { wp_pures. by iFrame. }
    { by iExFalso. }
Qed.

Lemma wp_for_post_do (v : val) stk E (post : val) P Φ :
  WP (post #()) @ stk; E {{ _, P }} -∗
  for_postcondition stk E post P Φ (execute_val v).
Proof.
  iIntros "H". rewrite for_postcondition_unseal /for_postcondition_def.
  eauto 10 with iFrame.
Qed.

Lemma wp_for_post_continue stk E (post : val) P Φ :
  WP (post #()) @ stk; E {{ _, P }} -∗
  for_postcondition stk E post P Φ continue_val.
Proof.
  iIntros "H". rewrite for_postcondition_unseal /for_postcondition_def.
  eauto 10 with iFrame.
Qed.

Lemma wp_for_post_break stk E (post : val) P Φ :
  Φ (execute_val #()) -∗
  for_postcondition stk E post P Φ break_val.
Proof.
  iIntros "H". rewrite for_postcondition_unseal /for_postcondition_def.
  eauto 10 with iFrame.
Qed.

Lemma wp_for_post_return stk E (post : val) P Φ v :
  Φ (return_val v) -∗
  for_postcondition stk E post P Φ (return_val v).
Proof.
  iIntros "H". rewrite for_postcondition_unseal /for_postcondition_def.
  eauto 10 with iFrame.
Qed.

End wps.

(** Tactic for convenient loop reasoning. First use [iAssert] to generalize the
current context to the loop invariant, then apply this tactic. Use
[wp_for_post_do], [wp_for_post_continue], and [wp_for_post_return] at the leaves
of the proof. *)
Ltac wp_for_core :=
  wp_bind (do_for _ _ _); iApply (wp_for with "[-]");
  [ by iNamedAccu
  | iIntros "!# __CTX"; iNamed "__CTX" ].

(** Automatically apply the right theorem for [for_postcondition] *)
Ltac wp_for_post_core :=
  lazymatch goal with
  | |- environments.envs_entails _ (for_postcondition _ _ _ _ _ _) =>
      (* this could use pattern matching but it's not really necessary,
      unification will handle it *)
      first [
          iApply wp_for_post_do; wp_pures
        | iApply wp_for_post_continue
        | iApply wp_for_post_break
        | iApply wp_for_post_return
        ]
  | _ => fail "wp_for_post: not a for_postcondition goal"
  end.
