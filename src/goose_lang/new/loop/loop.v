From Perennial.goose_lang Require Import notation typing exception proofmode.
From Perennial.goose_lang.new Require Export loop.impl.
From iris_named_props Require Export named_props.

Set Default Proof Using "Type".

Section pure_execs.
Context `{ffi_sem: ffi_semantics}.
Axiom some_n : nat.

Global Instance pure_continue_val (e : expr) : PureExec True some_n (exception_seq e (continue_val)) (continue_val).
Admitted.

Global Instance pure_break_val (e : expr) : PureExec True some_n (exception_seq e (break_val)) (break_val).
Admitted.

Global Instance pure_do_continue_val : PureExec True some_n (continue: #()) (continue_val).
Admitted.

Global Instance pure_do_break_val : PureExec True some_n (break: #()) (break_val).
Admitted.

End pure_execs.

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

(* FIXME: seal this *)
Definition for_postcondition stk E (post : val) P Φ bv : iProp Σ :=
            ⌜ bv = continue_val ⌝ ∗ WP post #() @ stk; E {{ _, P }} ∨
            (∃ v, ⌜ bv = execute_val v ⌝ ∗ WP post #() @ stk; E {{ _, P }}) ∨
            ⌜ bv = break_val ⌝ ∗ Φ (execute_val #()) ∨
            (∃ v, ⌜ bv = return_val v ⌝ ∗ Φ bv)
.

Theorem wp_for P stk E (cond body post : val) Φ :
  P -∗
  □ (P -∗
     WP cond #() @ stk ; E {{ v, ⌜ v = #true ⌝ ∗
                                 WP body #() @ stk ; E {{ for_postcondition stk E post P Φ }} ∨
                                 ⌜ v = #false ⌝ ∗ Φ (execute_val #()) }})  -∗
  WP (for: cond; post := body) @ stk ; E {{ Φ }}.
Proof.
  iIntros "HP #Hloop".
  rewrite do_for_unseal.
  iLöb as "IH".
  wp_rec.
  wp_pures.
  iDestruct ("Hloop" with "HP") as "Hloop1".
  wp_bind (cond #()).
  wp_apply (wp_wand with "Hloop1").
  iIntros (c) "Hbody".
  iDestruct "Hbody" as "[[% Hbody]|[% HΦ]]"; subst.
  - wp_pures.
    wp_apply (wp_wand with "Hbody").
    iIntros (bc) "Hb". (* "[[% HP] | [[% HP] | [[% HΦ] | HΦ]]]". *)
    iDestruct "Hb" as "[[% HP]|Hb]".
    { (* body terminates with "continue" *)
      subst. wp_pures. rewrite continue_val_unseal.
      wp_apply (wp_wand with "HP").
      iIntros (?) "HP".
      iSpecialize ("IH" with "HP").
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
  - wp_pures. by iFrame.
Qed.

Lemma wp_for_post_do (v : val) stk E (post : val) P Φ :
  WP (post #()) @ stk; E {{ _, P }} -∗
  for_postcondition stk E post P Φ (execute_val v).
Proof.
  iIntros "H". rewrite /for_postcondition. iRight. iLeft. iFrame "H". iPureIntro. by eexists.
Qed.

Lemma wp_for_post_continue stk E (post : val) P Φ :
  WP (post #()) @ stk; E {{ _, P }} -∗
  for_postcondition stk E post P Φ continue_val.
Proof.
  iIntros "H". rewrite /for_postcondition. iLeft. iFrame "H". iPureIntro. by eexists.
Qed.

End goose_lang.

(** Tactic for convenient loop reasoning *)
Ltac wp_for :=
  wp_bind (do_for _ _ _); iApply (wp_for with "[-]");
  [ by iNamedAccu
  | iIntros "!# __CTX"; iNamed "__CTX" ].
