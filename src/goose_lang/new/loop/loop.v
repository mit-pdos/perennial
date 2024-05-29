From Perennial.goose_lang Require Import notation typing exception proofmode.
From Perennial.goose_lang.new Require Export loop.impl.
From iris_named_props Require Export named_props.


Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

(* FIXME: seal this *)
Definition for_postcondition stk E (post : val) P Φ bv : iProp Σ :=
            ⌜ bv = continue_val ⌝ ∗ WP post #() @ stk; E {{ _, P }} ∨
            (∃ v, ⌜ bv = execute_val v ⌝ ∗ WP post #() @ stk; E {{ _, P }}) ∨
            ⌜ bv = break_val ⌝ ∗ WP do: #() @ stk ; E {{ Φ }} ∨
            (∃ v, ⌜ bv = return_val v ⌝ ∗ Φ bv)
.

Theorem wp_for P stk E (cond body post : val) Φ :
  P -∗
  □ (P -∗
     WP cond #() @ stk ; E {{ v, ⌜ v = #true ⌝ ∗
                                 WP body #() @ stk ; E {{ for_postcondition stk E post P Φ }} ∨
                                 ⌜ v = #false ⌝ ∗ WP (do: #()) @ stk ; E {{ Φ }} }})  -∗
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
      subst. wp_pures.
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
      subst. wp_pures. (* FIXME: don't unfold [do:] here *)
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
      subst. wp_pures.
      wp_apply (wp_wand with "HP").
      iIntros (?) "HΦ".
      wp_pures.
      done.
    }
    iDestruct "Hb" as (?) "[% HΦ]".
    { (* body terminates with other error code *)
      wp_pures.
      subst.
      wp_pures.
      done.
    }
  - wp_pures. wp_apply (wp_wand with "HΦ"). iIntros (?) "HΦ". wp_pures.
    done.
Qed.

Lemma wp_for_post_do (v : val) stk E (post : val) P Φ :
  WP (post #()) @ stk; E {{ _, P }} -∗
  WP (do: v) @ stk ; E {{ for_postcondition stk E post P Φ }}.
Proof.
  iIntros "H".
  rewrite /for_postcondition. rewrite do_execute_unseal /exception.do_execute_def.
  wp_pures. iRight. iLeft. iFrame "H". iPureIntro. by eexists.
Qed.

End goose_lang.

(** Tactic for convenient loop reasoning *)
Ltac wp_for :=
  wp_bind (do_for _ _ _); iApply (wp_for with "[-]");
  [ by iNamedAccu
  | iIntros "!# __CTX"; iNamed "__CTX" ].
