From Perennial.goose_lang Require Import notation typing exception.
From Perennial.goose_lang Require Import proofmode wpc_proofmode crash_borrow.
From Perennial.goose_lang.lib Require Export typed_mem.
From Perennial.goose_lang.new Require Export loop.impl.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Definition is_return_val bv : Prop :=
  match bv with
  | PairV #(str "return") _ => True
  | _ => False
  end
.

Definition for_postcondition stk E (post : val) P Φ bv : iProp Σ :=
            ⌜ bv = continue_val ⌝ ∗ WP post #() @ stk; E {{ _, P }} ∨
            ⌜ bv = execute_val ⌝ ∗ WP post #() @ stk; E {{ _, P }} ∨
            ⌜ bv = break_val ⌝ ∗ WP do: #() @ stk ; E {{ Φ }} ∨
            ∃ v, ⌜ bv = return_val v ⌝ ∗ Φ bv
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
    iDestruct "Hb" as "[[% HP]|Hb]".
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

Local Opaque load_ty store_ty.

End goose_lang.

(** Tactics for convenient loop reasoning *)

Ltac wp_for :=
  wp_bind (do_for _ _ _); iApply (wp_for with "[-]");
  [ by iNamedAccu
  | iIntros "!# __CTX"; iNamed "__CTX" ].
