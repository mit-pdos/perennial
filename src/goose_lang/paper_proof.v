From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode.
From Perennial.goose_lang.lib Require Export typed_mem loop.impl.
From Perennial.goose_lang Require Import crash_borrow.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!stagedG Σ}.
Context {ext_ty: ext_types ext}.

(* paper presentation of fork rule, with wpc *)
Theorem wpc_fork_paper (k: nat)
        (e e': expr) (P Q: iProp Σ) (R: val → iProp Σ) (Rc Rc': iProp Σ) :
  to_val e = None →
  □ (P -∗ Rc) -∗
  □ (Q -∗ Rc') -∗
  (P -∗ WPC e @ k; ⊤ {{ λ _, Rc }} {{ Rc }}) -∗
  (Q -∗ WPC e' @ k; ⊤ {{ R }} {{ Rc' }}) -∗
  (P ∗ Q -∗ WPC Fork e;; e' @ k; ⊤ {{ R }} {{ Rc ∗ Rc' }}).
Proof using stagedG0.
  iIntros (Henotval) "#HPRc #HQRc' He He' [HP HQ]".
  (* iSpecialize ("He" with "HP").
  iSpecialize ("He'" with "HQ"). *)

  rewrite bi.sep_comm.
  change (Fork e;; e')%E with (fill [AppRCtx (λ: <>, e')]%E (Fork e)).
  iApply (wpc_crash_borrow_init_ctx' with "HP HPRc").
  { done. }
  iSplit.
  { iApply "HQRc'". iFrame. }
  iIntros "HPborrow".
  wpc_apply (wpc_fork with "[He HPborrow]").
  - iApply bi.later_intro.
    iApply (wpc_crash_borrow_open_cancel with "HPborrow").
    { done. }
    iSplit; [ done | ].

    iIntros "HP" (mj Hmj). iSpecialize ("He" with "HP").
    iApply (wpc_mono _ _ _ _ _ _ _ with "He").
    { simpl.
      iIntros (_) "Hrc".
      iSplit; [ | done ].
      iApply wpc_crash_modality_intro. iFrame. }
    iIntros "$".
  - iSplit.
    { iApply "HQRc'". iFrame. }
    iNext.
    wpc_pures.
    { iApply "HQRc'". iFrame. }
    iApply ("He'" with "HQ").
Qed.

End goose_lang.
