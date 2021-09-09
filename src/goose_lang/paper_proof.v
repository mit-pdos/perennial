From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode.
From Perennial.goose_lang.lib Require Export typed_mem loop.impl.
From Perennial.goose_lang Require Import crash_borrow.

Set Default Proof Using "Type".

Section bi.
  Context {PROP:bi}.
  Implicit Types (P Q R: PROP).

  Lemma bi_and_forall_l_apply {A} (x: A) Φ P :
        (∀ x, Φ x)%I ∧ P -∗
        Φ x ∧ P.
  Proof.
    iIntros "H".
    iSplit.
    { iLeft in "H". iApply "H". }
    iRight in "H". iAssumption.
  Qed.

  Lemma bi_and_wand_l_apply `{!BiAffine PROP} P Q R :
        (P -∗ Q)%I ∧ R -∗
        P -∗
        Q ∧ R.
  Proof.
    iIntros "H P".
    iSplit.
    { iLeft in "H". iApply ("H" with "P"). }
    iRight in "H". iAssumption.
  Qed.
End bi.

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!stagedG Σ}.
Context {ext_ty: ext_types ext}.


Lemma wpc0_crash_to_post stk k mj E (e: expr) Φ Φc :
      wpc0 stk k mj E e Φ Φc -∗
      wpc0 stk k mj E e (λ (v: val), Φ v ∧ wpc_crash_modality E mj Φc) Φc.
Proof.
  iIntros "H".
  iLöb as "IH" forall (e).
  rewrite !wpc0_unfold /wpc_pre.
  destruct (language.to_val e) eqn:Hval.
  - fold (wpc_crash_modality E mj Φc).
    iSplit; last first.
    { iDestruct "H" as "[_ $]". }
    iIntros (q g ns D κs) "Hinterp NC".
    iDestruct (bi_and_forall_l_apply q with "H") as "H".
    iDestruct (bi_and_forall_l_apply g with "H") as "H".
    iDestruct (bi_and_forall_l_apply ns with "H") as "H".
    iDestruct (bi_and_forall_l_apply D with "H") as "H".
    iDestruct (bi_and_forall_l_apply κs with "H") as "H".
    iDestruct (bi_and_wand_l_apply with "H Hinterp") as "H".
    iDestruct (bi_and_wand_l_apply with "H NC") as "H".
Abort.

Lemma wpc_elim_wpc_crash_modality stk k E (e: expr) (Φ: val → iProp Σ) Φc :
  WPC e @ stk; k; E {{ Φ }} {{ Φc }} -∗
  ∀ mj, wpc_crash_modality E mj Φc.
Proof.
  rewrite wpc_unfold /wpc_pre.
  iIntros "Hwpc" (mj).
  iDestruct ("Hwpc" $! mj) as "[_ $]".
Qed.

(* paper presentation of fork rule, with wpc *)
Theorem wpc_fork_paper (k: nat)
        (e e': expr) (P Q: iProp Σ) (R: val → iProp Σ) (Rc Rc': iProp Σ) :
  to_val e = None →
  □ (P -∗ Rc) -∗
  (Q -∗ Rc') -∗
  (P -∗ WPC e @ k; ⊤ {{ λ _, Rc }} {{ Rc }}) -∗
  (Q -∗ WPC e' @ k; ⊤ {{ R }} {{ Rc' }}) -∗
  (P ∗ Q -∗ WPC Fork e;; e' @ k; ⊤ {{ R }} {{ Rc ∗ Rc' }}).
Proof using stagedG0.
  iIntros (Henotval) "#HPRc HQRc' He He' [HP HQ]".
  (* iSpecialize ("He" with "HP").
  iSpecialize ("He'" with "HQ"). *)

  rewrite (bi.sep_comm Rc Rc').
  change (Fork e;; e')%E with (fill [AppRCtx (λ: <>, e')]%E (Fork e)).
  iApply (wpc_crash_borrow_init_ctx'' with "HP HPRc").
  { done. }
  iSplit.
  { iApply (wpc_elim_wpc_crash_modality with "(He' HQ)"). }
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
