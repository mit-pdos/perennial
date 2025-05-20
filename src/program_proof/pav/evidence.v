From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import
  core cryptoffi logical_audit serde.

Module Evid.
Record t :=
  mk {
    sigDig0: SigDig.t;
    sigDig1: SigDig.t;
  }.
Section defs.
Context `{!heapGS Σ, !pavG Σ}.
Definition own ptr obj d : iProp Σ :=
  ∃ ptr_sigDig0 ptr_sigDig1,
  "Hown_sigDig0" ∷ SigDig.own ptr_sigDig0 obj.(sigDig0) d ∗
  "Hptr_sigDig0" ∷ ptr ↦[Evid :: "sigDig0"]{d} #ptr_sigDig0 ∗
  "Hown_sigDig1" ∷ SigDig.own ptr_sigDig1 obj.(sigDig1) d ∗
  "Hptr_sigDig1" ∷ ptr ↦[Evid :: "sigDig1"]{d} #ptr_sigDig1.
End defs.
End Evid.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

(* is_SigDig talks about proper encoding as well,
since dealing with the sigpred often requires this. *)
Definition is_SigDig obj pk : iProp Σ :=
  ∃ pre_sig,
  "%Henc" ∷ ⌜ PreSigDig.encodes pre_sig (PreSigDig.mk obj.(SigDig.Epoch) obj.(SigDig.Dig)) ⌝ ∗
  "#Hsig" ∷ is_sig pk pre_sig obj.(SigDig.Sig).

Definition is_Evid obj pk : iProp Σ :=
  "#His_sigDig0" ∷ is_SigDig obj.(Evid.sigDig0) pk ∗
  "#His_sigDig1" ∷ is_SigDig obj.(Evid.sigDig1) pk ∗
  "%Heq_ep" ∷ ⌜ obj.(Evid.sigDig0).(SigDig.Epoch) =
                obj.(Evid.sigDig1).(SigDig.Epoch) ⌝ ∗
  "%Hneq_dig" ∷ ⌜ obj.(Evid.sigDig0).(SigDig.Dig) ≠
                  obj.(Evid.sigDig1).(SigDig.Dig) ⌝.

Lemma is_sigdig_agree sd0 sd1 pk γ :
  sd0.(SigDig.Epoch) = sd1.(SigDig.Epoch) →
  is_sig_pk pk (sigpred γ) -∗
  is_SigDig sd0 pk -∗
  is_SigDig sd1 pk -∗
  ⌜ sd0.(SigDig.Dig) = sd1.(SigDig.Dig) ⌝.
Proof.
  iIntros (Heq) "#Hpk". iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iDestruct (is_sig_to_pred with "Hpk Hsig0") as "H". iNamedSuffix "H" "0".
  iDestruct (is_sig_to_pred with "Hpk Hsig1") as "H". iNamedSuffix "H" "1".
  (* unify with sigdig existentially hidden by sigpred. *)
  opose proof (PreSigDig.inj [] [] Henc1 Henc3 _); eauto.
  opose proof (PreSigDig.inj [] [] Henc0 Henc2 _); eauto.
  intuition. simplify_eq/=.
  iDestruct (mono_list_idx_own_get with "Hlb0") as "Hidx0"; [done|].
  iDestruct (mono_list_idx_own_get with "Hlb1") as "Hidx1"; [done|].
  rewrite Heq.
  iDestruct (mono_list_idx_agree with "Hidx0 Hidx1") as %?.
  naive_solver.
Qed.

Lemma evid_impl_not_good obj pk γ :
  is_Evid obj pk -∗
  is_sig_pk pk (sigpred γ) -∗
  False.
Proof.
  iIntros "#Hevid #Hpk". iNamed "Hevid".
  by iDestruct (is_sigdig_agree with "Hpk His_sigDig0 His_sigDig1") as %?.
Qed.

Lemma wp_CheckSigDig ptr obj sl_pk pk :
  {{{
    "#Hdig" ∷ SigDig.own ptr obj DfracDiscarded ∗
    "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk
  }}}
  CheckSigDig #ptr (slice_val sl_pk)
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷ (⌜ err = false ⌝ ∗-∗ is_SigDig obj pk)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hdig". wp_rec.
  do 2 wp_loadField.
  wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  wp_apply wp_NewSlice. iIntros "* Hsl_enc".
  wp_apply (PreSigDig.wp_enc (PreSigDig.mk _ _) with "[$Hsl_enc $Epoch $Dig //]").
  iIntros "*". iNamed 1. iClear "Hobj".
  replace (uint.nat (W64 0)) with (0%nat) by word.
  simpl in *.
  iDestruct (own_slice_to_small with "Hsl_b") as "Hsl_b".
  wp_loadField.
  wp_apply (wp_SigPublicKey__Verify with "[Hsl_pk Hsl_b Hsl_Sig]"); [iFrame "∗#"|].
  iClear "Hsl_pk Hsl_Sig".
  iIntros "*". iNamed 1.
  iApply "HΦ".
  destruct err.
  - iSplit. { by iIntros (?). }
    iDestruct "Hgenie" as "[_ Hgenie]".
    iNamedSuffix 1 "0".
    rewrite /PreSigDig.encodes in Henc Henc0.
    intuition. simplify_eq/=.
    by iApply "Hgenie".
  - iSplit; [|naive_solver].
    iIntros (_).
    iDestruct "Hgenie" as "[Hgenie _]".
    by iDestruct ("Hgenie" with "[//]") as "$".
Qed.

Lemma wp_Evid__Check ptr_e e sl_pk pk :
  {{{
    "#Hevid" ∷ Evid.own ptr_e e DfracDiscarded ∗
    "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk
  }}}
  Evid__Check #ptr_e (slice_val sl_pk)
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷ (⌜ err = false ⌝ ∗-∗ is_Evid e pk)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hevid". wp_rec.

  wp_loadField.
  wp_apply (wp_CheckSigDig with "[$Hown_sigDig0 $Hsl_pk]").
  iIntros "*". iNamedSuffix 1 "0".
  wp_if_destruct.
  { iApply "HΦ".
    iDestruct "Hgenie0" as "[_ Hgenie]".
    iIntros "!>". iSplit. { by iIntros (?). }
    iNamed 1.
    by iApply "Hgenie". }
  iDestruct "Hgenie0" as "[Hgenie0 _]".
  iDestruct ("Hgenie0" with "[//]") as "#Hgenie0".

  wp_loadField.
  wp_apply (wp_CheckSigDig with "[$Hown_sigDig1 $Hsl_pk]").
  iIntros "*". iNamedSuffix 1 "1".
  wp_if_destruct.
  { iApply "HΦ".
    iDestruct "Hgenie1" as "[_ Hgenie]".
    iIntros "!>". iSplit. { by iIntros (?). }
    iNamed 1.
    by iApply "Hgenie". }
  iDestruct "Hgenie1" as "[Hgenie1 _]".
  iDestruct ("Hgenie1" with "[//]") as "#Hgenie1".

  iNamedSuffix "Hown_sigDig0" "0". iNamedSuffix "Hown_sigDig1" "1".
  do 4 wp_loadField.
  wp_if_destruct.
  { iApply "HΦ".
    iIntros "!>". iSplit. { by iIntros (?). }
    by iNamed 1. }

  do 4 wp_loadField.
  wp_apply std_proof.wp_BytesEqual; [iFrame "#"|]. iIntros "_".
  iApply "HΦ".
  case_bool_decide.
  - iSplit. { by iIntros (?). }
    by iNamed 1.
  - iSplit; [|naive_solver].
    iIntros "_". iFrame "#%".
Qed.

End proof.
