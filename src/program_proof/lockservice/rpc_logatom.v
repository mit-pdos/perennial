From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import disk_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc fmcounter_map.
Require Import Decimal Ascii String DecimalString.
From Perennial.goose_lang Require Import ffi.grove_ffi.

Section rpc_namespace.

Definition rpcReqInvUpToN_list (seqno:u64) : list coPset :=
 ((λ (n:nat), ↑rpcRequestInvN {| Req_CID:= 0; Req_Seq:=(U64 n) |} ) <$> (seq 0 (int.nat seqno))).
Definition rpcReqInvUpToN (seqno:u64) : coPset :=
 ⋃ rpcReqInvUpToN_list seqno.

(*
Definition rpcReqInvUpToN (seqno:u64) : coPset :=
  [^union list] x ∈ (seq 0 (int.nat seqno)), ↑rpcRequestInvN {| Req_CID:= 0; Req_Seq:=(U64 (Z.of_nat x)) |}. *)

Lemma rpcReqInvUpToN_prop cid seq :
  ∀ seq', int.nat seq' < int.nat seq → (↑rpcRequestInvN {|Req_CID:=cid; Req_Seq:=seq' |}) ⊆ rpcReqInvUpToN seq.
Proof.
  intros seq' Hineq.
  enough (↑rpcRequestInvN {| Req_CID := cid; Req_Seq := seq' |} ∈ rpcReqInvUpToN_list seq).
  {
    intros x Hxin.
    rewrite elem_of_union_list.
    eauto.
  }
  unfold rpcReqInvUpToN_list.
  eapply (elem_of_fmap_2_alt _ _ (int.nat seq')).
  2:{
    unfold rpcRequestInvN.
    simpl.
    replace (U64 (Z.of_nat (int.nat seq'))) with (seq'); first done.
    admit.
  }
  admit.
Admitted.

Lemma rpcReqInvUpToN_prop_2 cid seq :
 ∀ seq', int.nat seq' ≥ int.nat seq → ↑rpcRequestInvN {|Req_CID:=cid; Req_Seq:=seq' |} ## rpcReqInvUpToN seq.
Admitted.

End rpc_namespace.

Section rpc_atomic_pre.
Context `{!heapG Σ}.
Context `{!rpcG Σ u64}.

(* This fupd grants resources R post-neutralization of the given sequence number *)
Definition rpc_atomic_pre_fupd_def γrpc (cid seq:u64) R : iProp Σ :=
  (own γrpc.(proc) (Excl ()) -∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq ={rpcReqInvUpToN seq}=∗ own γrpc.(proc) (Excl ()) ∗ R)%I.

Definition rpc_atomic_pre_fupd_aux : seal (@rpc_atomic_pre_fupd_def). Proof. by eexists. Qed.
Definition rpc_atomic_pre_fupd := rpc_atomic_pre_fupd_aux.(unseal).
Local Definition rpc_atomic_pre_fupd_eq : @rpc_atomic_pre_fupd = @rpc_atomic_pre_fupd_def := rpc_atomic_pre_fupd_aux.(seal_eq).

Notation "|RN={ γrpc , cid , seq }=> R" :=
 (rpc_atomic_pre_fupd γrpc cid seq R)
 (at level 20, right associativity)
  : bi_scope.

(* This says that R is available under an rnfupd with some sequence number that
   lower-bounds the client sequence number.

   This additionally has a <disc> in front of it, so it can be kept after crashes.
   The precondition fm[[...]]≥ 0 is simply there to make it possible to
   introduce this in front of arbitrary resources.
   *)
Definition rpc_atomic_pre_def γrpc cid R : iProp Σ :=
  <disc> (cid fm[[γrpc.(cseq)]]≥ 0 -∗ (∃ seq,
    cid fm[[γrpc.(cseq)]]≥ int.nat seq ∗
        <disc> (|RN={γrpc,cid,seq}=> R))).
(*   (∀ seq, cid fm[[γrpc.(cseq)]]↦ int.nat seq -∗
    cid fm[[γrpc.(cseq)]]↦ int.nat seq ∗
    (laterable.make_laterable (|RN={γrpc , cid , seq}=> R))).
   *)

Definition rpc_atomic_pre_aux : seal (@rpc_atomic_pre_def). Proof. by eexists. Qed.
Definition rpc_atomic_pre := rpc_atomic_pre_aux.(unseal).
Local Definition rpc_atomic_pre_eq : @rpc_atomic_pre = @rpc_atomic_pre_def := rpc_atomic_pre_aux.(seal_eq).

Global Instance rpc_atomic_pre_disc γrpc cid R : (Discretizable (rpc_atomic_pre γrpc cid R)).
Proof.
  rewrite rpc_atomic_pre_eq /Discretizable.
  unfold rpc_atomic_pre_def.
  iIntros "HH".
  rewrite own_discrete_fupd_eq.
  unfold own_discrete_fupd_def.
  iDestruct (own_discrete_idemp with "HH") as "HH".
  done.
Qed.

Notation "|PN={ γrpc , cid }=> R" :=
 (rpc_atomic_pre γrpc cid R)
 (at level 20, right associativity)
  : bi_scope.

Lemma rpc_atomic_pre_fupd_mono_strong γrpc cid seq P Q:
  (P -∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq -∗
     own γrpc.(proc) (Excl ())={rpcReqInvUpToN seq}=∗ own γrpc.(proc) (Excl ()) ∗ Q) -∗
  |RN={γrpc,cid,seq}=> P -∗
  |RN={γrpc,cid,seq}=> Q.
Proof.
  rewrite rpc_atomic_pre_fupd_eq.
  iIntros "HPQ HfupdP Hγproc #Hlb".
  iMod ("HfupdP" with "Hγproc Hlb") as "[Hγproc HP]".
  iSpecialize ("HPQ" with "HP Hlb Hγproc").
  iMod "HPQ".
  iFrame.
  by iModIntro.
Qed.

Lemma modality_rpc_atomic_mixin γrpc cid seq :
  modality_mixin (rpc_atomic_pre_fupd γrpc cid seq ) MIEnvId MIEnvId.
Proof.
  split; simpl; eauto.
  { iIntros (P) "#HP".
    rewrite rpc_atomic_pre_fupd_eq.
    iIntros "$ _ !#". done. }
  { iIntros (P) "HP".
    rewrite rpc_atomic_pre_fupd_eq.
      by iIntros "$ _ !>". }
  { iIntros.
    rewrite rpc_atomic_pre_fupd_eq.
    iIntros "$ _". by iModIntro. }
  {
    iIntros (P Q).
    intros HPQ.
    iApply rpc_atomic_pre_fupd_mono_strong.
    iIntros "HP _ $".
    iModIntro.
    by iApply HPQ.
  }
  {
    iIntros (P Q) "[HP HQ]".
    rewrite rpc_atomic_pre_fupd_eq.
    iIntros "Hγproc #Hlb".
    iDestruct ("HP" with "Hγproc Hlb") as ">[Hγproc $]".
    iDestruct ("HQ" with "Hγproc Hlb") as ">[$ $]".
    by iModIntro.
  }
Qed.

Definition modality_rpc_atomic γrpc cid seq :=
  Modality _ (modality_rpc_atomic_mixin γrpc cid seq).

(* IPM typeclasses for rnfupd *)
Global Instance from_modal_rpc_atomic γrpc cid seq P :
  FromModal (modality_rpc_atomic γrpc cid seq) (|RN={γrpc,cid,seq}=> P) (|RN={γrpc,cid,seq}=> P) P | 2.
Proof. by rewrite /FromModal. Qed.

Global Instance elim_modal_rpc_atomic γrpc p cid seq' seq P Q :
  ElimModal (int.nat seq' ≤ int.nat seq) p false (|RN={γrpc,cid,seq'}=> P) P (|RN={γrpc,cid,seq}=> Q) (|RN={γrpc,cid,seq}=> Q).
Proof.
  rewrite /ElimModal.
  simpl.
  rewrite rpc_atomic_pre_fupd_eq.
  iIntros (Hineq) "[HmodP HwandQ] Hγproc #Hlb".
  iDestruct (intuitionistically_if_elim with "HmodP") as "HmodP".
  iDestruct ("HmodP" with "Hγproc [Hlb]") as "HmodP".
  {
    iApply (fmcounter_map_mono_lb); last done.
    word.
  }

  iMod (fupd_mask_subseteq _) as "Hclose"; last iMod "HmodP" as "[Hγproc HP]".
  {
    admit. (* property of masks *)
  }
  iDestruct ("HwandQ" with "HP") as "HmodQ".
  iMod "Hclose" as "_".
  iDestruct ("HmodQ" with "Hγproc Hlb") as ">HmodQ".
  iFrame.
  by iModIntro.
Admitted.

Global Instance elim_modal_fupd_rpc_atomic p E γrpc cid seq P Q :
  ElimModal (E ⊆ rpcReqInvUpToN seq) p false (|={E}=> P) P (|RN={γrpc,cid,seq}=> Q) (|RN={γrpc,cid,seq}=> Q).
Proof.
  rewrite /ElimModal.
  simpl.
  rewrite rpc_atomic_pre_fupd_eq.
  iIntros (Hineq) "[HmodP HwandQ] Hγproc #Hlb".
  iDestruct (intuitionistically_if_elim with "HmodP") as "HmodP".

  iMod (fupd_mask_subseteq _) as "Hclose"; last iMod "HmodP".
  {
    done.
  }
  iMod "Hclose" as "_".
  iDestruct ("HwandQ" with "HmodP Hγproc Hlb") as ">HmodQ".
  iFrame.
  by iModIntro.
Qed.

(* If it can be eliminated with a fupd with the specified mask, it can be eliminated with the rnfupd *)
Global Instance elim_modal_fupd_rpc_atomic_forwarding γrpc cid seq p q φ P P' R E:
  (∀ Q, ElimModal φ p q P P' (|={E, rpcReqInvUpToN seq}=> Q) (|={E, rpcReqInvUpToN seq}=> Q))→
  ElimModal (φ ∧ E ⊆ rpcReqInvUpToN seq)  p q P P' (|RN={γrpc,cid,seq}=> R)
            (|RN={γrpc,cid,seq}=> R).
Proof.
  intros Helim.
  rewrite rpc_atomic_pre_fupd_eq.
  rewrite /ElimModal.
  iIntros (Hφ) "[HP Hwand]".
  iIntros "Hγproc Hlb".
  iMod (fupd_mask_subseteq E) as "Hclose".
  {
    naive_solver.
  }

  iApply Helim; first naive_solver.
  iFrame "HP". iIntros "HP'".
  iSpecialize ("Hwand" with "HP' Hγproc Hlb").
  by iMod "Hclose".
Qed.

Global Instance into_wand_rpc_atomic γrpc cid seq p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|RN={γrpc,cid,seq}=> P) (|RN={γrpc,cid,seq}=> Q).
Proof.
  rewrite /IntoWand' /IntoWand /=.
  intros.
  iIntros "HR HmodP".
  iDestruct (H with "HR") as "HwandQ".
  iDestruct (intuitionistically_if_elim with "HmodP") as "HmodP".
  iMod "HmodP".
  iModIntro.
  by iApply "HwandQ".
Qed.

Global Instance from_sep_rpc_atomic γrpc cid seq P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|RN={γrpc,cid,seq}=> P) (|RN={γrpc,cid,seq}=> Q1) (|RN={γrpc,cid,seq}=> Q2).
Proof.
  rewrite /FromSep.
  intros Hsep.
  iIntros "[H1 H2]".
  iApply Hsep.
  (* Make a lemma for this. *)

  rewrite rpc_atomic_pre_fupd_eq.
  iIntros "Hγproc #Hlb".
  iDestruct ("H1" with "Hγproc Hlb") as ">[Hγproc $]".
  iDestruct ("H2" with "Hγproc Hlb") as ">[$ $]".
    by iModIntro.
Qed.

(* IPM typeclasses for pnfupd *)

Lemma rpc_atomic_pre_mono_strong cid γrpc P Q :
  (∃ seq, cid fm[[γrpc.(cseq)]]≥ int.nat seq ∗ <disc>(P -∗ |RN={γrpc,cid,seq}=> Q )) -∗
  |PN={γrpc,cid}=> P -∗
  |PN={γrpc,cid}=> Q.
Proof.
  iIntros "HPQ HatomicP".
  iDestruct ("HPQ") as (seq2) "[#Hlb2 HPQ]".
  iDestruct (own_disc_fupd_idemp with "HPQ") as "HPQ".
  rewrite rpc_atomic_pre_eq.
  iModIntro.
  iIntros "Htype".
  iSpecialize ("HatomicP" with "Htype").
  iDestruct "HatomicP" as (seq) "[#Hlb HmodP]".
  destruct (decide (int.nat seq < int.nat seq2)).
  - iExists (seq2). iFrame "Hlb2".
    iModIntro. iMod "HmodP"; first by word.
    iDestruct ("HPQ" with "HmodP") as "$".
  - iExists (seq). iFrame "Hlb".
    iModIntro. iMod "HmodP".
    iSpecialize ("HPQ" with "HmodP").
    iMod "HPQ"; first by word.
    by iModIntro.
Qed.

Lemma pnfupd_wand γrpc cid P Q:
  <disc> (P -∗ ◇ Q) -∗ (|PN={γrpc,cid}=> P -∗ |PN={γrpc,cid}=> Q).
Proof.
  iIntros "HPmodQ HmodP".
  iDestruct (own_disc_fupd_idemp with "HPmodQ") as "HPmodQ".
  rewrite rpc_atomic_pre_eq.
  iModIntro.
  iIntros "Htype".
  iSpecialize ("HmodP" with "Htype").
  iDestruct "HmodP" as (seq) "[#Hlb HmodP]".
  iExists seq. iFrame "#".
  iModIntro.
  iMod "HmodP".
  iDestruct ("HPmodQ" with "HmodP") as ">HmodQ".
  by iModIntro.
Qed.

Class IntoPostNeutralize γrpc cid (P Q : iProp Σ) :=
  into_post_neutralize : (bi_entails P (|PN={γrpc,cid}=> Q)).

Arguments IntoPostNeutralize _ _ _%I _%I.
Arguments into_post_neutralize _ _ _%I _%I {_}.
Hint Mode IntoPostNeutralize + + ! - : typeclass_instances.

Global Instance IntoDiscretePostNeutralize γrpc cid (P Q : iProp Σ) :
 IntoDiscrete P Q → IntoPostNeutralize γrpc cid P (Q).
Proof.
  intros HPQ.
  rewrite /IntoPostNeutralize.
  iIntros "HP".
  rewrite /IntoDiscrete in HPQ.
  iDestruct (HPQ with "HP") as "HQ".
  iDestruct (own_discrete_idemp with "HQ") as "HQ".
  rewrite rpc_atomic_pre_eq.
  iModIntro.
  iIntros "Htype".
  iExists (U64 0).
  iFrame.
  iModIntro.
  by iModIntro.
Qed.

Global Instance post_neutralize_into_post_neutralize γrpc cid P :
       IntoPostNeutralize γrpc cid (|PN={γrpc,cid}=> P) P.
Proof. done. Qed.

Lemma modality_pnfupd_mixin γrpc cid :
    modality_mixin (rpc_atomic_pre γrpc cid)
                   (MIEnvId)
                   (MIEnvTransform (IntoPostNeutralize γrpc cid)).
  Proof.
    split; simpl; eauto.
    - rewrite rpc_atomic_pre_eq.
      iIntros (P) "#HP !> #Htype".
      iExists (U64 0).
      iFrame "#".
      iModIntro. iModIntro. done.
    - iIntros (_).
      rewrite rpc_atomic_pre_eq.
      iModIntro. iIntros "Htype". iExists (U64 0).
      iFrame "Htype".
      by repeat iModIntro.
    - iIntros (?? HPQ). iApply pnfupd_wand. iModIntro. iIntros. iModIntro. iApply HPQ. done.
    - iIntros (??).
      iIntros "[HP HQ]".
      rewrite rpc_atomic_pre_eq.
      iModIntro.
      iIntros "#Htype".
      iSpecialize ("HP" with "Htype").
      iSpecialize ("HQ" with "Htype").
      iDestruct "HP" as (seq1) "[#Hlb1 HP]".
      iDestruct "HQ" as (seq2) "[#Hlb2 HQ]".
      destruct (decide (int.nat seq1 < int.nat seq2)).
      + iExists seq2. iFrame "#". iModIntro.
        iMod "HP"; first by word.
        iMod "HQ".
        iModIntro. iFrame.
      + iExists seq1. iFrame "#". iModIntro.
        iMod "HQ"; first by word.
        iMod "HP".
        iModIntro. iFrame.
Qed.

Definition modality_pnfupd γrpc cid :=
  Modality _ (modality_pnfupd_mixin γrpc cid).

(* IPM typeclasses for rnfupd *)
(* Want to keep diamond around to eliminate laters on timeless resources; if we could iMod away pnfupds, then we could also make it so that laters could be iMod'd away *)
Global Instance from_modal_pnfupd γrpc cid P :
  FromModal (modality_pnfupd γrpc cid) (|PN={γrpc,cid}=> P) (|PN={γrpc,cid}=> P) (◇ P) | 2.
Proof.
  rewrite /FromModal //=.
  iIntros "HP".
  rewrite rpc_atomic_pre_eq.
  iModIntro.
  iIntros "#Htype".
  iDestruct ("HP" with "Htype") as (seq) "[#Hlb HP]".
  iExists seq.
  iFrame "#".
  iModIntro.
  iMod "HP".
  iMod "HP".
  by iModIntro.
Qed.

End rpc_atomic_pre.

Notation "|RN={ γrpc , cid , seq }=> R" :=
 (rpc_atomic_pre_fupd γrpc cid seq R)
 (at level 20, right associativity)
  : bi_scope.

Notation "|PN={ γrpc , cid }=> R" :=
 (rpc_atomic_pre γrpc cid R)
 (at level 20, right associativity)
  : bi_scope.

Section rpc_neutralization.

Context `{!heapG Σ}.
Context `{!rpcG Σ u64}.
Definition neutralized_pre γrpc cid PreCond PostCond : iProp Σ :=
  |PN={γrpc,cid}=> (▷ PreCond ∨ ▷ ∃ ret:u64, PostCond ret)%I.

Lemma neutralize_request (req:RPCRequestID) γrpc γreq (PreCond:iProp Σ) PostCond  :
  (int.nat (word.add req.(Req_Seq) 1) = int.nat req.(Req_Seq) + 1)%nat →
  is_RPCServer γrpc -∗
  is_RPCRequest γrpc γreq PreCond PostCond req -∗
  (RPCRequest_token γreq) ={⊤}=∗
  <disc> neutralized_pre γrpc req.(Req_CID) PreCond PostCond.
Proof.
    iIntros "%HincrSafe #Hsrpc #His_req Hγpost".
    iFrame "#∗".


    iInv "His_req" as "[>#Hcseq_lb_strict HN]" "HNClose".
    iMod ("HNClose" with "[$Hcseq_lb_strict $HN]") as "_".

    iModIntro.
    iModIntro.
    rewrite /neutralized_pre rpc_atomic_pre_eq.
    iModIntro.
    iIntros "_".
    iExists (word.add req.(Req_Seq) 1). (* Needs to be one larger *)
    iSplitL "Hcseq_lb_strict".
    { iApply (fmcounter_map_mono_lb with "Hcseq_lb_strict"). word. }
    iModIntro.

    rewrite rpc_atomic_pre_fupd_eq.
    unfold rpc_atomic_pre_fupd_def.
    iIntros "Hγproc #Hlb".

    iInv "His_req" as "HN" "HNClose".
    { apply (rpcReqInvUpToN_prop req.(Req_CID)). destruct req. simpl in *. word. }
    iDestruct "HN" as "[#>_ [HN|HN]]"; simpl. (* Is cseq_lb_strict relevant for this? *)
    {
      iDestruct "HN" as "[_ [>Hbad|HN]]".
      { iDestruct (own_valid_2 with "Hbad Hγproc") as %?; contradiction. }

      iMod ("HNClose" with "[Hγpost]") as "_".
      {
        iNext. iFrame "Hcseq_lb_strict". iRight. iFrame "#∗".
        iApply (fmcounter_map_mono_lb with "Hlb").
        word.
      }
      iFrame.
      iModIntro.
      iLeft.
      iNext.
      iDestruct "HN" as "[_ $]".
    }
    {
      iDestruct "HN" as "[#Hlseq_lb_req HN]".
      iDestruct "HN" as "[>Hbad|Hreply_post]".
      { by iDestruct (own_valid_2 with "Hγpost Hbad") as %Hbad. }
      iMod ("HNClose" with "[Hγpost]") as "_".
      {
        iNext.
        iFrame "Hcseq_lb_strict".
        iRight.
        iFrame "# ∗".
      }
      iDestruct "Hreply_post" as (last_reply) "[#Hreply Hpost]".
      iModIntro.
      iFrame.
      iRight.
      iExists _; iFrame.
    }
Qed.

Lemma neutralize_idemp γrpc cid seqno Q PreCond PostCond :
  cid fm[[γrpc.(cseq)]]≥ int.nat seqno -∗
  □(▷Q -∗ |RN={γrpc,cid,seqno}=> PreCond) -∗
  neutralized_pre γrpc cid Q (PostCond) -∗
  neutralized_pre γrpc cid PreCond PostCond.
Proof.
  iIntros "#Hseqno_lb #Hwand Hatomic_pre".
  iApply rpc_atomic_pre_mono_strong; last done.
  iExists seqno; iFrame "#".
  iModIntro.
  iIntros "[HQ|Hpost]".
  { iDestruct ("Hwand" with "HQ") as ">HQ". iModIntro. iLeft. iNext. done. }
  { iModIntro. by iRight. }
Qed.

Definition neutralized_fupd γrpc cid seqno PreCond PostCond : iProp Σ :=
  |RN={γrpc,cid,seqno}=> (▷ PreCond ∨ ▷ ∃ ret:u64, PostCond ret)%I.

Lemma post_neutralize_instantiate γrpc cid seqno P :
  RPCClient_own γrpc cid seqno -∗
  |PN={γrpc,cid}=> P ={⊤}=∗
  RPCClient_own γrpc cid seqno ∗
  <disc> |RN={γrpc,cid,seqno}=> P.
Proof.
  iIntros "Hcrpc HmodP".
  rewrite rpc_atomic_pre_eq.
  iDestruct (fmcounter_map_get_lb with "Hcrpc") as "#Htype".
  iDestruct (own_disc_fupd_elim with "HmodP") as ">HmodP".
  iModIntro.
  iSpecialize ("HmodP" with "[Htype]").
  { iApply (fmcounter_map_mono_lb with "Htype"). word. }
  iDestruct ("HmodP") as (seq) "[#Hlb HmodP]".
  iDestruct (fmcounter_map_agree_lb with "Hcrpc Hlb") as %Hineq.
  iFrame.
  iModIntro.
  iMod "HmodP"; first by word.
  by iModIntro.
Qed.

Lemma rnfupd_disc_laterable γrpc cid seqno P :
  <disc> |RN={γrpc,cid,seqno}=> P -∗
  ∃ Q, Q ∗ □(▷ Q -∗ ◇ Q) ∗ □(Q -∗ <disc> Q) ∗ □(▷ Q -∗ |RN={γrpc,cid,seqno}=> P).
Proof.
  iIntros "HrnfupdP".
  iEval (rewrite own_discrete_fupd_eq /own_discrete_fupd_def) in "HrnfupdP".
  rewrite own_discrete_eq /own_discrete_def.
  iDestruct "HrnfupdP" as (a Ha) "[Hown #Hwand]".

  iExists (uPred_ownM a)%I.
  iFrame.
  iSplit.
  { iModIntro. iIntros ">$". }
  iSplit.
  { iModIntro. iIntros. iModIntro. done. }
  iModIntro.
  iIntros ">Hown".
  iDestruct ("Hwand" with "Hown") as "Hrnfupd".
  rewrite rpc_atomic_pre_fupd_eq.
  iIntros "Hγproc #Hlb".
  iDestruct (fupd_level_fupd with "Hrnfupd") as "Hrnfupd".
  iMod (fupd_mask_subseteq _) as "Hclose"; last iMod "Hrnfupd".
  { set_solver. }
  iMod "Hclose".
  iDestruct ("Hrnfupd" with "Hγproc Hlb") as ">[$ $]".
  by iModIntro.
Qed.

End rpc_neutralization.
