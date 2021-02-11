From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc nondet kv_proof fmcounter_map wpc_proofmode common_proof rpc_durable_proof.
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

(* Need this fupd to be OK to fire with any sequence number larger than the *)
Definition rpc_atomic_pre_fupd_def γrpc (cid seq:u64) R : iProp Σ :=
  (own γrpc.(proc) (Excl ()) -∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq ={rpcReqInvUpToN seq}=∗ own γrpc.(proc) (Excl ()) ∗ R)%I.

Definition rpc_atomic_pre_fupd_aux : seal (@rpc_atomic_pre_fupd_def). Proof. by eexists. Qed.
Definition rpc_atomic_pre_fupd := rpc_atomic_pre_fupd_aux.(unseal).
Local Definition rpc_atomic_pre_fupd_eq : @rpc_atomic_pre_fupd = @rpc_atomic_pre_fupd_def := rpc_atomic_pre_fupd_aux.(seal_eq).

Notation "|RN={ γrpc , cid , seq }=> R" :=
 (rpc_atomic_pre_fupd γrpc cid seq R)
 (at level 20, right associativity)
  : bi_scope.

(* This gives the rpc_atomic_pre_fupd for any sequence number that the client can take on
   This is the precondition for ck.MakeRequest(args), where ck has the given cid *)
Definition rpc_atomic_pre_def γrpc cid R : iProp Σ :=
  cid fm[[γrpc.(cseq)]]≥ 0 -∗ (∃ seq,
    cid fm[[γrpc.(cseq)]]≥ int.nat seq ∗
        <disc> (|RN={γrpc,cid,seq}=> R)).
(*   (∀ seq, cid fm[[γrpc.(cseq)]]↦ int.nat seq -∗
    cid fm[[γrpc.(cseq)]]↦ int.nat seq ∗
    (laterable.make_laterable (|RN={γrpc , cid , seq}=> R))).
   *)

Definition rpc_atomic_pre_aux : seal (@rpc_atomic_pre_def). Proof. by eexists. Qed.
Definition rpc_atomic_pre := rpc_atomic_pre_aux.(unseal).
Local Definition rpc_atomic_pre_eq : @rpc_atomic_pre = @rpc_atomic_pre_def := rpc_atomic_pre_aux.(seal_eq).

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

  iMod (fupd_intro_mask' _ _) as "Hclose"; last iMod "HmodP" as "[Hγproc HP]".
  {
    admit. (* property of masks *)
  }
  iDestruct ("HwandQ" with "HP") as "HmodQ".
  iMod "Hclose" as "_".
  iDestruct ("HmodQ" with "Hγproc Hlb") as ">HmodQ".
  iFrame.
  by iModIntro.
Admitted.

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
  rewrite rpc_atomic_pre_eq.
  iIntros "Htype".
  iSpecialize ("HatomicP" with "Htype").
  iDestruct "HatomicP" as (seq) "[#Hlb HmodP]".
  iDestruct ("HPQ") as (seq2) "[#Hlb2 HPQ]".
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
  <disc> (P -∗ Q) -∗ (|PN={γrpc,cid}=> P -∗ |PN={γrpc,cid}=> Q).
Proof.
  iIntros "HPmodQ HmodP".
  rewrite rpc_atomic_pre_eq.
  iIntros "Htype".
  iSpecialize ("HmodP" with "Htype").
  iDestruct "HmodP" as (seq) "[#Hlb HmodP]".
  iExists seq. iFrame "#".
  iModIntro.
  iMod "HmodP".
  iDestruct ("HPmodQ" with "HmodP") as "HmodQ".
  by iModIntro.
Qed.

Lemma modality_pnfupd_mixin γrpc cid :
    modality_mixin (rpc_atomic_pre γrpc cid)
                   (MIEnvId)
                   (MIEnvTransform (IntoDiscrete)).
  Proof.
    split; simpl; eauto.
    - rewrite rpc_atomic_pre_eq.
      iIntros (P) "#HP #Htype".
      iExists (U64 0).
      replace (int.nat 0%Z) with (0) by word.
      iFrame "#".
      iModIntro. iModIntro. done.
    - rewrite /IntoDiscrete//=.
      rewrite rpc_atomic_pre_eq.
      iIntros (P Q HPQ) "HP Htype".
      iExists (U64 0).
      replace (int.nat 0%Z) with (0) by word.
      iFrame "Htype".
      iDestruct (HPQ with "HP") as "HQ".
      iModIntro. by iModIntro.
    - iIntros (_).
      rewrite rpc_atomic_pre_eq.
      iIntros "Htype". iExists (U64 0).
      replace (int.nat 0%Z) with (0) by word.
      iFrame "Htype".
      by repeat iModIntro.
    - iIntros (?? HPQ). iApply pnfupd_wand. iModIntro. iApply HPQ.
    - iIntros (??).
      iIntros "[HP HQ]".
      rewrite rpc_atomic_pre_eq.
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
Global Instance from_modal_pnfupd γrpc cid P :
  FromModal (modality_pnfupd γrpc cid) (|PN={γrpc,cid}=> P) (|PN={γrpc,cid}=> P) P | 2.
Proof. by rewrite /FromModal. Qed.

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
  int.nat (word.add req.(Req_Seq) 1) = int.nat req.(Req_Seq) + 1 →
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
  □(▷Q -∗ (rpc_atomic_pre_fupd γrpc cid seqno (▷ PreCond ∨ ▷ ∃ ret:u64, PostCond ret))) -∗
  neutralized_pre γrpc cid Q (PostCond) -∗
  neutralized_pre γrpc cid PreCond PostCond.
Proof.
  iIntros "#Hseqno_lb #Hwand Hatomic_pre".
  iApply rpc_atomic_pre_mono_strong; last done.
  iExists seqno; iFrame "#".
  iModIntro.
  iIntros "[HQ|Hpost]".
  { iMod ("Hwand" with "HQ") as "HQ"; last by iModIntro. }
  { iModIntro. by iRight. }
Qed.

Definition neutralized_fupd γrpc cid seqno PreCond PostCond : iProp Σ :=
  |RN={γrpc,cid,seqno}=> (▷ PreCond ∨ ▷ ∃ ret:u64, PostCond ret)%I.

Lemma post_neutralize_instantiate γrpc cid seqno P :
  RPCClient_own γrpc cid seqno -∗
  |PN={γrpc,cid}=> P ={⊤}=∗
  RPCClient_own γrpc cid seqno ∗
  |RN={γrpc,cid,seqno}=> P.
Proof.
  iIntros "Hcrpc HmodP".
  rewrite rpc_atomic_pre_eq.
  iDestruct (fmcounter_map_get_lb with "Hcrpc") as "#Htype".
  iSpecialize ("HmodP" with "[Htype]").
  { iApply (fmcounter_map_mono_lb with "Htype"). word. }
  iDestruct ("HmodP") as (seq) "[#Hlb HmodP]".
  iDestruct (fmcounter_map_agree_lb with "Hcrpc Hlb") as %Hineq.
  iFrame.
  iDestruct (own_disc_fupd_elim with "HmodP") as "HH".
  iMod "HH".
  iModIntro. iMod "HH". by iModIntro.
Qed.

End rpc_neutralization.
