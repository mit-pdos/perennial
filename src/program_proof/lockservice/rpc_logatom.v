From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc nondet kv_proof fmcounter_map wpc_proofmode common_proof rpc_durable_proof.
Require Import Decimal Ascii String DecimalString.
From Perennial.goose_lang Require Import ffi.grove_ffi.

Section rpc_logatom_proof.
Context `{!heapG Σ}.
Context `{!rpcG Σ u64}.


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


(* Need this fupd to be OK to fire with any sequence number larger than the *)
Definition rpc_atomic_pre_fupd γrpc (cid seq:u64) R : iProp Σ :=
  (own γrpc.(proc) (Excl ()) -∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq ={rpcReqInvUpToN seq}=∗ own γrpc.(proc) (Excl ()) ∗ R)%I.

Notation "|RN={ γrpc , cid , seq }=> R" :=
 (rpc_atomic_pre_fupd γrpc cid seq R)
 (at level 20, right associativity)
  : bi_scope.

(* This gives the rpc_atomic_pre_fupd for any sequence number that the client can take on
   This is the precondition for ck.MakeRequest(args), where ck has the given cid *)
Definition rpc_atomic_pre γrpc cid R : iProp Σ :=
    <bdisc> (∀ seq, cid fm[[γrpc.(cseq)]]↦ int.nat seq ={⊤}=∗
    cid fm[[γrpc.(cseq)]]↦ int.nat seq ∗
   (laterable.make_laterable (|RN={γrpc , cid , seq}=> R))).

Lemma rpc_atomic_pre_fupd_mono_strong γrpc cid seq P Q:
  (P -∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq -∗
     own γrpc.(proc) (Excl ())={rpcReqInvUpToN seq}=∗ own γrpc.(proc) (Excl ()) ∗ Q) -∗
  |RN={γrpc,cid,seq}=> P -∗
  |RN={γrpc,cid,seq}=> Q.
Proof.
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
  {
    iIntros (P) "#HP".
    iIntros "$ _ !#".
    done.
  }
  {
    iIntros (P) "HP".
    by iIntros "$ _ !>".
  }
  {
    iIntros. iIntros "$ _".
    by iModIntro.
  }
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
    iIntros "Hγproc #Hlb".
    iDestruct ("HP" with "Hγproc Hlb") as ">[Hγproc $]".
    iDestruct ("HQ" with "Hγproc Hlb") as ">[$ $]".
    by iModIntro.
  }
Qed.
Definition modality_rpc_atomic γrpc cid seq :=
  Modality _ (modality_rpc_atomic_mixin γrpc cid seq).

(** FromModal *)
Global Instance from_modal_rpc_atomic γrpc cid seq P :
  FromModal (modality_rpc_atomic γrpc cid seq) (|RN={γrpc,cid,seq}=> P) (|RN={γrpc,cid,seq}=> P) P | 2.
Proof. by rewrite /FromModal. Qed.

Global Instance elim_modal_rpc_atomic γrpc cid seq' seq P Q :
  ElimModal (int.nat seq' ≤ int.nat seq) false false (|RN={γrpc,cid,seq'}=> P) P (|RN={γrpc,cid,seq}=> Q) (|RN={γrpc,cid,seq}=> Q).
Proof.
  rewrite /ElimModal.
  simpl.
  iIntros (Hineq) "[HmodP HwandQ] Hγproc #Hlb".
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

Lemma rpc_atomic_pre_mono_strong cid γrpc P Q :
  □(∀ seq, P -∗ |RN={γrpc,cid,seq}=> Q) -∗
  rpc_atomic_pre γrpc cid P -∗
  rpc_atomic_pre γrpc cid Q.
Proof.
  iIntros "#HPQ HatomicP".
  iModIntro.
  iIntros (seq) "Hcown".
  iMod ("HatomicP" $! seq with "Hcown") as "[Hcown HatomicP]".
  iFrame.
  unfold laterable.make_laterable.
  iDestruct "HatomicP" as (R) "[HR #HatomicP]".
  iExists (R). iFrame.
  iModIntro.
  iModIntro.
  iIntros "HR".
  iMod ("HatomicP" with "HR") as "HP".
  iDestruct ("HPQ" with "HP") as "$".
Qed.

(*
Lemma rpc_atomic_pre_fupd_mono γrpc cid seq P Q:
  (P -∗ Q) -∗
  rpc_atomic_pre_fupd γrpc cid seq P -∗
  rpc_atomic_pre_fupd γrpc cid seq Q.
Proof.
  iIntros "HPQ".
  iApply rpc_atomic_pre_fupd_mono_strong.
  iIntros "HP _ $".
  by iApply "HPQ".
Qed.

Lemma rpc_atomic_pre_mono cid γrpc P Q :
  <bdisc>(P -∗ Q) -∗
  rpc_atomic_pre γrpc cid P -∗
  rpc_atomic_pre γrpc cid Q.
Proof.
  iIntros "HPQ HatomicP".
  iModIntro.
  iIntros (seq) "Hcown".
  iMod ("HatomicP" $! seq with "Hcown") as "[Hcown HatomicP]".
  iFrame.
  iApply (rpc_atomic_pre_fupd_mono with "HPQ HatomicP").
Qed.
*)

Definition quiesce_fupd γrpc cid seqno PreCond PostCond : iProp Σ :=
  laterable.make_laterable (rpc_atomic_pre_fupd γrpc cid seqno (▷ PreCond ∨ ▷ ∃ ret:u64, PostCond ret))%I.

Definition quiesceable_pre γrpc cid PreCond PostCond : iProp Σ :=
  rpc_atomic_pre γrpc cid (▷ PreCond ∨ ▷ ∃ ret:u64, PostCond ret)%I.

Global Instance quiesceable_pre_disc γrpc cid PreCond PostCond : (Discretizable
       (quiesceable_pre γrpc cid PreCond PostCond)).
Proof.
  rewrite /Discretizable.
  by rewrite -own_discrete_idemp.
Defined.

Lemma quiesce_request (req:RPCRequestID) γrpc γreq (PreCond:iProp Σ) PostCond  :
  is_RPCServer γrpc -∗
  is_RPCRequest γrpc γreq PreCond PostCond req -∗
  (RPCRequest_token γreq) -∗
  quiesceable_pre γrpc req.(Req_CID) PreCond PostCond.
Proof.
    iIntros "#Hsrpc #His_req Hγpost".
    iFrame "#∗".

    iModIntro.

    iIntros (new_seq) "Hcown".
    iInv "His_req" as "[>#Hcseq_lb_strict HN]" "HNClose".
    iMod ("HNClose" with "[$Hcseq_lb_strict $HN]") as "_".

    iDestruct (fmcounter_map_agree_lb with "Hcown Hcseq_lb_strict") as %Hnew_seq.
    iFrame.
    iModIntro.
    iExists (RPCRequest_token γreq).
    iFrame.
    iModIntro.
    iIntros ">Hγpost".

    iIntros "Hγproc #Hlseq_lb".
    iInv "His_req" as "HN" "HNClose".
    { apply (rpcReqInvUpToN_prop req.(Req_CID)). destruct req. simpl in *. word. }
    iDestruct "HN" as "[#>_ [HN|HN]]"; simpl. (* Is cseq_lb_strict relevant for this? *)
    {
      iDestruct "HN" as "[_ [>Hbad|HN]]".
      { iDestruct (own_valid_2 with "Hbad Hγproc") as %?; contradiction. }

      iMod ("HNClose" with "[Hγpost]") as "_".
      { iNext. iFrame "Hcseq_lb_strict". iRight. iFrame.
        iDestruct (fmcounter_map_mono_lb (int.nat req.(Req_Seq)) with "Hlseq_lb") as "$".
        lia.
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

Lemma quiesce_idemp γrpc cid seqno Q PreCond PostCond :
  cid fm[[γrpc.(cseq)]]≥ int.nat seqno -∗
  □(▷Q -∗ (rpc_atomic_pre_fupd γrpc cid seqno (▷ PreCond ∨ ▷ ∃ ret:u64, PostCond ret))) -∗
  quiesceable_pre γrpc cid Q (PostCond) -∗
  quiesceable_pre γrpc cid PreCond PostCond.
Proof.
  iIntros "#Hseqno_lb #Hwand Hatomic_pre".
  iModIntro.
  iIntros (seq) "Hcown".
  iDestruct (fmcounter_map_agree_lb with "Hcown Hseqno_lb") as %Hseqno_ineq.

  iDestruct ("Hatomic_pre" $! seq with "Hcown") as ">[Hcown Hfupd]".
  iFrame.
  unfold laterable.make_laterable.
  iDestruct "Hfupd" as (S) "[HS #Hfupd]".
  iExists S.
  iModIntro.
  iFrame "HS".
  iModIntro.
  iIntros "HS".
  iSpecialize ("Hfupd" with "HS").
  iApply (rpc_atomic_pre_fupd_mono_strong with "[Hwand] Hfupd").
  iIntros "HQR #Hlb Hγproc".
  iDestruct (fmcounter_map_mono_lb (int.nat seqno) with "Hlb") as "#Hlb_seqno".
  { lia. }
  iDestruct "HQR" as "[HQ | HRpost]".
  {
    iDestruct ("Hwand" with "HQ") as "Hfupd".
    iDestruct ("Hfupd" with "Hγproc Hlb_seqno") as "HH".
    (* TODO: Show that mask of seqno is in mask of seq *)
    (* by iModIntro. *)
    admit.
  }
  { iFrame. by iModIntro. }
Admitted.

Lemma quiesce_intro γrpc cid seqno PreCond PostCond :
  PreCond -∗ (quiesce_fupd γrpc cid seqno PreCond PostCond).
Proof.
  iIntros.
  iExists (PreCond)%I.
  iFrame.
  iModIntro; iFrame.
  iIntros.
  iIntros "Hγproc #Hlb".
  iFrame.
    by iModIntro.
Qed.

Definition quiesce_fupd_raw γrpc cid seqno PreCond PostCond : iProp Σ :=
  (rpc_atomic_pre_fupd γrpc cid seqno (▷ PreCond ∨ ▷ ∃ ret:u64, PostCond ret))%I.

Lemma quiesceable_pre_instantiate γrpc cid seqno PreCond PostCond :
  RPCClient_own γrpc cid seqno -∗
  quiesceable_pre γrpc cid PreCond PostCond ={⊤}=∗
  RPCClient_own γrpc cid seqno ∗
  (quiesce_fupd γrpc cid seqno PreCond PostCond).
Proof.
  iIntros "Hcrpc Hqpre".
  iDestruct (own_discrete_elim with "Hqpre") as "Hqpre".
  iMod ("Hqpre" $! seqno with "Hcrpc") as "[Hcrpc Hfupd]".
  iModIntro. iFrame.
Qed.

End rpc_logatom_proof.
