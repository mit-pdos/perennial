From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_protocol.
From Perennial.goose_lang.lib Require Import waitgroup.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_increasecommit_proof pb_apply_proof.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section pb_sendcommitthread_proof.

Context `{!heapGS Σ}.
Context {pb_record:Sm.t}.
Notation OpType := (pb_record.(Sm.OpType)).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).
Notation "server.t" := (server.t (pb_record:=pb_record)).
Notation pbG := (pbG (pb_record:=pb_record)).
Notation get_rwops := (get_rwops (pb_record:=pb_record)).

Context `{!pbG Σ}.

Lemma get_commitIndex_facts st γ γsrv :
  own_Server_ghost_eph_f st γ γsrv -∗
  ∃ σ,
  ⌜int.nat st.(server.committedNextIndex) = length σ⌝ ∗
  is_pb_log_lb γ.(s_pb) σ ∗
  is_proposal_lb γ.(s_pb) st.(server.epoch) σ ∗
  □ committed_log_fact γ st.(server.epoch) σ
.
Proof.
  intros.
  rewrite /own_Server_ghost_eph_f /tc_opaque.
  iNamed 1.
  repeat iExists _; iFrame "Hcommit_lb #".
  iPureIntro. rewrite fmap_length in HcommitLen. word.
Qed.

Lemma wp_Server__increaseCommitThread (s:loc) γ γsrv :
  {{{
        "#Hsrv" ∷ is_Server s γ γsrv
  }}}
    pb.Server__sendIncreaseCommitThread #s
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (?) "Hsrv HΦ".
  iNamed "Hsrv". iNamed "Hsrv".
  wp_call.
  wp_forBreak.
  wp_pures.

  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  wp_pures.
  wp_forBreak_cond.
  iNamed "Hown".
  iNamed "Hvol".
  wp_pures.
  wp_loadField.
  wp_if_destruct.
  { (* not the primary; wait and try again later *)
    wp_pures.
    wp_loadField.
    wp_apply (wp_condWait with "[- HΦ]").
    {
      iFrame "# Hlocked".
      repeat iExists _; iSplitR "HghostEph"; last iFrame.
      repeat iExists _. iFrame "∗#". done.
    }
    iIntros "[Hlocked Hown]".
    wp_pures.
    iLeft. iModIntro.
    eauto with iFrame.
  }
  (* we are the primary, so can send out the new commit index to backups *)
  iRight.
  iModIntro. iSplitR; first done.
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.

  iDestruct (get_commitIndex_facts with "HghostEph") as "#Hpre".
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    repeat (iExists _).
    iSplitR "HghostEph"; last iFrame.
    repeat (iExists _).
    iFrame "Hstate ∗#"; iFrame "%".
  }
  wp_pures.

  (* XXX: copy paste from Apply proof *)
  iDestruct "Hprimary" as "[%Hbad|Hprimary]"; first exfalso.
  { by rewrite Hbad in Heqb. }
  iNamed "Hprimary".
  iMod (readonly_load with "Hclerkss_sl") as (?) "Hclerkss_sl2".

  iDestruct (is_slice_small_sz with "Hclerkss_sl2") as %Hclerkss_sz.
  wp_apply (wp_random).
  iIntros (randint) "_".
  wp_apply wp_slice_len.
  wp_pures.
  set (clerkIdx:=(word.modu randint clerks_sl.(Slice.sz))).

  assert (int.nat clerkIdx < length clerkss) as Hlookup_clerks.
  { (* FIXME: better lemmas about mod? *)
    rewrite Hclerkss_sz.
    unfold clerkIdx.
    rewrite Hclerkss_len in Hclerkss_sz.
    replace (clerks_sl.(Slice.sz)) with (U64 (32)); last first.
    {
      unfold numClerks in Hclerkss_sz.
      word.
    }
    enough (int.Z randint `mod` 32 < int.Z 32)%Z.
    { word. }
    apply Z.mod_pos_bound.
    word.
  }

  assert (∃ clerks_sl_inner, clerkss !! int.nat clerkIdx%Z = Some clerks_sl_inner) as [clerks_sl_inner Hclerkss_lookup].
  {
    apply list_lookup_lt.
    rewrite Hclerkss_len.
    word.
  }

  wp_apply (wp_SliceGet with "[$Hclerkss_sl2]").
  { done. }
  iIntros "Hclerkss_sl2".
  wp_pures.

  wp_apply (wp_NewWaitGroup pbN (λ _, True)%I).
  iIntros (wg γwg) "Hwg".
  wp_pures.

  iDestruct (big_sepL_lookup_acc with "Hclerkss_rpc") as "[Hclerks_rpc _]".
  { done. }
  iNamed "Hclerks_rpc".

  iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks_sl2".
  iDestruct (is_slice_small_sz with "Hclerks_sl2") as %Hclerks_sz.

  wp_apply (wp_forSlice' _ (λ j, (own_WaitGroup pbN wg γwg j _))%I with "[] [$Hwg $Hclerks_sl2]").
  2: {
    iDestruct (big_sepL2_to_sepL_1 with "Hclerks_rpc") as "H2".
    iFrame "H2".
  }
  {
    iIntros (i ck).
    simpl.
    clear Φ.
    iIntros (Φ) "!# (% & %Hlookup & Hϕ & Hwg) HΦ".
    iDestruct "Hϕ" as "(% & (% & #Hck & #Hepoch_lb))".
    wp_pures.
    wp_apply (wp_WaitGroup__Add with "[$Hwg]").
    { rewrite Hclerks_sz in H. word. }
    iIntros "[Hwg Hwg_tok]".
    wp_pures.
    iDestruct (own_WaitGroup_to_is_WaitGroup with "[$Hwg]") as "#His_wg".
    wp_apply (wp_fork with "[Hwg_tok]").
    {
      iNext.
      wp_pures.
      wp_forBreak_cond.
      wp_pures.

      iDestruct "Hpre" as (?) "(% & Hlog_lb & Hprop2 & Hcom)".
      wp_apply (wp_Clerk__IncreaseCommit with "[$Hck]").
      { iFrame "#%". }
      iIntros (err) "_".

      wp_pures.
      wp_if_destruct.
      2:{
        wp_pures.
        iLeft.
        iFrame "∗".
        by iPureIntro.
      }
      iModIntro.
      iRight.
      iSplitR; first done.
      wp_apply (wp_WaitGroup__Done with "[$Hwg_tok $His_wg]").
      { done. }
      done.
    }
    iApply "HΦ".
    iFrame.
  }
  iIntros "Hwg".
  wp_pures.
  wp_apply (wp_WaitGroup__Wait with "[$]").
  iIntros "_".
  wp_pures.
  wp_apply wp_Sleep.
  wp_pures.
  iLeft.
  by iFrame.
Qed.

End pb_sendcommitthread_proof.
