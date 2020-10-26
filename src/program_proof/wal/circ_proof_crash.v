From iris.bi.lib Require Import fractional.
From Perennial.algebra Require Import deletable_heap.

From RecordUpdate Require Import RecordSet.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.program_logic Require Import staged_wpc.
From Perennial.Helpers Require Import Transitions.
From Perennial.goose_lang Require Import crash_modality fmcounter.
From Perennial.Helpers Require Import NamedProps.
From Perennial.program_proof Require Import proof_prelude disk_lib.
From Perennial.program_proof Require Import wal.lib.
From Perennial.program_proof Require Import marshal_block util_proof.
From Perennial.program_proof Require Import circ_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.


Section heap.
Context `{!heapG Σ}.
Context `{!circG Σ}.

Context (N: namespace).
Context (P: circΣ.t -> iProp Σ).

Hint Unfold circ_low_wf : word.
Hint Unfold circΣ.diskEnd : word.

Ltac mod_bound :=
  (* TODO: repeat *)
  match goal with
 | |- context[?x `mod` ?m] =>
   pose proof (Z.mod_bound_pos x m)
  end.

Theorem wpc_recoverCircular stk k E1 d σ γ :
  {{{ is_circular_state γ σ }}}
    recoverCircular #d @ stk; k; E1
  {{{ γ' (c:loc) (diskStart diskEnd: u64) (bufSlice:Slice.t) (upds: list update.t),
      RET (#c, #diskStart, #diskEnd, slice_val bufSlice);
      updates_slice bufSlice upds ∗
      is_circular_state γ' σ ∗
      is_circular_appender γ' c ∗
      start_is γ' (1/2) diskStart ∗
      diskEnd_is γ' (1/2) (int.val diskStart + length upds) ∗
      ⌜σ.(circΣ.start) = diskStart⌝ ∗
      ⌜σ.(circΣ.upds) = upds⌝ ∗
      ⌜circΣ.diskEnd σ = int.val diskEnd⌝
  }}}
  {{{ is_circular_state γ σ }}}.
Proof.
  clear P.
  iIntros (Φ Φc) "Hcs HΦ".

  Opaque struct.t.
  rewrite /recoverCircular.
  wpc_pures; first iFrame.
  { crash_case; eauto. }

  iDestruct "Hcs" as (Hwf) "[Hpos Hcs]".
  iDestruct "Hcs" as (addrs0 blocks0 Hupds) "(Hown & Hlow)".
  iDestruct "Hown" as (Hlow_wf) "[Haddrs Hblocks]".
  iDestruct "Hlow" as (hdr1 hdr2 Hhdr1 Hhdr2) "(Hd0 & Hd1 & Hd2)".

  iCache with "HΦ Hpos Haddrs Hblocks Hd0 Hd1 Hd2".
  { crash_case.
    iFrame "% ∗".
    iExists _, _; iFrame "∗ %".
    iExists _, _; iFrame "∗ %". }

  wpc_apply (wpc_Read with "[Hd0]"); first by iFrame.
  iSplit.
  { iLeft in "HΦ". iModIntro. iNext. iIntros "Hd0". iApply "HΦ".
    iFrame "% ∗".
    iExists _, _; iFrame "∗ %".
    iExists _, _; iFrame "∗ %". }

  iIntros (s0) "!> [Hd0 Hs0]".
  wpc_pures.

  wpc_apply (wpc_Read with "[Hd1]"); first iFrame.
  iSplit.
  { iLeft in "HΦ". iModIntro. iNext. iIntros "Hd1". iApply "HΦ".
    iFrame "% ∗".
    iExists _, _; iFrame "∗ %".
    iExists _, _; iFrame "∗ %". }

  iIntros (s1) "!> [Hd1 Hs1]".
  wpc_pures.

  wpc_bind (decodeHdr1 _).
  wpc_frame.
  iApply slice.is_slice_to_small in "Hs0".
  wp_apply (wp_decodeHdr1 with "Hs0"); [ eauto | word | ].
  iIntros (addrs) "Hdiskaddrs H". iNamed "H".
  wpc_pures.

  wpc_bind (decodeHdr2 _).
  wpc_frame.
  iApply slice.is_slice_to_small in "Hs1".
  wp_apply (wp_decodeHdr2 with "Hs1"); [ eauto | ].
  iNamed 1.

  wpc_pures.
  wpc_frame_seq.
  wp_apply wp_ref_of_zero; eauto.
  iIntros (bufsloc) "Hbufsloc".
  iNamed 1.

  wpc_pures.
  wpc_frame_seq.
  wp_apply wp_ref_to; eauto.
  iIntros (pos) "Hposl".
  iNamed 1.

  wpc_pures.
  wpc_apply (wpc_forUpto (fun i =>
    ⌜int.val σ.(start) <= int.val i⌝ ∗
    (∃ bufSlice,
      bufsloc ↦[slice.T (struct.t Update.S)] (slice_val bufSlice) ∗
      updates_slice bufSlice (take (int.nat i - int.nat σ.(start)) σ.(upds))) ∗
      is_slice_small addrs uint64T 1 addrs0 ∗
      2 d↦∗ blocks0
    )%I
    (fun i => 2 d↦∗ blocks0)%I with "[] [Hbufsloc $Hposl $Hd2 Hdiskaddrs]").
  - word_cleanup.
    destruct Hwf.
    rewrite /circΣ.diskEnd.
    word.
  - iIntros (??) "(H&?&?&?)".
    iModIntro; eauto.
  - iIntros (i Φₗ Φcₗ) "!> (HI&Hposl&%) HΦ".
    iDestruct "HI" as (Hstart_bound) "(Hbufs&Hdiskaddrs&Hd2)".
    iDestruct "Hbufs" as (bufSlice) "[Hbufsloc Hupds]".
    iDestruct (updates_slice_len with "Hupds") as %Hupdslen.

    wpc_pures.
    { crash_case; eauto. }
    iCache with "HΦ Hd2".
    { crash_case; iLeft; iFrame. }

    wpc_frame_seq.
    wp_load.
    list_elem addrs0 (int.val i `mod` LogSz) as a.
    { destruct Hlow_wf.
      mod_bound; word. }
    wp_apply (wp_SliceGet _ _ _ _ 1 addrs0 with "[$Hdiskaddrs]"); eauto.
    { iPureIntro.
      change (word.divu _ _) with (U64 LogSz).
      word_cleanup.
      rewrite Ha_lookup.
      eauto. }
    iIntros "Hdiskaddrs".
    iNamed 1.
    wpc_pures.

    wpc_bind (load_ty _ _).
    wpc_frame.
    wp_load.
    iNamed 1.

    wpc_pures.
    change (word.divu _ _) with (U64 LogSz).
    destruct (list_lookup_lt _ blocks0 (Z.to_nat (int.val i `mod` LogSz))) as [b Hblookup].
    { destruct Hlow_wf.
      mod_bound; word. }
    iDestruct (disk_array_acc_disc _ blocks0 (int.val i `mod` LogSz) with "[Hd2]") as "[Hdi Hd2']"; eauto.
    { mod_bound; word. }
    wpc_apply (wpc_Read with "[Hdi]").
    { iExactEq "Hdi".
      f_equal.
      mod_bound; word. }
    iSplit.
    { iLeft in "HΦ". iModIntro. iNext. iIntros "Hdi".
      iSpecialize ("Hd2'" with "[Hdi]").
      { iExactEq "Hdi". f_equal. mod_bound. word. }
      rewrite list_insert_id; eauto. iApply "HΦ"; eauto. }

    iNext.
    iIntros (b_s) "[Hdi Hb_s]".
    iDestruct (own_discrete_elim with "Hd2'") as "Hd2'".

    iDestruct ("Hd2'" with "[Hdi]") as "Hd2".
    { iExactEq "Hdi".
      f_equal.
      mod_bound; word. }
    rewrite list_insert_id; eauto.
    wpc_pures.

    wpc_bind (load_ty _ _).
    wpc_frame.
    wp_load.
    iNamed 1.

    wpc_frame.
    wp_apply (wp_SliceAppend_updates (uv:=(a, b_s)) with "[$Hupds Hb_s]").
    { iApply slice.is_slice_to_small in "Hb_s". iFrame. }
    iIntros (bufSlice') "Hupds'".
    wp_store.

    iNamed 1.

    iApply "HΦ".
    iFrame.
    iSplit; first by iPureIntro; word.
    iExists _; iFrame.
    iExactEq "Hupds'".
    f_equal.
    destruct Hwf.
    destruct Hlow_wf.
    rewrite /circΣ.diskEnd in H.
    word_cleanup.
    autorewrite with len in Hupdslen.
    revert H; word_cleanup; intros.
    assert (int.nat i - int.nat σ.(start) < length σ.(upds))%nat as Hinbounds by word.
    apply list_lookup_lt in Hinbounds.
    destruct Hinbounds as [[a' b'] Hieq].
    pose proof (Hupds _ _ Hieq) as Haddr_block_eq. rewrite /LogSz /= in Haddr_block_eq.
    replace (int.val (start σ) + Z.of_nat (int.nat i - int.nat (start σ)))
      with (int.val i) in Haddr_block_eq by word.
    destruct Haddr_block_eq.
    replace (Z.to_nat (int.val i + 1) - int.nat (start σ))%nat with (S (int.nat i - int.nat (start σ))) by word.
    erewrite take_S_r; eauto.
    rewrite Hieq /=.
    congruence.

  - iDestruct (is_slice_to_small with "Hdiskaddrs") as "Hdiskaddrs".
    iFrame.
    rewrite zero_slice_val.
    iSplit; first by iPureIntro; word.
    iExists _. iFrame.
    iExists nil; simpl.
    iSplitL.
    { iApply is_slice_zero. }
    replace (int.nat (start σ) - int.nat (start σ))%nat with 0%nat by lia.
    rewrite take_0.
    rewrite big_sepL2_nil.
    auto.

  - iSplit.
    { iLeft in "HΦ". iModIntro. iNext. iDestruct 1 as (i) "(Hd2&%)".
      iApply "HΦ".
      iFrame "% ∗".
      iExists _, _; iFrame "∗ %".
      iExists _, _; iFrame "∗ %". }

    iIntros "!> [(_ & HI & Hdiskaddrs & Hd2) Hposl]".
    iDestruct "HI" as (bufSlice) "[Hbufsloc Hupds]".

    wpc_frame.
    wp_pures.

    Transparent struct.t.
    wp_apply wp_allocStruct; first by eauto.
    Opaque struct.t.
    iIntros (ca) "Hca".

    wp_load.

    iMod (ghost_var_alloc addrs0) as (addrs_name') "[Haddrs' Hγaddrs]".
    iMod (ghost_var_alloc blocks0) as (blocks_name') "[Hblocks' Hγblocks]".
    iMod (fmcounter_alloc (int.nat σ.(start))) as (start_name') "[Hstart1 Hstart2]".
    iMod (fmcounter_alloc (Z.to_nat (circΣ.diskEnd σ))) as (diskEnd_name') "[HdiskEnd1 HdiskEnd2]".
    set (γ' := {| addrs_name := addrs_name';
                  blocks_name := blocks_name';
                  start_name := start_name';
                  diskEnd_name := diskEnd_name'; |}).

    iMod (fmcounter_get_lb with "HdiskEnd2") as "[HdiskEnd2 #HdiskEndLb]".

    wp_pures.
    iNamed 1.
    iDestruct "HΦ" as "(_&HΦ)".
    iApply ("HΦ" $! γ').
    iFrame "Hupds".
    iFrame "Hstart1 HdiskEnd1 HdiskEndLb".
    iSplitR "Hca Hdiskaddrs Hγaddrs Hγblocks Hstart2 HdiskEnd2".
    { iSplit; first by eauto.
      iSplit.
      { iPureIntro.
        destruct Hwf; word. }
      iExists _, _.
      iSplit; first by eauto.
      iSplitL "Haddrs' Hblocks'".
      { iFrame "Haddrs' Hblocks'".
        iPureIntro; eauto. }
      iExists _, _.
      iFrame.
      iPureIntro; eauto.
    }
    iSplitR "Hstart2 HdiskEnd2".
    {
      iExists _, _, _.
      iDestruct (struct_fields_split with "Hca") as "[Hca _]".
      by iFrame. }
    iFrame.
    iSplitL.
    { iSplit.
      { iPureIntro; destruct Hwf; len. }
      iSplitL "HdiskEnd2".
      { iExactEq "HdiskEnd2".
        f_equal.
        destruct Hwf; len. }
      iExactEq "HdiskEndLb".
      rewrite /diskEnd_at_least. subst γ'. simpl.
      f_equal.
      destruct Hwf; len.
    }
    iPureIntro; intuition eauto.
    * rewrite take_ge; auto.
      destruct Hwf; word.
    * word_cleanup.
      destruct Hwf.
      rewrite /circΣ.diskEnd.
      word.
Qed.


(* XXX: this instance seems dangerous, I don't want it to get picked up for an l ↦ v, for example.
  But it seems not to since those definitions are sealed. *)
Local Instance own_into_crash {A} `{inG Σ A} (γ: gname) (x: A):
  IntoCrash (own γ x) (λ _, own γ x).
Proof.
  rewrite /IntoCrash. iApply post_crash_nodep.
Qed.
Local Instance gost_var_into_crash {A} `{ghost_varG Σ A} (γ: gname) q (x: A):
  IntoCrash (ghost_var γ q x) (λ _, ghost_var γ q x).
Proof.
  rewrite /IntoCrash. iApply post_crash_nodep.
Qed.

Global Instance is_circular_state_durable γ (σ : circΣ.t):
  IntoCrash (is_circular_state γ σ) (λ _, is_circular_state γ σ).
Proof. apply _. Qed.

Lemma is_circular_state_post_crash σ γ P':
  (IntoCrash (P σ) (P' σ)) →
  is_circular_state γ σ ∗ P σ -∗ post_crash (λ hG, is_circular_state γ σ ∗ P' σ hG).
Proof. iIntros (?) "His". rewrite /is_circular. iCrash. eauto. Qed.

(*
Lemma is_circular_post_crash γ P' :
  (∀ s, IntoCrash (P s) (P' s)) →
  is_circular N P γ ={↑N, ∅}=∗ ▷ post_crash (λ hG, ∃ σ, is_circular_state γ σ ∗ P' σ hG).
Proof.
  iIntros (?) "His".
  rewrite /is_circular.
  iInv "His" as "Hinner" "_".
  iDestruct "Hinner" as (σ) "(>His&HP)".
  rewrite difference_diag_L.
  iModIntro. iNext. iPoseProof (is_circular_state_post_crash with "[$]") as "H".
  iCrash. eauto.
Qed.
*)

(* Once the circular buffer is initialized or recovered, the is_circular
   invariant can be allocated. By allocating that invariant, we no longer need
   to show is_circular_state γ σ ∗ P σ in the crash condition anymore, because at
   crash time we know that this will hold because it is in an invariant.

   This lemma encodes this principle.
 *)

Lemma circ_buf_crash_obligation e Φ Φc Φc' k σ γ:
  is_circular_state γ σ  -∗
  P σ -∗
  □ ((∃ σ', is_circular_state γ σ' ∗ P σ') -∗ Φc -∗ Φc') -∗
  (is_circular N P γ -∗ (WPC e @ NotStuck; k; ⊤ {{ Φ }} {{ Φc }})) -∗
  |={⊤}=> is_circular N P γ ∗ WPC e @ NotStuck; k; ⊤ {{ Φ }} {{ Φc' }}%I.
Proof.
  iIntros "Hstate HP #Hcrash1 HWP". rewrite /is_circular.
  iMod (ncinv_alloc N _ (∃ σ, is_circular_state γ σ ∗ P σ)%I with "[Hstate HP]") as "(#Hinv&Hcfupd)".
  { iNext. iExists _. iFrame. }
  iFrame "Hinv".
  iModIntro.
  iMod "Hcfupd".
  iSpecialize ("HWP" with "[$]").
  iApply (wpc_strong_mono with "HWP"); auto.
  iSplit; first eauto.
  iModIntro. iIntros "H1 !> !> H2".
  iApply ("Hcrash1" with "[$] [$]").
Qed.

(* Note: the version above is more usable, but this helps understand what it achieves *)
Lemma circ_buf_crash_obligation_simple e Φ k σ γ:
  is_circular_state γ σ  -∗
  P σ -∗
  (is_circular N P γ -∗ (WPC e @ NotStuck; k; ⊤ {{ Φ }} {{ True }})) -∗
  |={⊤}=> is_circular N P γ ∗
          WPC e @ NotStuck; k; ⊤ {{ Φ }} {{ ∃ σ', is_circular_state γ σ' ∗ P σ' }}%I.
Proof.
  iIntros "Hstate HP HWP".
  iApply (circ_buf_crash_obligation with "[$] [$] [] [$]"); auto; set_solver+.
Qed.

End heap.
