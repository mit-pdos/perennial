From iris.bi.lib Require Import fractional.
From Perennial.goose_lang Require Import mono_nat.

From RecordUpdate Require Import RecordSet.

From Goose.github_com.mit_pdos.go_journal Require Import wal.

From Perennial.Helpers Require Import Transitions.
From Perennial.goose_lang Require Import crash_modality.
From Perennial.Helpers Require Import NamedProps.
From Perennial.program_proof Require Import disk_prelude disk_lib.
From Perennial.program_proof Require Import wal.lib.
From Perennial.program_proof Require Import marshal_block util_proof.
From Perennial.program_proof Require Import circ_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

(***************)
(*

Crash reasoning strategy:

OLD APPROACH:

We had a persistent assertion is_circular γ, which was an invariant containing
is_circular_state γ σ * P σ, where P is a client chosen rep predicate.  Hence,
by Perennial 1 style reasoning we could know on crash that we had
is_circular_state γ σ * P σ. Because is_circular_state only referred to disk
resources and ghost resources, it was stable under post_crash, hence recovery
got as a precondiiton is_circular_state γ σ * P σ. Recovery generated some fresh
γ' and is_circular_state γ' σ * P σ + the resources sent to installer/logger in
γ' (which were otherwise lost upon crash).

NEW APPROACH:

is_circular is as before, but using an ncinv. We introduce 3 additional predicates:

- init_ghost_state -- this is all of the ghost resources used by both is_circular_state and installer/loggers

- is_circular_state_crash -- this represents a "weakening" of is_circular_state that will be an invariant at crash time.

- circular_crash_ghost_exchange -- this is a series of disjunctions of the form (own γold ... \/ own γnew)

Then we have a lemma crash_upd, which transforms is_circular_state into the resources at crash time.

Lemma crash_upd γold γnew σ :
  is_circular_state γold σ -∗ init_ghost_state γnew ==∗
  is_circular_state γnew σ ∗
  is_circular_state_crash γold σ ∗
  circular_crash_ghost_exchange γold γnew.

This is then used as part of the following lemma, which should be called at the end of recovery:


Lemma circ_buf_crash_obligation_alt Prec Pcrash γ σ:
  is_circular_state γ σ -∗
  □ (∀ σ, ▷ P σ -∗ |0={⊤ ∖ ↑N}=> ▷ Prec σ ∗ ▷ Pcrash σ) -∗
  P σ -∗
  |={⊤}=> ∃ γ', is_circular N P γ ∗ (<bdisc> C -∗ |0={⊤}=> ▷ ∃ σ, is_circular_state γ' σ ∗ Prec σ)
                            ∗ □ (C -∗ |0={⊤}=> inv N (∃ σ, is_circular_state_crash γ σ ∗
                                                           circular_crash_ghost_exchange γ γ' ∗
                                                           Pcrash σ)).

which is used to remove is_circular_state from the crash obligation etc.

When a crash transition actually modifies the state, the above should be changed to:
  □ (∀ σ σ' (Hcrash: crash_rel σ σ'), ▷ P σ -∗ |0={⊤ ∖ ↑N}=> ▷ Prec σ' ∗ ▷ Pcrash σ σ') ...

and analogously in crash_upd. This would allow us to encode further tha Prec σ'
should only hold if σ' is a post-crash state.

*)
(***************)

Section heap.
Context `{!heapGS Σ}.
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

Lemma split_513_blocks :
  0 d↦∗ repeat block0 513 -∗
  0 d↦ block0 ∗ 1 d↦ block0 ∗ 2 d↦∗ repeat block0 511.
Proof. reflexivity. Qed.

Lemma circ_own_init :
  ⊢ |==> ∃ γaddrs γblocks,
        let addrs := repeat (U64 0) 511 in
        let blocks := repeat block0 511 in
        ⌜circ_low_wf addrs blocks⌝ ∗
        ghost_var γaddrs 1 addrs ∗
        ghost_var γblocks 1 blocks.
Proof.
  iMod (ghost_var_alloc (repeat (U64 0) 511)) as (γaddrs) "?".
  iMod (ghost_var_alloc (repeat block0 511)) as (γblocks) "?".
  iModIntro.
  iExists _, _; iFrame.
  iPureIntro.
  rewrite /circ_low_wf.
  rewrite !repeat_length //.
Qed.

Lemma zero_encodings :
  let σ := {| upds := []; start := U64 0; |} in
  block_encodes block0
    ([EncUInt64 (circΣ.diskEnd σ)] ++ map EncUInt64 (repeat (U64 0) 511))
  ∧ block_encodes block0 [EncUInt64 (start σ)].
Proof.
  rewrite /block_encodes /has_encoding.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma circular_init :
  0 d↦∗ repeat block0 513 -∗
  |==> ∃ γ, is_circular_state γ {| upds := []; start := U64 0; |} ∗
            is_circular_appender_pre γ ∗
            start_is γ (1/2) (U64 0) ∗
            diskEnd_is γ (1/2) 0.
Proof.
  set (σ:={| upds := []; start := U64 0; |}).
  assert (circΣ.diskEnd σ = 0) as HdiskEnd by reflexivity.
  rewrite split_513_blocks.
  iIntros "(Hhdr1 & Hhdr2 & Hlog)".
  iMod circ_own_init as (γaddrs γblocks Hlow_wf) "[[Haddrs1 Haddrs2] [Hblocks1 Hblocks2]]".
  iMod (mono_nat_own_alloc 0) as (γstart) "[[Hstart1 Hstart2] #Hstart_lb]".
  iMod (mono_nat_own_alloc 0) as (γend) "[[Hend1 Hend2] #Hend_lb]".
  iExists {| addrs_name := γaddrs; blocks_name := γblocks;
             start_name := γstart; diskEnd_name := γend;
          |}.
  iModIntro.
  rewrite /is_circular_state.
  iSplitR "Haddrs2 Hblocks2 Hstart2 Hend2".
  - iSplit.
    { iPureIntro; hnf; simpl.
      rewrite HdiskEnd.
      word. }
    iSplitL "Hstart1 Hend1".
    { rewrite /circ_positions.
      rewrite /start_is /diskEnd_is /diskEnd_at_least /=.
      rewrite HdiskEnd.
      iFrame "#∗".
      iPureIntro; lia. }
    iExists _, _.
    rewrite /circ_own.
    cbn [addrs_name blocks_name].
    iFrame "Haddrs1 Hblocks1".
    iSplit.
    { iPureIntro.
      rewrite /σ /has_circ_updates.
      cbn [upds start].
      inversion 1. }
    iSplit; first by eauto.
    rewrite /is_low_state.
    iExists block0, block0; iFrame "Hhdr1 Hhdr2 Hlog".
    iPureIntro.
    apply zero_encodings.
  - rewrite /is_circular_appender_pre.
    iSplitL "Haddrs2 Hblocks2".
    + iExists _, _.
      iSplit; first by eauto.
      iFrame.
    + rewrite /start_is /diskEnd_is /=.
      iFrame.
      iSplit; first by (iPureIntro; lia).
      rewrite /diskEnd_at_least /=.
      iFrame "#".
Qed.

Theorem wpc_recoverCircular stk k E1 d σ γ :
  {{{ is_circular_state γ σ ∗ is_circular_appender_pre γ}}}
    recoverCircular (disk_val d) @ stk; k; E1
  {{{ (c:loc) (diskStart diskEnd: u64) (bufSlice:Slice.t) (upds: list update.t),
      RET (#c, #diskStart, #diskEnd, slice_val bufSlice);
      updates_slice bufSlice upds ∗
      is_circular_state γ σ ∗
      is_circular_appender γ c ∗
      ⌜σ.(circΣ.start) = diskStart⌝ ∗
      ⌜σ.(circΣ.upds) = upds⌝ ∗
      ⌜circΣ.diskEnd σ = int.Z diskEnd⌝
  }}}
  {{{ is_circular_state γ σ ∗ is_circular_appender_pre γ }}}.
Proof.
  clear P.
  iIntros (Φ Φc) "(Hcs&Hres) HΦ".

  Opaque struct.t.
  rewrite /recoverCircular.
  wpc_pures; first iFrame.
  { crash_case; eauto with iFrame. }

  iDestruct "Hcs" as (Hwf) "[Hpos Hcs]".
  iDestruct "Hcs" as (addrs0 blocks0 Hupds) "(Hown & Hlow)".
  iDestruct "Hown" as (Hlow_wf) "[Haddrs Hblocks]".
  iDestruct "Hlow" as (hdr1 hdr2 Hhdr1 Hhdr2) "(Hd0 & Hd1 & Hd2)".

  iCache with "HΦ Hpos Haddrs Hblocks Hd0 Hd1 Hd2 Hres".
  { crash_case.
    iFrame "% ∗".
    iExists _, _; iFrame "∗ %".
    iExists _, _; iFrame "∗ %". }

  wpc_apply (wpc_Read with "[Hd0]"); first by iFrame.
  iSplit.
  { iLeft in "HΦ". iIntros "Hd0". iApply "HΦ".
    iFrame "% ∗".
    iExists _, _; iFrame "∗ %".
    iExists _, _; iFrame "∗ %". }

  iIntros (s0) "!> [Hd0 Hs0]".
  wpc_pures.

  wpc_apply (wpc_Read with "[Hd1]"); first iFrame.
  iSplit.
  { iLeft in "HΦ". iIntros "Hd1". iApply "HΦ".
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
    ⌜int.Z σ.(start) <= int.Z i⌝ ∗
    (∃ bufSlice,
      bufsloc ↦[slice.T (struct.t Update)] (slice_val bufSlice) ∗
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
    eauto.
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
    list_elem addrs0 (int.Z i `mod` LogSz) as a.
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
    wp_load. iModIntro.
    iNamed 1.

    wpc_pures.
    change (word.divu _ _) with (U64 LogSz).
    destruct (list_lookup_lt _ blocks0 (Z.to_nat (int.Z i `mod` LogSz))) as [b Hblookup].
    { destruct Hlow_wf.
      mod_bound; word. }
    iDestruct (disk_array_acc _ blocks0 (int.Z i `mod` LogSz) with "[Hd2]") as "[Hdi Hd2']"; eauto.
    { mod_bound; word. }
    wpc_apply (wpc_Read with "[Hdi]").
    { iExactEq "Hdi".
      f_equal.
      mod_bound; word. }
    iSplit.
    { iLeft in "HΦ". iIntros "Hdi".
      iSpecialize ("Hd2'" with "[Hdi]").
      { iExactEq "Hdi". f_equal. mod_bound. word. }
      rewrite list_insert_id; eauto. iApply "HΦ"; eauto. }

    iNext.
    iIntros (b_s) "[Hdi Hb_s]".

    iDestruct ("Hd2'" with "[Hdi]") as "Hd2".
    { iExactEq "Hdi".
      f_equal.
      mod_bound; word. }
    rewrite list_insert_id; eauto.
    wpc_pures.

    wpc_bind (load_ty _ _).
    wpc_frame.
    wp_load. iModIntro.
    iNamed 1.

    wpc_frame.
    wp_apply (wp_SliceAppend_updates (uv:=(a, b_s)) with "[$Hupds Hb_s]").
    { iApply slice.is_slice_to_small in "Hb_s". iFrame. }
    iIntros (bufSlice') "Hupds'".
    wp_store. iModIntro.

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
    replace (int.Z (start σ) + Z.of_nat (int.nat i - int.nat (start σ)))
      with (int.Z i) in Haddr_block_eq by word.
    destruct Haddr_block_eq.
    replace (Z.to_nat (int.Z i + 1) - int.nat (start σ))%nat with (S (int.nat i - int.nat (start σ))) by word.
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
    { iLeft in "HΦ". iDestruct 1 as (i) "(Hd2&%)".
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
    (*

    iMod (ghost_var_alloc addrs0) as (addrs_name') "[Haddrs' Hγaddrs]".
    iMod (ghost_var_alloc blocks0) as (blocks_name') "[Hblocks' Hγblocks]".
    iMod (mono_nat_own_alloc (int.nat σ.(start))) as (start_name') "[[Hstart1 Hstart2] _]".
    iMod (mono_nat_own_alloc (Z.to_nat (circΣ.diskEnd σ))) as (diskEnd_name') "[[HdiskEnd1 HdiskEnd2] #HdiskEndLb]".
    set (γ' := {| addrs_name := addrs_name';
                  blocks_name := blocks_name';
                  start_name := start_name';
                  diskEnd_name := diskEnd_name'; |}).

    *)
    wp_pures. iModIntro.
    iNamed 1.
    iDestruct "HΦ" as "(_&HΦ)".
    iApply ("HΦ").
    iFrame "Hpos Hupds". iFrame.
    iDestruct "Hres" as (???) "(Haddrs'&Hblocks')".
    iDestruct (ghost_var_agree with "Hblocks Hblocks'") as %->.
    iDestruct (ghost_var_agree with "Haddrs Haddrs'") as %->.
    iSplitL "Hd0 Hd1 Hd2 Hblocks Haddrs".
    { iSplit; first done. iExists _, _. iFrame.
      iSplit; first done.
      iSplit; first done.
      iExists _, _. iFrame. eauto.
    }
    iSplitL "Hca Hposl Hdiskaddrs Haddrs' Hblocks'".
    {
      iExists _, _, _. iFrame. iSplit; first done.
      iDestruct (struct_fields_split with "Hca") as "[Hca _]".
      iFrame.
    }
    iFrame.
    (*
    iSplitL "Hend_is".
    {
      iExactEq "Hend_is".
      rewrite take_ge; auto. destruct Hwf; word.
    }
     *)
    iPureIntro; split_and!; eauto.
    * rewrite take_ge; auto. destruct Hwf; word.
    * destruct Hwf.
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
Local Instance ghost_var_into_crash {A} `{ghost_varG Σ A} (γ: gname) q (x: A):
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

Lemma circ_buf_crash_obligation_alt E Prec Pcrash γ σ:
  ↑N ⊆ E →
  is_circular_state γ σ -∗
  □ (∀ σ, ▷ P σ -∗ |0={E ∖ ↑N}=> ▷ Prec σ ∗ ▷ Pcrash σ) -∗
  P σ -∗
  |={⊤}=> ∃ γ', is_circular N P γ ∗
                            (<bdisc> (|C={E}_0=> ∃ σ, is_circular_state γ' σ ∗
                                                    circ_resources γ' σ ∗
                                                    ▷ Prec σ))
                            ∗ □ (|C={E}_0=> inv N (∃ σ, is_circular_state_crash γ σ ∗
                                                           circular_crash_ghost_exchange γ γ' ∗
                                                           Pcrash σ)).
Proof.
  iIntros (?) "Hcs #HPwand HP".
  iMod (alloc_init_ghost_state) as (γ') "Hinit".
  iMod (ncinv_cinv_alloc N 0 ⊤ E
         ((∃ σ, is_circular_state γ σ ∗ P σ) ∗ init_ghost_state γ')
         (∃ σ, is_circular_state_crash γ σ ∗
               circular_crash_ghost_exchange γ γ' ∗
               Pcrash σ)%I
         (∃ σ, is_circular_state γ' σ ∗ circ_resources γ' σ ∗ Prec σ)%I with
            "[] [Hcs HP Hinit]") as "(Hncinv&Hcfupd&Hcinv)".
  { solve_ndisj. }
  { iModIntro. iIntros "(H1&>Hinit)".
    iDestruct "H1" as (σ') "(>Hstate&HP)".
    iIntros "#HC".
    iApply (fupd_level_fupd).
    iMod ("HPwand" with "[$]") as "(HPrec&HPcrash)".
    iMod (crash_upd with "[$] [$]") as "(Hcs&Hres&Hcs_crash&Hexchange)".
    iModIntro.
    iSplitR "Hcs HPrec Hres".
    { iNext. iExists _. iFrame. }
    { iNext. iExists _. iFrame. }
  }
  { iNext. iFrame. iExists _. iFrame. }
  iModIntro. iExists γ'.
  iSplitL "Hncinv".
  { rewrite /is_circular. iApply ncinv_split_l; iApply "Hncinv". }
  eauto. iFrame "Hcinv".
  iModIntro. iIntros "HC". iMod ("Hcfupd" with "[$]") as (?) "(>?&>?&?)".
  iModIntro; iExists _; iFrame.
Qed.

(* Once the circular buffer is initialized or recovered, the is_circular
   invariant can be allocated. By allocating that invariant, we no longer need
   to show is_circular_state γ σ ∗ P σ in the crash condition anymore, because at
   crash time we know that this will hold because it is in an invariant.

   This lemma encodes this principle.
 *)

Lemma circ_buf_crash_obligation e Φ Φc Φc' k σ γ:
  is_circular_state γ σ  -∗
  P σ -∗
  □ (▷ (∃ σ', is_circular_state γ σ' ∗ P σ') -∗ Φc -∗ Φc') -∗
  (is_circular N P γ -∗ (WPC e @ k; ⊤ {{ Φ }} {{ Φc }})) -∗
  |={⊤}=> is_circular N P γ ∗ WPC e @ k; ⊤ {{ Φ }} {{ Φc' }}%I.
Proof.
  iIntros "Hstate HP #Hcrash1 HWP". rewrite /is_circular.
  iMod (ncinv_alloc N _ (∃ σ, is_circular_state γ σ ∗ P σ)%I with "[Hstate HP]") as "(#Hinv&Hcfupd)".
  { iNext. iExists _. iFrame. }
  iFrame "Hinv".
  iModIntro.
  iMod (own_disc_fupd_elim with "Hcfupd") as "Hcfupd".
  iSpecialize ("HWP" with "[$]").
  iApply (wpc_strong_mono with "HWP"); auto.
  iSplit; first eauto.
   iIntros "H1".
  iMod (cfupd_weaken_all with "[$]"); try lia; eauto.
  iModIntro.
  iApply ("Hcrash1" with "[$] [$]").
Qed.

(* Note: the version above is more usable, but this helps understand what it achieves *)
Lemma circ_buf_crash_obligation_simple e Φ k σ γ:
  is_circular_state γ σ  -∗
  P σ -∗
  (is_circular N P γ -∗ (WPC e @ k; ⊤ {{ Φ }} {{ True }})) -∗
  |={⊤}=> is_circular N P γ ∗
          WPC e @ k; ⊤ {{ Φ }} {{ ▷ ∃ σ', is_circular_state γ σ' ∗ P σ' }}%I.
Proof.
  iIntros "Hstate HP HWP".
  iApply (circ_buf_crash_obligation with "[$] [$] [] [$]"); auto; set_solver+.
Qed.

End heap.
