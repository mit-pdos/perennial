Import EqNotations.
From Perennial.Helpers Require Import Map.
From Perennial.algebra Require Import auth_map liftable log_heap async.

From Goose.github_com.mit_pdos.go_journal Require Import jrnl.
From Perennial.program_logic Require Export ncinv.
From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof obj.obj_proof.
From Perennial.program_proof Require jrnl.jrnl_proof.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.goose_lang.ffi Require Import disk_prelude.
From Perennial.program_proof Require Import jrnl.sep_jrnl_invariant.

(** * A more separation logic-friendly spec for jrnl

Overview of resources used here:

durable_pointsto_own - durable, exclusive
durable_pointsto - durable but missing modify_token
jrnl_maps_to - ephemeral

is_crash_lock (durable_pointsto_own) (durable_pointsto)
on crash: exchange durable_pointsto for durable_pointsto_own

lift: move durable_pointsto_own into transaction and get jrnl_maps_to and durable_pointsto is added to is_jrnl

is_jrnl P = is_jrnl_mem * is_jrnl_durable P

reads and writes need jrnl_maps_to and is_jrnl_mem

is_jrnl_durable P -* P (P is going to be durable_pointsto) (use this to frame out crash condition)

exchange own_last_frag γ for own_last_frag γ' ∗ modify_token γ' (in sep_jrnl layer)
exchange ephemeral_txn_val γ for ephemeral_txn_val γ' if the transaction id was preserved
 *)

(* mspec is a shorthand for referring to the old "map-based" spec, since we will
want to use similar names in this spec *)
Module mspec := jrnl.jrnl_proof.

Section goose_lang.
  Context `{!jrnlG Σ}.
  Context `{!heapGS Σ}.

  Context (N:namespace).

  Implicit Types (l: loc) (γ: jrnl_names) (γtxn: gname).
  Implicit Types (obj: object).

  Theorem wp_Op__Begin' (l_txn: loc) γ dinit :
    {{{ is_txn l_txn γ.(jrnl_txn_names) dinit ∗ is_txn_system N γ }}}
      Begin #l_txn
    {{{
      γtxn γdurable l, RET #l;
      "Hjrnl_mem" ∷ is_jrnl_mem N l γ dinit γtxn γdurable ∗
      "Hdurable_frag" ∷ map_ctx γdurable (1/2) ∅
    }}}.
  Proof.
    iIntros (Φ) "Hpre HΦ".
    iDestruct "Hpre" as "[#His_txn #Htxn_inv]".
    iApply wp_fupd.
    wp_apply (mspec.wp_jrnl_Begin with "His_txn").
    iIntros (l) "Hjrnl".
    iMod (map_init ∅) as (γtxn) "Hctx".
    iMod (map_init ∅) as (γdurable) "[Hdurable Hdurable_frag]".
    iModIntro.
    iApply "HΦ".
    iFrame "Hdurable_frag".
    iExists ∅, false.
    rewrite !fmap_empty. iFrame "Hctx".
    iFrame "∗#".
    auto with iFrame.
  Qed.

  Theorem wp_Op__Begin (l_txn: loc) γ dinit :
    {{{ is_txn l_txn γ.(jrnl_txn_names) dinit ∗ is_txn_system N γ }}}
      Begin #l_txn
    {{{ γtxn l, RET #l; is_jrnl N l γ dinit γtxn (λ _, emp) }}}.
  Proof.
    iIntros (Φ) "Hpre HΦ".
    wp_apply (wp_Op__Begin' with "Hpre").
    iIntros (???) "[? ?]".
    iNamed.
    iApply "HΦ".
    iExists γdurable.
    iFrame.
    rewrite !big_sepM_empty.
    auto with iFrame.
  Qed.

  Definition is_object l a obj: iProp Σ :=
    ∃ dirty, is_buf l a
                    {| bufKind := objKind obj;
                       bufData := objData obj;
                       bufDirty := dirty |}.

  Theorem wp_Op__ReadBuf l γ dinit γtxn γdurable (a: addr) (sz: u64) obj :
    bufSz (objKind obj) = uint.nat sz →
    {{{ is_jrnl_mem N l γ dinit γtxn γdurable ∗ jrnl_maps_to γtxn a obj }}}
      Op__ReadBuf #l (addr2val a) #sz
    {{{ dirty (bufptr:loc), RET #bufptr;
        is_buf bufptr a (Build_buf _ (objData obj) dirty) ∗
        (∀ (obj': bufDataT (objKind obj)) dirty',
            is_buf bufptr a (Build_buf _ obj' dirty') -∗
            ⌜dirty' = true ∨ (dirty' = dirty ∧ obj' = objData obj)⌝ ==∗
            is_jrnl_mem N l γ dinit γtxn γdurable ∗ jrnl_maps_to γtxn a (existT (objKind obj) obj')) }}}.
  Proof.
    iIntros (? Φ) "Hpre HΦ".
    iDestruct "Hpre" as "[Hjrnl Ha]".
    iNamed "Hjrnl".
    iDestruct (map_valid with "Htxn_ctx Ha") as %Hmt_lookup.
    fmap_Some in Hmt_lookup as vo.
    wp_apply (mspec.wp_Op__ReadBuf with "[$Hjrnl]").
    { iPureIntro.
      split; first by eauto.
      rewrite H.
      word. }
    iIntros (??) "[Hbuf Hbuf_upd]".
    iApply "HΦ".
    iFrame "Hbuf".
    iIntros (obj' dirty') "Hbuf". iIntros (Hdirty).
    iMod ("Hbuf_upd" with "[$Hbuf]") as "Hjrnl".
    { iPureIntro; intuition auto. }
    intuition subst.
    - (* user inserted a new value into the read buffer; need to do the updates
      to incorporate that write *)
      iMod (map_update with "Htxn_ctx Ha") as
          "[Htxn_ctx $]".
      iModIntro.
      iExists (<[a:=mspec.mkVersioned (objData (mspec.committed vo)) obj']> mT), true.
      iFrame "Htxn_system".
      rewrite !fmap_insert !mspec.committed_mkVersioned !mspec.modified_mkVersioned //.
      change (existT (objKind ?x) (objData ?x)) with x.
      rewrite (insert_id (mspec.committed <$> mT)); last first.
      { rewrite lookup_fmap Hmt_lookup //. }
      rewrite orb_true_r.
      iFrame "∗#".
      iPureIntro; intros; congruence.
    - (* user did not change buf, so no basic updates are needed *)
      iModIntro.
      simpl.
      rewrite insert_id; last first.
      { rewrite Hmt_lookup.
        destruct vo as [K [c m]]; done. }
      iFrame "Ha".
      iExists mT, _.
      iFrameNamed.
      iPureIntro. destruct anydirty; eauto.
  Qed.

  Definition data_has_obj (data: list byte) (a:addr) obj : Prop :=
    match objData obj with
    | bufBit b =>
      ∃ b0, data = [b0] ∧
            get_bit b0 (word.modu (addrOff a) 8) = b
    | bufInode i => vec_to_list i = data
    | bufBlock b => vec_to_list b = data
    end.

  Theorem data_has_obj_to_buf_data s a obj data :
    data_has_obj data a obj →
    own_slice_small s u8T (DfracOwn 1) data -∗ is_buf_data s (objData obj) a.
  Proof.
    rewrite /data_has_obj /is_buf_data.
    iIntros (?) "Hs".
    destruct (objData obj); subst.
    - destruct H as (b' & -> & <-).
      iExists b'; iFrame.
      auto.
    - iFrame.
    - iFrame.
  Qed.

  Theorem is_buf_data_has_obj s a obj :
    is_buf_data s (objData obj) a ⊣⊢ ∃ data, own_slice_small s u8T (DfracOwn 1) data ∗ ⌜data_has_obj data a obj⌝.
  Proof.
    iSplit; intros.
    - rewrite /data_has_obj /is_buf_data.
      destruct (objData obj); subst; eauto.
      iDestruct 1 as (b') "[Hs %]".
      iExists [b']; iFrame.
      eauto.
    - iDestruct 1 as (data) "[Hs %]".
      iApply (data_has_obj_to_buf_data with "Hs"); auto.
  Qed.

  (* the subst in this lemma is really where the magic is happening *)
  Lemma is_buf_data_rew K s a obj (H: objKind obj = K) :
    is_buf_data s (objData obj) a ⊢@{_}
    is_buf_data s (rew [bufDataT] H in objData obj) a.
  Proof.
    subst.
    reflexivity.
  Qed.

  Theorem wp_Op__OverWrite l γ dinit γtxn γdurable (a: addr) (sz: u64)
          (data_s: Slice.t) (data: list byte) obj0 obj :
    bufSz (objKind obj) = uint.nat sz →
    data_has_obj data a obj →
    objKind obj = objKind obj0 →
    {{{ is_jrnl_mem N l γ dinit γtxn γdurable ∗ jrnl_maps_to γtxn a obj0 ∗
        (* NOTE(tej): this has to be a 1 fraction, because the slice is
        incorporated into the jrnl, is handed out in ReadBuf, and should then
        be mutable. *)
        own_slice_small data_s byteT (DfracOwn 1) data }}}
      Op__OverWrite #l (addr2val a) #sz (slice_val data_s)
    {{{ RET #(); is_jrnl_mem N l γ dinit γtxn γdurable ∗ jrnl_maps_to γtxn a obj }}}.
  Proof.
    iIntros (??? Φ) "Hpre HΦ".
    iDestruct "Hpre" as "(Hjrnl & Ha & Hdata)".
    iNamed "Hjrnl".
    iApply wp_fupd.
    iDestruct (map_valid with "Htxn_ctx Ha") as %Hlookup.
    fmap_Some in Hlookup as vo0.
    wp_apply (mspec.wp_Op__OverWrite _ _ _ _ _ _ (mspec.mkVersioned (objData (mspec.committed vo0)) (rew H1 in objData obj)) with "[$Hjrnl Hdata]").
    { iSplit; eauto.
      iSplitL.
      - iApply data_has_obj_to_buf_data in "Hdata"; eauto.
        simpl.
        iApply (is_buf_data_rew with "Hdata").
      - iPureIntro.
        simpl.
        destruct vo0 as [K0 [c0 m0]]; simpl in *; subst.
        split; [rewrite H; word|done]. }
    iIntros "Hjrnl".
    iMod (map_update _ _ obj with "Htxn_ctx Ha") as "[Htxn_ctx Ha]".
    iModIntro.
    iApply "HΦ".
    iFrame "Ha".
    iExists _, true; iFrame "Htxn_system Hjrnl".
    rewrite !fmap_insert !mspec.committed_mkVersioned !mspec.modified_mkVersioned /=.
    rewrite (insert_id (mspec.committed <$> mT)); last first.
    { rewrite lookup_fmap Hlookup //. }
    iFrame "∗#".
    iSplit.
    2: eauto.
    iExactEq "Htxn_ctx".
    rewrite /named.
    f_equal.
    f_equal.
    destruct obj; simpl in *; subst; reflexivity.
  Qed.

  Theorem wp_Op__NDirty l γ dinit γtxn γdurable :
    {{{ is_jrnl_mem N l γ dinit γtxn γdurable }}}
      Op__NDirty #l
    {{{ (n:u64), RET #n; is_jrnl_mem N l γ dinit γtxn γdurable }}}.
  Proof.
    iIntros (Φ) "H HΦ". iNamed "H".
    wp_apply (mspec.wp_Op__NDirty with "Hjrnl").
    iIntros (n) "Hjrnl".
    iApply "HΦ".
    iExists _, _; iFrameNamed.
  Qed.

  (*
  lift: modify_token ∗ stable_maps_to ==∗ jrnl_maps_to

  is_crash_lock (P (modify_token ∗ stable_maps_to)) (P stable_maps_to)

  durable_lb i
  -∗ exact_txn_id i' (≥ i)

  ephemeral_maps_to (≥i+1) a v ∗ stable_maps_to i a v0 ∗ durable_lb i
  -∗ (ephemeral_maps_to i' a v ∗ stable_maps_to i' a v) ∨


  P (ephemeral_maps_to (≥i+1)) ∗ P0 (stable_maps_to i) ∗ durable_lb i
  -∗

  {P jrnl_maps_to ∧ P0 stable_maps_to}
    CommitWait
  {P (modify_token ∗ stable_maps_to)}
  {P0 stable_maps_to ∨ P stable_maps_to}
*)

  (* TODO: is this too weak with [durable_pointsto]? does it need to be
  [durable_pointsto_own]? *)
  Lemma async_ctx_durable_map_split γ mT σs :
    async_ctx γ.(jrnl_async_name) 1 σs -∗
    ([∗ map] a↦v ∈ mT, durable_pointsto γ a v) -∗
    |==> async_ctx γ.(jrnl_async_name) 1 σs ∗
          (* this complex expression is persistent and guarantees that the value
          after a crash comes from [mT] if we crash to any current transaction
          (that is, to a transaction id [≤ length (possible σs)]) *)
          (([∗ map] k↦x ∈ mT,
                ∃ i, txn_durable γ i ∗
                     ephemeral_txn_val_range γ.(jrnl_async_name)
                        i (length (possible σs)) k x)) ∗
          ([∗ map] k↦x ∈ mT, ephemeral_val_from γ.(jrnl_async_name)
                               (length (possible σs) - 1) k x).
  Proof.
    iIntros "Hctx".
    iInduction mT as [|k x mT] "IH" using map_ind.
    - rewrite !big_sepM_empty.
      by iFrame.
    - rewrite !big_sepM_insert //.
      iIntros "[Hi Hm]".
      iDestruct "Hi" as (i) "[Hi Hi_durable]".
      iMod (async_ctx_ephemeral_val_from_split with "Hctx Hi")
        as "(Hctx&Hrange&H+)".
      iMod ("IH" with "Hctx Hm") as "(Hctx&Hold&Hm)".
      iModIntro.
      iFrame.
  Qed.


  Theorem wp_Op__CommitWait {l γ dinit γtxn} P0 P `{!Liftable P} :
    N ## invariant.walN →
    N ## invN →
    {{{ "Hjrnl" ∷ is_jrnl N l γ dinit γtxn P0 ∗
        "HP" ∷ P (jrnl_maps_to γtxn)
    }}}
      Op__CommitWait #l #true
    {{{ (ok:bool), RET #ok;
        if ok then
            P (λ a v, durable_pointsto_own γ a v)
        else P0 (λ a v, durable_pointsto_own γ a v) }}}.
  (* crash condition will be [∃ txn_id', P0 (ephemeral_val_from
     γ.(jrnl_async_name) txn_id') ∨ P (ephemeral_val_from γ.(jrnl_async_name)
     txn_id') ]

     where txn_id' is either the original and we get P0 or we commit and advance
     to produce new [ephemeral_val_from]'s *)
  Proof.
    iIntros (?? Φ) "Hpre HΦ"; iNamed "Hpre".
    iNamed "Hjrnl".
    iNamed "Hjrnl_mem".
    iNamed "Hjrnl_durable".
    iDestruct (map_ctx_agree with "Hdurable_frag Hdurable") as %->.
    iDestruct (liftable_restore_elim with "HP") as (m) "[Hstable HPrestore]".
    iDestruct (map_valid_subset with "Htxn_ctx Hstable") as %HmT_sub.
    (* here things are a little tricky because committing doesn't give us
    [durable_pointsto] but just [ephemeral_val_from] *)
    wp_apply (mspec.wp_Op__CommitWait
                (* ([∗ map] a↦v ∈ (mspec.committed <$> mT),
                 ephemeral_val_from γ.(jrnl_async_name) txn_id0 a v) *) _
                _ _ _ _ _ _
              (λ txn_id', ([∗ map] a↦v∈mspec.modified <$> mT, ephemeral_val_from γ.(jrnl_async_name) txn_id' a v))%I
                with "[$Hjrnl Hold_vals]").
    { iSplit; [ iModIntro; iAccu | ].
      iDestruct "Htxn_system" as "[Hinv _]".
      iInv "Hinv" as ">Hinner" "Hclo".
      iModIntro.
      iNamed "Hinner".
      iExists σs.
      iFrame "H◯async".
      iIntros "H◯async".

      (* NOTE: we don't use this theorem and instead inline its proof (to some
      extent) since we really need to know what the new map is, to restore
      txn_system_inv. *)
      (* iMod (map_update_predicate with "H●latest HP0 HP") as (m') "[H●latest HP]". *)
      iMod (async_ctx_durable_map_split with "H●latest Hold_vals")
        as "(H●latest & #Hold_vals & Hnew)".
      (* Hold_vals is what we should be using in the crash condition *)

      iMod (async_update_map (mspec.modified <$> mT) with "H●latest Hnew") as "[H●latest Hnew]".
      { set_solver. }

      iMod ("Hclo" with "[H◯async H●latest]") as "_".
      { iNext.
        iExists _.
        iFrame. }
      iModIntro.
      rewrite length_possible_async_put.
      iExactEq "Hnew".
      auto with f_equal lia. }
    iIntros (ok) "Hpost".
    destruct ok.
    - iDestruct "Hpost" as "[Hpost | Hpost]".
      + iDestruct "Hpost" as "[%Hanydirty_true Hpost]".
        iDestruct "Hpost" as (txn_id) "(HQ & Hmod_tokens & Hlower_bound)".
        iAssert (txn_durable γ txn_id) as "#Hdurable_txn_id {Hlower_bound}".
        { iApply "Hlower_bound". done. }
        iApply "HΦ".
        iApply "HPrestore".
        iApply big_sepM_subseteq; eauto.
        iApply big_sepM_sep; iFrame.
        rewrite /durable_pointsto.
        iSplitR "HQ".
        (* TODO: factor this out to a lemma *)
        { iApply (big_sepM_mono with "Hmod_tokens").
          rewrite /modify_token. eauto. }
        iApply (big_sepM_impl with "HQ []").
        iIntros "!>" (k x ?) "Hval".
        iExists _; iFrame "∗#".
      + iDestruct "Hpost" as "[%Hanydirty_false Hpost]".
        iDestruct "Hpost" as "(Hpreq & Hmod_tokens)".
        iApply "HΦ".
        iApply "HPrestore".
        iApply big_sepM_subseteq; eauto.
        iApply big_sepM_sep; iFrame.
        iSplitR "Hpreq".
        { iApply (big_sepM_mono with "Hmod_tokens").
          rewrite /modify_token. eauto. }
        rewrite Hanydirty; eauto.
    - iDestruct "Hpost" as "[Heph Hmod_tokens]".
      iApply "HΦ".
      iApply "HrestoreP0".
      iApply big_sepM_sep; iFrame.
      iApply (big_sepM_mono with "Hmod_tokens").
      iIntros (k x Hkx) "H".
      iExists _; iFrame.
  Qed.

  Theorem wpc_Op__CommitWait' {l γ γ' dinit γtxn γdurable committed_mT m} :
    N ## invariant.walN →
    N ## invN →
    N ## mspec.wpwpcN →
    {{{
      "Hjrnl_mem" ∷ is_jrnl_mem N l γ dinit γtxn γdurable ∗
      "Hdurable_frag" ∷ map_ctx γdurable (1/2) committed_mT ∗
      "Hold_vals" ∷ ([∗ map] a↦v ∈ committed_mT, durable_pointsto γ a v) ∗
      "Hstable" ∷ ([∗ map] a↦v ∈ m, jrnl_maps_to γtxn a v) ∗
      "#Htxn_cinv" ∷ txn_cinv N γ γ'
    }}}
      Op__CommitWait #l #true @ ⊤
    {{{
      (ok:bool), RET #ok;
      ([∗ map] a↦v ∈ (if ok then m else committed_mT), durable_pointsto_own γ a v)
    }}}
    {{{
      ([∗ map] a↦v ∈ committed_mT, durable_pointsto_own γ' a v) ∨
      ([∗ map] a↦v ∈ m, durable_pointsto_own γ' a v)
    }}}.
  Proof.
    iIntros (HwalN HinvN HwpwpcN Φ Φc) "(?&?&?&?&?) HΦ".
    iNamed.
    iNamed "Hjrnl_mem".
    iDestruct (map_ctx_agree with "Hdurable_frag Hdurable") as %->.
    iDestruct (map_valid_subset with "Htxn_ctx Hstable") as %HmT_sub.

    iApply wpc_cfupd.

    (* here things are a little tricky because committing doesn't give us
    [durable_pointsto] but just [ephemeral_val_from] *)
    wpc_apply (mspec.wpc_Op__CommitWait
                (* ([∗ map] a↦v ∈ (mspec.committed <$> mT),
                 ephemeral_val_from γ.(jrnl_async_name) txn_id0 a v) *) _
                _ _ _ _ _ _
              (λ txn_id', ([∗ map] a↦v∈mspec.modified <$> mT,
                            ephemeral_val_from γ.(jrnl_async_name) txn_id' a v))%I
              (λ txn_id',
               ([∗ map] a↦v∈mspec.modified <$> mT,
                            ephemeral_val_from γ.(jrnl_async_name) txn_id' a v) ∗
               ([∗ map] k↦x ∈ (mspec.committed <$> mT), ∃ i : nat,
                   txn_durable γ i
                               ∗ ephemeral_txn_val_range γ.(jrnl_async_name) i
                                                              txn_id' k x))%I
                with "[$Hjrnl Hold_vals]").
    1: { iSplit; [ iModIntro; iAccu | ].
      iDestruct "Htxn_system" as "[Hinv _]".
      iInv "Hinv" as ">Hinner" "Hclo".
      iModIntro.
      iNamed "Hinner".
      iExists σs.
      iFrame "H◯async".
      iIntros "H◯async".

      (* NOTE: we don't use this theorem and instead inline its proof (to some
      extent) since we really need to know what the new map is, to restore
      txn_system_inv. *)
      (* iMod (map_update_predicate with "H●latest HP0 HP") as (m') "[H●latest HP]". *)
      iMod (async_ctx_durable_map_split with "H●latest Hold_vals")
        as "(H●latest & #Hold_vals & Hnew)".
      (* Hold_vals is what we should be using in the crash condition *)

      iMod (async_update_map (mspec.modified <$> mT) with "H●latest Hnew") as "[H●latest Hnew]".
      { set_solver. }

      iMod ("Hclo" with "[H◯async H●latest]") as "_".
      { iNext.
        iExists _.
        iFrame. }
      iModIntro.
      rewrite length_possible_async_put.
      replace (S (length (possible σs)) - 1)%nat with (length (possible σs))%nat by lia.
      iSplit.
      { iModIntro. iModIntro. generalize (length (possible σs)); intros. iFrame "∗#". }
      iExactEq "Hnew".
      auto with f_equal lia. }
    iSplit.
    { iDestruct "HΦ" as "[HΦc _]". iIntros "H".
      iDestruct "H" as "[H|H]".
      {
        iDestruct "H" as (txnid) "(H&#Hold_vals)".
        iMod (exchange_pointsto_commit with "[$Htxn_cinv $H $Hold_vals]") as "H".
        { rewrite ?dom_fmap //. }
        iModIntro.
        iApply "HΦc".
        iDestruct "H" as "[H|H]".
        - iLeft. iApply "H".
        - iRight. iDestruct (big_sepM_subseteq with "H") as "H"; eauto.
      }
      { iMod (exchange_durable_pointsto with "[$Htxn_cinv $H]") as "H".
        iModIntro. iApply "HΦc". iLeft. iFrame. }
    }
    iModIntro.
    iIntros (ok) "Hpost".
    destruct ok.
    - iDestruct "Hpost" as "[Hpost | Hpost]".
      + iDestruct "Hpost" as "[%Hanydirty_true Hpost]".
        iDestruct "Hpost" as (txn_id) "(HQ & Hmod_tokens & Hlower_bound)".
        iAssert (txn_durable γ txn_id) as "#Hdurable_txn_id {Hlower_bound}".
        { iApply "Hlower_bound". done. }
        iApply "HΦ".
        iApply big_sepM_subseteq; eauto.
        iApply big_sepM_sep; iFrame.
        rewrite /durable_pointsto.
        iSplitR "HQ".
        (* TODO: factor this out to a lemma *)
        { iApply (big_sepM_mono with "Hmod_tokens").
          rewrite /modify_token. eauto. }
        iApply (big_sepM_impl with "HQ []").
        iIntros "!>" (k x ?) "Hval".
        iExists _; iFrame "∗#".
      + iDestruct "Hpost" as "[%Hanydirty_false Hpost]".
        iDestruct "Hpost" as "(Hpreq & Hmod_tokens)".
        iApply "HΦ".
        iApply big_sepM_subseteq; eauto.
        iApply big_sepM_sep; iFrame.
        iSplitR "Hpreq".
        { iApply (big_sepM_mono with "Hmod_tokens").
          rewrite /modify_token. eauto. }
        rewrite Hanydirty; eauto.
    - iDestruct "Hpost" as "[Heph Hmod_tokens]".
      iApply "HΦ".
      iApply big_sepM_sep; iFrame.
      iApply (big_sepM_mono with "Hmod_tokens").
      iIntros (k x Hkx) "H".
      iExists _; iFrame.
      Unshelve.
      apply _.
  Qed.

  Theorem wpc_Op__CommitWait {l γ γ' dinit γtxn} P0 P `{!Liftable P} :
    N ## invariant.walN →
    N ## invN →
    N ## mspec.wpwpcN ->
    {{{ "Hjrnl" ∷ is_jrnl N l γ dinit γtxn P0 ∗
        "HP" ∷ P (jrnl_maps_to γtxn) ∗
        "#Htxn_cinv" ∷ txn_cinv N γ γ'
    }}}
      Op__CommitWait #l #true @ ⊤
    {{{ (ok:bool), RET #ok;
        if ok then
            P (λ a v, durable_pointsto_own γ a v)
        else P0 (λ a v, durable_pointsto_own γ a v) }}}
    {{{ P0 (durable_pointsto_own γ') ∨
         P (durable_pointsto_own γ') }}}.
  Proof.
    iIntros (??? Φ Φc) "Hpre HΦ". iNamed "Hpre".
    iNamed "Hjrnl".
    (* iNamed "Hjrnl_mem". *)
    iNamed "Hjrnl_durable".
    (* iDestruct (map_ctx_agree with "Hdurable_frag Hdurable") as %->. *)
    iDestruct (liftable_restore_elim with "HP") as (m) "[Hstable #HPrestore]".

    wpc_apply (
      wpc_Op__CommitWait'
      with "[$Hjrnl_mem Hdurable_frag Hold_vals Hstable Htxn_cinv]"
    ).
    1-3: solve_ndisj.
    1: iFrame "∗ #".
    iSplit.
    {
      iDestruct "HΦ" as "[HΦc _]".
      iDestruct 1 as "[H|H]"; iApply "HΦc".
      - iLeft.
        iApply "HrestoreP0".
        iApply "H".
      - iRight.
        iApply "HPrestore".
        iApply "H".
    }
    iIntros (ok) "!> H".
    iApply "HΦ".
    destruct ok.
    - iApply "HPrestore".
      iApply "H".
    - iApply "HrestoreP0".
      iApply "H".
  Qed.

  Theorem is_jrnl_mem_durable l γ dinit γtxn P0 γdurable :
    is_jrnl_mem N l γ dinit γtxn γdurable -∗
    is_jrnl_durable γ γdurable P0 -∗
    is_jrnl N l γ dinit γtxn P0.
  Proof.
    iIntros "Hmem Hdurable".
    iExists _. iFrame.
  Qed.

End goose_lang.
