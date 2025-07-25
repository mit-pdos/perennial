From iris.algebra Require Import mono_nat mono_list gmap_view gset.
From iris.algebra.lib Require Import dfrac_agree.
From Perennial.Helpers Require Import gmap_algebra.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm Require Import big_sep.
From Perennial.program_proof.rsm.pure Require Import fin_maps.
From Perennial.program_proof.tulip Require Import base stability.

Section res.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  Section replica_validated_ts.

    (** Set of transaction IDs that are validated on a replica in a group. *)

    Definition is_replica_validated_ts γ (gid rid : u64) (vts : nat) : iProp Σ :=
      own γ.(replica_validated_ts) {[ (gid, rid) := gmap_view_frag vts DfracDiscarded tt ]}.

    Definition own_replica_validated_tss_auth
      γ (gid rid : u64) (vtss : gset nat) : iProp Σ :=
      own γ.(replica_validated_ts) {[ (gid, rid) := gmap_view_auth (DfracOwn 1) (gset_to_gmap tt vtss) ]}.

    Definition own_replica_validated_tss γ (gid rid : u64) (vtss : gset nat) : iProp Σ :=
      own_replica_validated_tss_auth γ gid rid vtss ∗
      ([∗ set] t ∈ vtss, is_replica_validated_ts γ gid rid t).

    #[global]
    Instance is_replica_validated_persistent γ gid rid ts :
      Persistent (is_replica_validated_ts γ gid rid ts).
    Proof. apply _. Defined.

    Lemma replica_validated_ts_insert {γ gid rid vtss} vts :
      own_replica_validated_tss γ gid rid vtss ==∗
      own_replica_validated_tss γ gid rid ({[vts]} ∪ vtss).
    Proof.
      destruct (decide (vts ∈ vtss)) as [Hin | Hnotin].
      { replace (_ ∪ _) with vtss by set_solver.
        by iIntros.
      }
      iIntros "[Hauth #Hfrags]".
      set vtss' := _ ∪ _.
      iAssert (own_replica_validated_tss_auth γ gid rid vtss' ∗
               is_replica_validated_ts γ gid rid vts)%I
        with "[> Hauth]" as "[Hauth #Hfrag]".
      { iRevert "Hauth".
        rewrite -own_op.
        iApply own_update.
        rewrite singleton_op.
        apply singleton_update.
        rewrite gset_to_gmap_union_singleton.
        apply: gmap_view_alloc; last done; last done.
        by rewrite lookup_gset_to_gmap_None.
      }
      iFrame.
      iModIntro.
      by iApply big_sepS_insert_2.
    Qed.

    Lemma replica_validated_ts_witness {γ gid rid vtss} vts :
      vts ∈ vtss ->
      own_replica_validated_tss γ gid rid vtss -∗
      is_replica_validated_ts γ gid rid vts.
    Proof.
      iIntros (Hin) "[_ Hfrags]".
      by iApply (big_sepS_elem_of with "Hfrags").
    Qed.

    Lemma replica_validated_ts_elem_of γ gid rid vtss vts :
      is_replica_validated_ts γ gid rid vts -∗
      own_replica_validated_tss γ gid rid vtss -∗
      ⌜vts ∈ vtss⌝.
    Proof.
      iIntros "Hfrag [Hauth _]".
      iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      apply gmap_view_both_dfrac_valid_discrete_total in Hvalid.
      destruct Hvalid as (v' & _ & _ & Hlookup & _ & _).
      apply elem_of_dom_2 in Hlookup.
      rewrite dom_gset_to_gmap in Hlookup.
      done.
    Qed.

  End replica_validated_ts.

  Section replica_key_validation.

    (** Mapping from keys to boolean lists encoding whether each key is
    validated at a particular timestamp. *)

    Definition own_replica_key_validation
      γ (gid rid : u64) (key : dbkey) (l : list bool) : iProp Σ :=
      own γ.(replica_key_validation) {[ (gid, rid, key) := ●ML{#1} l ]}.

    Definition is_replica_key_validation_lb
      γ (gid rid : u64) (key : dbkey) (l : list bool) : iProp Σ :=
      own γ.(replica_key_validation) {[ (gid, rid, key) := ◯ML l ]}.

    Definition is_replica_key_validation_length_lb
      γ (gid rid : u64) (key : dbkey) (n : nat) : iProp Σ :=
      ∃ l, is_replica_key_validation_lb γ gid rid key l ∧ ⌜(n ≤ length l)%nat⌝.

    Definition is_replica_key_validation_at
      γ (gid rid : u64) (key : dbkey) (ts : nat) (b : bool) : iProp Σ :=
      ∃ l, is_replica_key_validation_lb γ gid rid key l ∧ ⌜l !! ts = Some b⌝.

    Definition is_replica_key_validated_at
      γ (gid rid : u64) (key : dbkey) (ts : nat) : iProp Σ :=
      is_replica_key_validation_at γ gid rid key ts true.

    Definition is_replica_key_invalidated_at
      γ (gid rid : u64) (key : dbkey) (ts : nat) : iProp Σ :=
      is_replica_key_validation_at γ gid rid key ts false.

    #[global]
    Instance is_replica_key_validation_lb_persistent γ gid rid key l :
      Persistent (is_replica_key_validation_lb γ gid rid key l).
    Proof. apply _. Defined.

    Lemma replica_key_validation_update {γ gid rid key l} l' :
      prefix l l' ->
      own_replica_key_validation γ gid rid key l ==∗
      own_replica_key_validation γ gid rid key l'.
    Proof.
      intros Hprefix.
      iApply own_update.
      apply singleton_update.
      by apply mono_list_update.
    Qed.

    Lemma replica_key_validation_witness γ gid rid key l :
      own_replica_key_validation γ gid rid key l -∗
      is_replica_key_validation_lb γ gid rid key l.
    Proof.
      iApply own_mono.
      apply singleton_included_mono.
      apply mono_list_included.
    Qed.

    Lemma replica_key_validation_prefix γ gid rid key l lb :
      is_replica_key_validation_lb γ gid rid key lb -∗
      own_replica_key_validation γ gid rid key l -∗
      ⌜prefix lb l⌝.
    Proof.
      iIntros "Hh Hlb".
      iDestruct (own_valid_2 with "Hh Hlb") as %Hvalid.
      iPureIntro. revert Hvalid.
      rewrite singleton_op singleton_valid.
      rewrite cmra_comm mono_list_both_dfrac_valid_L.
      by intros [_ ?].
    Qed.

    Lemma replica_key_validation_lookup γ gid rid key l ts b :
      is_replica_key_validation_at γ gid rid key ts b -∗
      own_replica_key_validation γ gid rid key l -∗
      ⌜l !! ts = Some b⌝.
    Proof.
      iIntros "(%lb & Hlb & %Hb) Hl".
      iDestruct (replica_key_validation_prefix with "Hlb Hl") as %Hprefix.
      iPureIntro.
      by eapply prefix_lookup_Some.
    Qed.

    Lemma replica_key_validation_lb_lookup γ gid rid key l ts b :
      (ts < length l)%nat ->
      is_replica_key_validation_at γ gid rid key ts b -∗
      is_replica_key_validation_lb γ gid rid key l -∗
      ⌜l !! ts = Some b⌝.
    Proof.
      iIntros (Hlen) "(%lb & #Hlb & %Hv) #Hl".
      iDestruct (own_valid_2 with "Hl Hlb") as %Hvalid.
      iPureIntro.
      rewrite singleton_op singleton_valid mono_list_lb_op_valid_L in Hvalid.
      destruct Hvalid as [Hprefix | Hprefix].
      { by rewrite (prefix_lookup_lt _ _ _ Hlen Hprefix). }
      { by eapply prefix_lookup_Some. }
    Qed.

    Lemma replica_key_validation_lb_weaken {γ gid rid key l} l' :
      prefix l' l ->
      is_replica_key_validation_lb γ gid rid key l -∗
      is_replica_key_validation_lb γ gid rid key l'.
    Proof.
      iIntros (Hprefix).
      iApply own_mono.
      apply singleton_included_mono.
      by apply mono_list_lb_mono.
    Qed.

    Lemma replica_key_validation_at_length γ gid rid key ts b :
      is_replica_key_validation_at γ gid rid key ts b -∗
      is_replica_key_validation_length_lb γ gid rid key (S ts).
    Proof.
      iIntros "(%lb & Hlb & %Hb)".
      iFrame.
      iPureIntro.
      apply lookup_lt_Some in Hb.
      lia.
    Qed.

    Lemma replica_key_validation_big_update {γ gid rid kvdm} kvdm' :
      map_Forall2 (λ _ l1 l2, prefix l1 l2) kvdm kvdm' ->
      ([∗ map] k ↦ l ∈ kvdm, own_replica_key_validation γ gid rid k l) ==∗
      ([∗ map] k ↦ l ∈ kvdm', own_replica_key_validation γ gid rid k l).
    Proof.
      iIntros (Hprefix) "Hkvdlm".
      rewrite -big_sepM_bupd.
      iApply (big_sepM_impl_dom_eq with "Hkvdlm").
      { by apply map_Forall2_dom_L in Hprefix. }
      iIntros (k l1 l2 Hl1 Hl2) "!>".
      iApply replica_key_validation_update.
      apply map_Forall2_forall in Hprefix as [Hprefix _].
      by eapply Hprefix.
    Qed.

  End replica_key_validation.

  Section replica_clog.

    (** Per-replica consistent log. *)

    Definition own_replica_clog_half γ (gid rid : u64) (l : list ccommand) : iProp Σ :=
      own γ.(replica_clog) {[ (gid, rid) := (to_dfrac_agree (A:=clogO) (DfracOwn (1 / 2)) l) ]}.

    Lemma replica_clog_update {γ gid rid l1 l2} l' :
      own_replica_clog_half γ gid rid l1 -∗
      own_replica_clog_half γ gid rid l2 ==∗
      own_replica_clog_half γ gid rid l' ∗
      own_replica_clog_half γ gid rid l'.
    Proof.
      iIntros "Hv1 Hv2".
      iCombine "Hv1 Hv2" as "Hv".
      rewrite -own_op singleton_op.
      iApply (own_update with "Hv").
      apply singleton_update.
      apply dfrac_agree_update_2.
      by rewrite dfrac_op_own Qp.half_half.
    Qed.

    Lemma replica_clog_agree {γ gid rid l1 l2} :
      own_replica_clog_half γ gid rid l1 -∗
      own_replica_clog_half γ gid rid l2 -∗
      ⌜l2 = l1⌝.
    Proof.
      iIntros "Hv1 Hv2".
      iDestruct (own_valid_2 with "Hv1 Hv2") as %Hvalid.
      rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hvalid.
      by destruct Hvalid as [_ ?].
    Qed.

  End replica_clog.

  Section replica_ilog.

    (** Per-replica inconsistent log. *)

    Definition own_replica_ilog_frac
      γ (gid rid : u64) (q : Qp) (l : list (nat * icommand)) : iProp Σ :=
      own γ.(replica_ilog) {[ (gid, rid) := (to_dfrac_agree (A:=ilogO) (DfracOwn q) l) ]}.

    Definition own_replica_ilog_quarter γ (gid rid : u64) (l : list (nat * icommand)) : iProp Σ :=
      own_replica_ilog_frac γ gid rid (1 / 4) l.

    Definition own_replica_ilog_half γ (gid rid : u64) (l : list (nat * icommand)) : iProp Σ :=
      own_replica_ilog_frac γ gid rid (1 / 2) l.

    Lemma replica_ilog_combine {γ gid rid l1 l2} :
      own_replica_ilog_quarter γ gid rid l1 -∗
      own_replica_ilog_quarter γ gid rid l2 -∗
      own_replica_ilog_half γ gid rid l1 ∗ ⌜l2 = l1⌝.
    Proof.
      iIntros "Hl1 Hl2".
      iDestruct (own_valid_2 with "Hl1 Hl2") as %Hvalid.
      rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hvalid.
      destruct Hvalid as [_ Heq]. subst l2.
      iCombine "Hl1 Hl2" as "Hl".
      rewrite -dfrac_agree_op dfrac_op_own Qp.quarter_quarter.
      by iFrame.
    Qed.

    Lemma replica_ilog_split {γ gid rid l} :
      own_replica_ilog_half γ gid rid l -∗
      own_replica_ilog_quarter γ gid rid l ∗ own_replica_ilog_quarter γ gid rid l.
    Proof.
      iIntros "Hl".
      rewrite -own_op singleton_op -dfrac_agree_op dfrac_op_own Qp.quarter_quarter.
      by iFrame.
    Qed.

    Lemma replica_ilog_update {γ gid rid l1 l2} l' :
      own_replica_ilog_half γ gid rid l1 -∗
      own_replica_ilog_half γ gid rid l2 ==∗
      own_replica_ilog_half γ gid rid l' ∗
      own_replica_ilog_half γ gid rid l'.
    Proof.
      iIntros "Hv1 Hv2".
      iCombine "Hv1 Hv2" as "Hv".
      rewrite -own_op singleton_op.
      iApply (own_update with "Hv").
      apply singleton_update.
      apply dfrac_agree_update_2.
      by rewrite dfrac_op_own Qp.half_half.
    Qed.

    Lemma replica_ilog_agree {γ gid rid l1 l2} q1 q2 :
      own_replica_ilog_frac γ gid rid q1 l1 -∗
      own_replica_ilog_frac γ gid rid q2 l2 -∗
      ⌜l2 = l1⌝.
    Proof.
      iIntros "Hv1 Hv2".
      iDestruct (own_valid_2 with "Hv1 Hv2") as %Hvalid.
      rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hvalid.
      by destruct Hvalid as [_ ?].
    Qed.

  End replica_ilog.

  Section replica_ballot.

    (** Mapping from transaction IDs to booleans indicating whether they are
    prepared on a replica in a group at a certain rank. *)

    Definition own_replica_ballot_map_auth γ (gid rid : u64) (gnames : gmap nat gname) : iProp Σ :=
      own γ.(replica_ballot) {[ (gid, rid) := gmap_view_auth (DfracOwn 1) (to_agree <$> gnames) ]}.

    Definition own_replica_ballot_map_frag γ (gid rid : u64) (ts : nat) (α : gname) : iProp Σ :=
      own γ.(replica_ballot) {[ (gid, rid) := gmap_view_frag ts DfracDiscarded (to_agree α) ]}.

    Definition own_replica_ballot_map γ (gid rid : u64) (bs : gmap nat ballot) : iProp Σ :=
      ∃ gnames,
        own_replica_ballot_map_auth γ gid rid gnames ∗
        ([∗ map] t ↦ α; l ∈ gnames; bs, own α (mono_list_auth (DfracOwn 1) l)) ∗
        ([∗ map] t ↦ α ∈ gnames, own_replica_ballot_map_frag γ gid rid t α).

    Definition is_replica_ballot_lb γ (gid rid : u64) (ts : nat) (blt : ballot) : iProp Σ :=
      ∃ α,
        own_replica_ballot_map_frag γ gid rid ts α ∗ own α (mono_list_lb blt).

    #[global]
    Instance is_replica_ballot_lb_persistent γ gid rid ts blt :
      Persistent (is_replica_ballot_lb γ gid rid ts blt).
    Proof. apply _. Defined.

    Definition is_replica_pdec_at_rank γ (gid rid : u64) (ts rank : nat) (p : bool) : iProp Σ :=
      ∃ blt, is_replica_ballot_lb γ gid rid ts blt ∧ ⌜blt !! rank = Some (Accept p)⌝.

    Lemma replica_ballot_insert {γ gid rid bs} ts l :
      bs !! ts = None ->
      own_replica_ballot_map γ gid rid bs ==∗
      own_replica_ballot_map γ gid rid (<[ts := l]> bs).
    Proof.
      iIntros (Hnotin) "Hauth".
      iDestruct "Hauth" as (gnames) "(Hauth & Hblts & #Hfrags)".
      iMod (own_alloc (●ML l)) as (α) "Hblt".
      { apply mono_list_auth_valid. }
      iDestruct (big_sepM2_dom with "Hblts") as %Hdom.
      assert (Hgnotin : gnames !! ts = None).
      { by rewrite -not_elem_of_dom Hdom not_elem_of_dom. }
      iAssert (own_replica_ballot_map_auth γ gid rid (<[ts := α]> gnames) ∗
               own_replica_ballot_map_frag γ gid rid ts α)%I
        with "[> Hauth]" as "[Hauth #Hfrag]".
      { iRevert "Hauth".
        rewrite -own_op.
        iApply own_update.
        rewrite singleton_op.
        apply singleton_update.
        rewrite fmap_insert.
        apply: gmap_view_alloc; [|done..].
        by rewrite lookup_fmap Hgnotin.
      }
      iFrame.
      iModIntro.
      iSplit.
      { iApply (big_sepM2_insert_2 with "[Hblt] Hblts"); first done. }
      by iApply big_sepM_insert_2.
    Qed.

    Lemma replica_ballot_update {γ gid rid bs} ts l l' :
      bs !! ts = Some l ->
      prefix l l' ->
      own_replica_ballot_map γ gid rid bs ==∗
      own_replica_ballot_map γ gid rid (<[ts := l']> bs).
    Proof.
      iIntros (Hl Hprefix) "Hauth".
      iDestruct "Hauth" as (gnames) "(Hauth & Hblts & #Hfrags)".
      iDestruct (big_sepM2_dom with "Hblts") as %Hdom.
      assert (is_Some (gnames !! ts)) as [α Hα].
      { by rewrite -elem_of_dom Hdom elem_of_dom. }
      iDestruct (big_sepM2_delete with "Hblts") as "[Hblt Hblts]".
      { apply Hα. }
      { apply Hl. }
      iMod (own_update with "Hblt") as "Hblt".
      { apply mono_list_update, Hprefix. }
      iDestruct (big_sepM2_insert_2 _ _ _ ts with "[Hblt] Hblts") as "Hblts".
      { iFrame "Hblt". }
      rewrite 2!insert_delete_eq.
      iFrame.
      rewrite insert_id; last done.
      by iFrame "∗ #".
    Qed.

    Lemma replica_ballot_witness {γ gid rid bs} ts l :
      bs !! ts = Some l ->
      own_replica_ballot_map γ gid rid bs -∗
      is_replica_ballot_lb γ gid rid ts l.
    Proof.
      iIntros (Hl) "Hauth".
      iDestruct "Hauth" as (gnames) "(Hauth & Hblts & #Hfrags)".
      iDestruct (big_sepM2_dom with "Hblts") as %Hdom.
      assert (is_Some (gnames !! ts)) as [α Hα].
      { by rewrite -elem_of_dom Hdom elem_of_dom. }
      iDestruct (big_sepM2_lookup with "Hblts") as "Hblt".
      { apply Hα. }
      { apply Hl. }
      iDestruct (big_sepM_lookup with "Hfrags") as "Hfrag".
      { apply Hα. }
      iFrame "Hfrag".
      iApply (own_mono with "Hblt").
      apply mono_list_included.
    Qed.

    Lemma replica_ballot_lookup {γ gid rid bs} ts lb :
      is_replica_ballot_lb γ gid rid ts lb -∗
      own_replica_ballot_map γ gid rid bs -∗
      ⌜∃ l, bs !! ts = Some l ∧ prefix lb l⌝.
    Proof.
      iIntros "#Hlb Hauth".
      iDestruct "Hauth" as (gnames) "(Hauth & Hblts & #Hfrags)".
      iDestruct "Hlb" as (α) "[Hfrag Hlb]".
      iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      apply gmap_view_both_dfrac_valid_discrete_total in Hvalid.
      destruct Hvalid as (v' & _ & _ & Hlookup & _ & Hincl).
      apply lookup_fmap_Some in Hlookup as (b & <- & Hb).
      apply to_agree_included_L in Hincl.
      subst b.
      iDestruct (big_sepM2_dom with "Hblts") as %Hdom.
      assert (is_Some (bs !! ts)) as [blt Hblt].
      { by rewrite -elem_of_dom -Hdom elem_of_dom. }
      iDestruct (big_sepM2_lookup with "Hblts") as "Hblt".
      { apply Hb. }
      { apply Hblt. }
      iDestruct (own_valid_2 with "Hblt Hlb") as %Hvalid.
      iPureIntro.
      apply mono_list_both_dfrac_valid_L in Hvalid as [_ Hprefix].
      by eauto.
    Qed.

    Lemma replica_ballot_prefix {γ gid rid bs} ts l lb :
      bs !! ts = Some l ->
      is_replica_ballot_lb γ gid rid ts lb -∗
      own_replica_ballot_map γ gid rid bs -∗
      ⌜prefix lb l⌝.
    Proof.
      iIntros (Hl) "#Hlb Hauth".
      iDestruct "Hauth" as (gnames) "(Hauth & Hblts & #Hfrags)".
      iDestruct "Hlb" as (α) "[Hfrag Hlb]".
      iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      apply gmap_view_both_dfrac_valid_discrete_total in Hvalid.
      destruct Hvalid as (v' & _ & _ & Hlookup & _ & Hincl).
      apply lookup_fmap_Some in Hlookup as (b & <- & Hb).
      apply to_agree_included_L in Hincl.
      subst b.
      iDestruct (big_sepM2_lookup with "Hblts") as "Hblt".
      { apply Hb. }
      { apply Hl. }
      iDestruct (own_valid_2 with "Hblt Hlb") as %Hvalid.
      iPureIntro.
      by apply mono_list_both_dfrac_valid_L in Hvalid as [_ Hprefix].
    Qed.

  End replica_ballot.

  Section replica_backup_vote.

    (** Mappings from transaction IDs and ranks to coordinator IDs to which vote
    of the transaction ID and rank is casted by this replica. This is used to
    ensure no two replicas could serve as the coordinator in the same term. *)

    Definition is_replica_backup_vote
      γ (gid rid : u64) (ts rank : nat) (cid : coordid) : iProp Σ :=
      own γ.(replica_vote)
              {[ (gid, rid) := (gmap_view_frag (ts, rank) DfracDiscarded (to_agree cid)) ]}.

    Definition own_replica_backup_vote_map_auth
      γ (gid rid : u64) (m : gmap (nat * nat) coordid) : iProp Σ :=
      own γ.(replica_vote) {[ (gid, rid) := (gmap_view_auth (DfracOwn 1) (to_agree <$> m)) ]}.

    Definition own_replica_backup_vote_map
      γ (gid rid : u64) (bvm : gmap nat (gmap nat coordid)) : iProp Σ :=
      ∃ m : gmap (nat * nat) coordid,
        own_replica_backup_vote_map_auth γ gid rid m ∗
        (⌜∀ t r c, m !! (t, r) = Some c -> ∃ im, bvm !! t = Some im ∧ im !! r = Some c⌝).

    #[global]
    Instance is_replica_backup_vote_persistent γ gid rid ts rank cid :
      Persistent (is_replica_backup_vote γ gid rid ts rank cid).
    Proof. apply _. Defined.

    (* TODO: doesn't need update modality *)
    Lemma replica_backup_vote_init {γ gid rid bvm} ts :
      bvm !! ts = None ->
      own_replica_backup_vote_map γ gid rid bvm ==∗
      own_replica_backup_vote_map γ gid rid (<[ts := ∅]> bvm).
    Proof.
      iIntros (Hnotin) "Hauth".
      iDestruct "Hauth" as (m) "[Hauth %Hincl]".
      iExists m.
      iFrame.
      iPureIntro.
      intros t r c Hc.
      destruct (decide (t = ts)) as [-> | Hne].
      { specialize (Hincl _ _ _ Hc).
        destruct Hincl as (im & Him & _).
        by rewrite Hnotin in Him.
      }
      rewrite lookup_insert_ne; last done.
      by apply Hincl.
    Qed.

    Lemma replica_backup_vote_insert {γ gid rid bvm vm} ts rank cid :
      bvm !! ts = Some vm ->
      vm !! rank = None ->
      own_replica_backup_vote_map γ gid rid bvm ==∗
      own_replica_backup_vote_map γ gid rid (<[ts := (<[rank := cid]> vm)]> bvm) ∗
      is_replica_backup_vote γ gid rid ts rank cid.
    Proof.
      iIntros (Hm Hnotin) "Hauth".
      iDestruct "Hauth" as (m) "[Hauth %Hincl]".
      iAssert (own_replica_backup_vote_map_auth γ gid rid (<[(ts, rank) := cid]> m) ∗
               is_replica_backup_vote γ gid rid ts rank cid)%I
        with "[> Hauth]" as "[Hauth #Hfrag]".
      { iRevert "Hauth".
        rewrite -own_op.
        iApply own_update.
        rewrite singleton_op.
        apply singleton_update.
        rewrite fmap_insert. apply: gmap_view_alloc; [|done..].
        rewrite lookup_fmap.
        destruct (m !! (ts, rank)) as [c' |] eqn:Hin; last done.
        specialize (Hincl _ _ _ Hin).
        destruct Hincl as (im & Him & Hc').
        rewrite Hm in Him. inv Him.
      }
      iFrame "∗ #".
      iPureIntro.
      intros t r c Hc.
      destruct (decide (t = ts)) as [-> | Hne].
      { rewrite lookup_insert_eq.
        destruct (decide (r = rank)) as [-> | Hner].
        { rewrite lookup_insert_eq in Hc. inv Hc.
          exists (<[rank := c]> vm).
          split; first done.
          by rewrite lookup_insert_eq.
        }
        { rewrite lookup_insert_ne in Hc; last first.
          { intros Hcontra. congruence. }
          specialize (Hincl _ _ _ Hc).
          destruct Hincl as (im & Him & Himr).
          rewrite Hm in Him. inv Him.
          exists (<[rank := cid]> im).
          split; first done.
          by rewrite lookup_insert_ne.
        }
      }
      { rewrite lookup_insert_ne in Hc; last first.
        { intros Hcontra. congruence. }
        rewrite lookup_insert_ne; last done.
        by apply Hincl.
      }
    Qed.

    Lemma replica_backup_vote_agree γ gid rid ts rank cid1 cid2 :
      is_replica_backup_vote γ gid rid ts rank cid1 -∗
      is_replica_backup_vote γ gid rid ts rank cid2 -∗
      ⌜cid2 = cid1⌝.
    Proof.
      iIntros "Hv1 Hv2".
      iDestruct (own_valid_2 with "Hv1 Hv2") as %Hvalid.
      rewrite singleton_op singleton_valid gmap_view_frag_op_valid in Hvalid.
      destruct Hvalid as [_ Hagree].
      by apply to_agree_op_inv_L in Hagree.
    Qed.

  End replica_backup_vote.

  Section replica_backup_token.

    (** Mappings from transaction IDs and ranks to sets of groups IDs. This is
    used to ensure that the same replica can become the coordinator at a certain
    rank for a certain group at most once. *)

    Definition own_replica_backup_tokens_map_auth
      γ (gid rid : u64) (s : gset (nat * nat * u64)) : iProp Σ :=
      own γ.(replica_token) {[ (gid, rid) := gmap_view_auth (DfracOwn 1) (gset_to_gmap tt s) ]}.

    Definition own_replica_backup_tokens_map
      γ (gid rid : u64) (bvm : gmap nat (gmap nat (gset u64))) : iProp Σ :=
      ∃ s : gset (nat * nat * u64),
        own_replica_backup_tokens_map_auth γ gid rid s ∗
        (⌜∀ t r g, (t, r, g) ∈ s -> ∃ im, bvm !! t = Some im ∧ ∃ ix, im !! r = Some ix ∧ g ∈ ix⌝).

    Definition own_replica_backup_token
      γ (gid rid : u64) (ts rank : nat) (tgid : u64) : iProp Σ :=
      own γ.(replica_token)
              {[ (gid, rid) := gmap_view_frag (ts, rank, tgid) (DfracOwn 1) tt ]}.

    (* TODO: doesn't need update modality *)
    Lemma replica_backup_token_init {γ gid rid btm} ts :
      btm !! ts = None ->
      own_replica_backup_tokens_map γ gid rid btm ==∗
      own_replica_backup_tokens_map γ gid rid (<[ts := ∅]> btm).
    Proof.
      iIntros (Hnotin) "Hauth".
      iDestruct "Hauth" as (m) "[Hauth %Hincl]".
      iExists m.
      iFrame.
      iPureIntro.
      intros t r c Hc.
      destruct (decide (t = ts)) as [-> | Hne].
      { specialize (Hincl _ _ _ Hc).
        destruct Hincl as (im & Him & _).
        by rewrite Hnotin in Him.
      }
      rewrite lookup_insert_ne; last done.
      by apply Hincl.
    Qed.

    Lemma replica_backup_token_insert {γ gid rid btm tm} ts rank tgids :
      btm !! ts = Some tm ->
      tm !! rank = None ->
      own_replica_backup_tokens_map γ gid rid btm ==∗
      own_replica_backup_tokens_map γ gid rid (<[ts := (<[rank := tgids]> tm)]> btm) ∗
      ([∗ set] tgid ∈ tgids, own_replica_backup_token γ gid rid ts rank tgid).
    Proof.
      iIntros (Htm Hnotin) "Hauth".
      iDestruct "Hauth" as (s) "[Hauth %Hincl]".
      set tksnew : gset (nat * nat * u64) := set_map (λ g, (ts, rank, g)) tgids.
      iAssert (own_replica_backup_tokens_map_auth γ gid rid (tksnew ∪ s) ∗
               ([∗ set] g ∈ tgids, own_replica_backup_token γ gid rid ts rank g))%I
        with "[> Hauth]" as "[Hauth Hfrags]".
      { iRevert "Hauth".
        rewrite -big_opS_own_1 -own_op.
        iApply own_update.
        etrans.
        { apply singleton_update.
          apply: (gmap_view_alloc_big _ (gset_to_gmap () tksnew) (DfracOwn 1)).
          { rewrite map_disjoint_dom 2!dom_gset_to_gmap.
            subst tksnew.
            intros [[t r] g] Hin1 Hin2.
            specialize (Hincl _ _ _ Hin2).
            apply elem_of_map in Hin1.
            destruct Hin1 as (g' & Heq & Hg').
            inv Heq.
            destruct Hincl as (im & Him & Hix).
            rewrite Htm in Him. inv Him.
            destruct Hix as (ix & Hix & Hinix).
            by rewrite Hnotin in Hix.
          }
          { done. }
          { done. }
        }
        etrans; last first.
        { apply cmra_update_op.
          { reflexivity. }
          apply cmra_update_included.
          apply singleton_big_opS_le.
        }
        rewrite singleton_op.
        apply singleton_update.
        replace (_ ∪ _) with (gset_to_gmap () (tksnew ∪ s)); last first.
        { apply map_eq.
          intros tg.
          rewrite lookup_union.
          rewrite 3!lookup_gset_to_gmap.
          destruct (decide (tg ∈ tksnew)) as [Htgin | Htgnotin].
          { rewrite option_guard_True.
            { rewrite option_guard_True; last done.
              by rewrite union_Some_l.
            }
            set_solver.
          }
          rewrite (option_guard_False (tg ∈ tksnew)); last done.
          rewrite option_union_left_id.
          destruct (decide (tg ∈ s)) as [Htgin' | Htgnotin'].
          { rewrite option_guard_True.
            { by rewrite option_guard_True. }
            set_solver.
          }
          { rewrite option_guard_False.
            { by rewrite option_guard_False. }
            set_solver.
          }
        }
        by rewrite big_opM_gset_to_gmap big_opS_set_map.
      }
      iFrame.
      iPureIntro.
      intros t r g Hin.
      destruct (decide (t = ts)) as [-> | Hne]; last first.
      { rewrite lookup_insert_ne; last done.
        apply Hincl.
        apply elem_of_union in Hin.
        destruct Hin as [Hin | ?]; last done.
        apply elem_of_map in Hin.
        destruct Hin as (g' & Heq & _).
        inv Heq.
      }
      rewrite lookup_insert_eq.
      exists (<[rank:=tgids]> tm).
      split; first done.
      destruct (decide (r = rank)) as [-> | Hne]; last first.
      { rewrite lookup_insert_ne; last done.
        apply elem_of_union in Hin.
        destruct Hin as [Hin | Hin]; last first.
        { specialize (Hincl _ _ _ Hin).
          destruct Hincl as (im & Him & Hix).
          rewrite Htm in Him. by inv Him.
        }
        apply elem_of_map in Hin.
        destruct Hin as (g' & Heq & _).
        inv Heq.
      }
      rewrite lookup_insert_eq.
      exists tgids.
      split; first done.
      apply elem_of_union in Hin as [Hin | Hin]; last first.
      { specialize (Hincl _ _ _ Hin).
        destruct Hincl as (im & Him & Hix).
        rewrite Htm in Him. inv Him.
        destruct Hix as (ix & Hix & _).
        by rewrite Hnotin in Hix.
      }
      apply elem_of_map in Hin as (g' & Heq & Hg').
      by inv Heq.
    Qed.

    Lemma replica_backup_token_excl γ gid rid ts rank tgid :
      own_replica_backup_token γ gid rid ts rank tgid -∗
      own_replica_backup_token γ gid rid ts rank tgid -∗
      False.
    Proof.
      iIntros "Ht1 Ht2".
      iDestruct (own_valid_2 with "Ht1 Ht2") as %Hvalid.
      rewrite singleton_op singleton_valid gmap_view_frag_op_valid in Hvalid.
      destruct Hvalid as [Hcontra _].
      by apply dfrac_valid_own_r in Hcontra.
    Qed.

  End replica_backup_token.

  Section replica_ilog_fname.

    Definition is_replica_ilog_fname γ (gid rid : u64) (fname : byte_string) : iProp Σ :=
      own γ.(replica_ilog_fname) {[ (gid, rid) := (to_agree (A:=byte_stringO) fname) ]}.

    #[global]
    Instance is_replica_ilog_fname_persistent γ gid rid fname :
      Persistent (is_replica_ilog_fname γ gid rid fname).
    Proof. apply _. Defined.

    Lemma replica_ilog_fname_agree {γ gid rid fname1 fname2} :
      is_replica_ilog_fname γ gid rid fname1 -∗
      is_replica_ilog_fname γ gid rid fname2 -∗
      ⌜fname2 = fname1⌝.
    Proof.
      iIntros "Hv1 Hv2".
      iDestruct (own_valid_2 with "Hv1 Hv2") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      by apply to_agree_op_inv_L in Hvalid.
    Qed.

  End replica_ilog_fname.

End res.
