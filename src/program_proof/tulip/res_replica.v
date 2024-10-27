(** Global resources. *)
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip Require Import base stability.

Section res.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  Section replica_validated_ts.

    (** Set of transaction IDs that are validated on a replica in a group. *)

    Definition own_replica_validated_tss γ (gid rid : u64) (vtss : gset nat) : iProp Σ.
    Admitted.

    Definition is_replica_validated_ts γ (gid rid : u64) (vts : nat) : iProp Σ.
    Admitted.

    #[global]
    Instance is_replica_validated_persistent γ gid rid ts :
      Persistent (is_replica_validated_ts γ gid rid ts).
    Admitted.

    Lemma replica_validated_ts_insert {γ gid rid vtss} vts :
      own_replica_validated_tss γ gid rid vtss ==∗
      own_replica_validated_tss γ gid rid ({[vts]} ∪ vtss).
    Admitted.

    Lemma replica_validated_ts_witness {γ gid rid vtss} vts :
      vts ∈ vtss ->
      own_replica_validated_tss γ gid rid vtss -∗
      is_replica_validated_ts γ gid rid vts.
    Admitted.

    Lemma replica_validated_ts_elem_of γ gid rid vtss vts :
      is_replica_validated_ts γ gid rid vts -∗
      own_replica_validated_tss γ gid rid vtss -∗
      ⌜vts ∈ vtss⌝.
    Admitted.

  End replica_validated_ts.

  Section replica_key_validation.

    (** Mapping from keys to boolean lists encoding whether each key is
    validated at a particular timestamp. *)

    Definition own_replica_key_validation
      γ (gid rid : u64) (key : dbkey) (l : list bool) : iProp Σ.
    Admitted.

    Definition is_replica_key_validation_lb
      γ (gid rid : u64) (key : dbkey) (l : list bool) : iProp Σ.
    Admitted.

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
    Admitted.

    Lemma replica_key_validation_update {γ gid rid key l} l' :
      prefix l l' ->
      own_replica_key_validation γ gid rid key l ==∗
      own_replica_key_validation γ gid rid key l'.
    Admitted.

    Lemma replica_key_validation_witness γ gid rid key l :
      own_replica_key_validation γ gid rid key l -∗
      is_replica_key_validation_lb γ gid rid key l.
    Admitted.

    Lemma replica_key_validation_prefix γ gid rid key l lb :
      is_replica_key_validation_lb γ gid rid key lb -∗
      own_replica_key_validation γ gid rid key l -∗
      ⌜prefix lb l⌝.
    Admitted.

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
    Admitted.

    Lemma replica_key_validation_lb_weaken {γ gid rid key l} l' :
      prefix l' l ->
      is_replica_key_validation_lb γ gid rid key l -∗
      is_replica_key_validation_lb γ gid rid key l'.
    Admitted.

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
    Admitted.

  End replica_key_validation.

  Section dura_hist.

    (** Mapping from keys to durable histories on each replica. The durable
    history reflects all the commands up to the highest LSN of inconsistent
    commands. *)

    Definition own_dura_hist_half γ (rid : u64) (k : dbkey) (h : dbhist) : iProp Σ.
    Admitted.

    Lemma dura_hist_update {γ rid k h1 h2} h' :
      own_dura_hist_half γ rid k h1 -∗
      own_dura_hist_half γ rid k h2 ==∗
      own_dura_hist_half γ rid k h' ∗
      own_dura_hist_half γ rid k h'.
    Admitted.

    Lemma dura_hist_agree {γ rid k h1 h2} :
      own_dura_hist_half γ rid k h1 -∗
      own_dura_hist_half γ rid k h2 -∗
      ⌜h2 = h1⌝.
    Admitted.

  End dura_hist.

  Section replica_pts.

    (** Mapping from keys to the prepare timestamps on each replica. *)

    Definition own_replica_pts_half γ (rid : u64) (k : dbkey) (ts : nat) : iProp Σ.
    Admitted.

    Lemma replica_pts_update {γ rid k ts1 ts2} ts' :
      own_replica_pts_half γ rid k ts1 -∗
      own_replica_pts_half γ rid k ts2 ==∗
      own_replica_pts_half γ rid k ts' ∗
      own_replica_pts_half γ rid k ts'.
    Admitted.

    Lemma replica_pts_agree {γ rid k ts1 ts2} :
      own_replica_pts_half γ rid k ts1 -∗
      own_replica_pts_half γ rid k ts2 -∗
      ⌜ts2 = ts1⌝.
    Admitted.

    Lemma replica_pts_big_agree {γ rid ptsm1 ptsm2} :
      dom ptsm1 = dom ptsm2 ->
      ([∗ map] k ↦ pts ∈ ptsm1, own_replica_pts_half γ rid k pts) -∗
      ([∗ map] k ↦ pts ∈ ptsm2, own_replica_pts_half γ rid k pts) -∗
      ⌜ptsm2 = ptsm1⌝.
    Admitted.

    Lemma replica_pts_big_update {γ rid ptsm} ptsm' :
      dom ptsm = dom ptsm' ->
      ([∗ map] k ↦ pts ∈ ptsm, own_replica_pts_half γ rid k pts) -∗
      ([∗ map] k ↦ pts ∈ ptsm, own_replica_pts_half γ rid k pts) ==∗
      ([∗ map] k ↦ pts ∈ ptsm', own_replica_pts_half γ rid k pts) ∗
      ([∗ map] k ↦ pts ∈ ptsm', own_replica_pts_half γ rid k pts).
    Admitted.

  End replica_pts.

  Section replica_spts.

    (** Mapping from keys to the smallest preparable timestamps on each replica. *)

    Definition own_replica_spts_half γ (rid : u64) (k : dbkey) (ts : nat) : iProp Σ.
    Admitted.

    Lemma replica_spts_update {γ rid k ts1 ts2} ts' :
      own_replica_spts_half γ rid k ts1 -∗
      own_replica_spts_half γ rid k ts2 ==∗
      own_replica_spts_half γ rid k ts' ∗
      own_replica_spts_half γ rid k ts'.
    Admitted.

    Lemma replica_spts_agree {γ rid k ts1 ts2} :
      own_replica_spts_half γ rid k ts1 -∗
      own_replica_spts_half γ rid k ts2 -∗
      ⌜ts2 = ts1⌝.
    Admitted.

    Lemma replica_spts_big_agree {γ rid sptsm1 sptsm2} :
      dom sptsm1 = dom sptsm2 ->
      ([∗ map] k ↦ spts ∈ sptsm1, own_replica_spts_half γ rid k spts) -∗
      ([∗ map] k ↦ spts ∈ sptsm2, own_replica_spts_half γ rid k spts) -∗
      ⌜sptsm2 = sptsm1⌝.
    Admitted.

    Lemma replica_spts_big_update {γ rid sptsm} sptsm' :
      dom sptsm = dom sptsm' ->
      ([∗ map] k ↦ spts ∈ sptsm, own_replica_spts_half γ rid k spts) -∗
      ([∗ map] k ↦ spts ∈ sptsm, own_replica_spts_half γ rid k spts) ==∗
      ([∗ map] k ↦ spts ∈ sptsm', own_replica_spts_half γ rid k spts) ∗
      ([∗ map] k ↦ spts ∈ sptsm', own_replica_spts_half γ rid k spts).
    Admitted.

  End replica_spts.

  Section replica_commit_map.

    Definition own_replica_commit_map_half γ (rid : u64) (cm : gmap nat bool) : iProp Σ.
    Admitted.

    Lemma replica_commit_map_update {γ rid cm1 cm2} cm' :
      own_replica_commit_map_half γ rid cm1 -∗
      own_replica_commit_map_half γ rid cm2 ==∗
      own_replica_commit_map_half γ rid cm' ∗
      own_replica_commit_map_half γ rid cm'.
    Admitted.

    Lemma replica_commit_map_agree {γ rid cm1 cm2} :
      own_replica_commit_map_half γ rid cm1 -∗
      own_replica_commit_map_half γ rid cm2 -∗
      ⌜cm2 = cm1⌝.
    Admitted.

  End replica_commit_map.

  Section replica_currently_prepared_map.

    Definition own_replica_currently_prepared_map_half
      γ (rid : u64) (cpm : gmap nat dbmap) : iProp Σ.
    Admitted.

    Lemma replica_currently_prepared_map_update {γ rid cpm1 cpm2} cpm' :
      own_replica_currently_prepared_map_half γ rid cpm1 -∗
      own_replica_currently_prepared_map_half γ rid cpm2 ==∗
      own_replica_currently_prepared_map_half γ rid cpm' ∗
      own_replica_currently_prepared_map_half γ rid cpm'.
    Admitted.

    Lemma replica_currently_prepared_map_agree {γ rid cpm1 cpm2} :
      own_replica_currently_prepared_map_half γ rid cpm1 -∗
      own_replica_currently_prepared_map_half γ rid cpm2 -∗
      ⌜cpm2 = cpm1⌝.
    Admitted.

  End replica_currently_prepared_map.

  Section replica_ballot.

    (** Mapping from transaction IDs to booleans indicating whether they are
    prepared on a replica in a group at a certain rank. *)

    Definition own_replica_ballots γ (gid rid : u64) (bs : gmap nat ballot) : iProp Σ.
    Admitted.

    Definition is_replica_ballot_lb γ (gid rid : u64) (ts : nat) (blt : ballot) : iProp Σ.
    Admitted.

    #[global]
    Instance is_replica_ballot_lb_persistent γ gid rid ts blt :
      Persistent (is_replica_ballot_lb γ gid rid ts blt).
    Admitted.

    Definition is_replica_pdec_at_rank γ (gid rid : u64) (ts rank : nat) (p : bool) : iProp Σ :=
      ∃ blt, is_replica_ballot_lb γ gid rid ts blt ∧ ⌜blt !! rank = Some (Accept p)⌝.

  End replica_ballot.

End res.
