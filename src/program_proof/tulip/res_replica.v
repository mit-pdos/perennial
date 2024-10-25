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

    Lemma replica_validated_ts_insert γ gid rid vtss vts :
      own_replica_validated_tss γ gid rid vtss ==∗
      own_replica_validated_tss γ gid rid ({[vts]} ∪ vtss).
    Admitted.

    Lemma replica_validated_ts_witness γ gid rid vtss vts :
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

  End replica_key_validation.

  Section replica_ballot.

    (** Mapping from transaction IDs to whether they are prepared on a replica
    in a group at a certain rank. *)

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
