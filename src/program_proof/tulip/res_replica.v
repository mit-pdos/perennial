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

  Section replica_clog.

    (** Per-replica consistent log. *)

    Definition own_replica_clog_half γ (rid : u64) (l : list ccommand) : iProp Σ.
    Admitted.

    Lemma replica_clog_update {γ rid l1 l2} l' :
      own_replica_clog_half γ rid l1 -∗
      own_replica_clog_half γ rid l2 ==∗
      own_replica_clog_half γ rid l' ∗
      own_replica_clog_half γ rid l'.
    Admitted.

    Lemma replica_clog_agree {γ rid l1 l2} :
      own_replica_clog_half γ rid l1 -∗
      own_replica_clog_half γ rid l2 -∗
      ⌜l2 = l1⌝.
    Admitted.

  End replica_clog.

  Section replica_ilog.

    (** Per-replica inconsistent log. *)

    Definition own_replica_ilog_half γ (rid : u64) (l : list (nat * icommand)) : iProp Σ.
    Admitted.

    Lemma replica_ilog_update {γ rid l1 l2} l' :
      own_replica_ilog_half γ rid l1 -∗
      own_replica_ilog_half γ rid l2 ==∗
      own_replica_ilog_half γ rid l' ∗
      own_replica_ilog_half γ rid l'.
    Admitted.

    Lemma replica_ilog_agree {γ rid l1 l2} :
      own_replica_ilog_half γ rid l1 -∗
      own_replica_ilog_half γ rid l2 -∗
      ⌜l2 = l1⌝.
    Admitted.

  End replica_ilog.

  Section replica_ballot.

    (** Mapping from transaction IDs to booleans indicating whether they are
    prepared on a replica in a group at a certain rank. *)

    Definition own_replica_ballot_map γ (gid rid : u64) (bs : gmap nat ballot) : iProp Σ.
    Admitted.

    Definition is_replica_ballot_lb γ (gid rid : u64) (ts : nat) (blt : ballot) : iProp Σ.
    Admitted.

    #[global]
    Instance is_replica_ballot_lb_persistent γ gid rid ts blt :
      Persistent (is_replica_ballot_lb γ gid rid ts blt).
    Admitted.

    Definition is_replica_pdec_at_rank γ (gid rid : u64) (ts rank : nat) (p : bool) : iProp Σ :=
      ∃ blt, is_replica_ballot_lb γ gid rid ts blt ∧ ⌜blt !! rank = Some (Accept p)⌝.

    Lemma replica_ballot_insert {γ gid rid bs} ts l :
      bs !! ts = None ->
      own_replica_ballot_map γ gid rid bs ==∗
      own_replica_ballot_map γ gid rid (<[ts := l]> bs).
    Admitted.

    Lemma replica_ballot_update {γ gid rid bs} ts l l' :
      bs !! ts = Some l ->
      prefix l l' ->
      own_replica_ballot_map γ gid rid bs ==∗
      own_replica_ballot_map γ gid rid (<[ts := l']> bs).
    Admitted.

    Lemma replica_ballot_witness {γ gid rid bs} ts l :
      bs !! ts = Some l ->
      own_replica_ballot_map γ gid rid bs -∗
      is_replica_ballot_lb γ gid rid ts l.
    Admitted.

    Lemma replica_ballot_lookup {γ gid rid bs} ts lb :
      is_replica_ballot_lb γ gid rid ts lb -∗
      own_replica_ballot_map γ gid rid bs -∗
      ⌜∃ l, bs !! ts = Some l ∧ prefix lb l⌝.
    Admitted.

    Lemma replica_ballot_prefix {γ gid rid bs} ts l lb :
      bs !! ts = Some l ->
      is_replica_ballot_lb γ gid rid ts lb -∗
      own_replica_ballot_map γ gid rid bs -∗
      ⌜prefix lb l⌝.
    Admitted.

  End replica_ballot.

  Section replica_backup_vote.

    (** Mappings from transaction IDs and ranks to coordinator IDs to which vote
    of the transaction ID and rank is casted by this replica. This is used to
    ensure no two replicas could serve as the coordinator in the same term. *)

    Definition own_replica_backup_vote_map
      γ (gid rid : u64) (bvm : gmap nat (gmap nat coordid)) : iProp Σ.
    Admitted.

    Definition is_replica_backup_vote
      γ (gid rid : u64) (ts rank : nat) (cid : coordid) : iProp Σ.
    Admitted.

    #[global]
    Instance is_replica_backup_vote_persistent γ gid rid ts rank cid :
      Persistent (is_replica_backup_vote γ gid rid ts rank cid).
    Admitted.

    Lemma replica_backup_vote_init {γ gid rid bvm} ts :
      bvm !! ts = None ->
      own_replica_backup_vote_map γ gid rid bvm ==∗
      own_replica_backup_vote_map γ gid rid (<[ts := ∅]> bvm).
    Admitted.

    Lemma replica_backup_vote_insert {γ gid rid bvm m} ts rank cid :
      bvm !! ts = Some m ->
      m !! rank = None ->
      own_replica_backup_vote_map γ gid rid bvm ==∗
      own_replica_backup_vote_map γ gid rid (<[ts := (<[rank := cid]> m)]> bvm) ∗
      is_replica_backup_vote γ gid rid ts rank cid.
    Admitted.

    Lemma replica_backup_vote_agree γ gid rid ts rank cid1 cid2 :
      is_replica_backup_vote γ gid rid ts rank cid1 -∗
      is_replica_backup_vote γ gid rid ts rank cid2 -∗
      ⌜cid2 = cid1⌝.
    Admitted.

  End replica_backup_vote.

  Section replica_backup_token.

    (** Mappings from transaction IDs and ranks to sets of groups IDs. This is
    used to ensure that the same replica proposes become the coordinator at a
    certain rank for a certain group at most once. *)

    Definition own_replica_backup_tokens_map
      γ (gid rid : u64) (btm : gmap nat (gmap nat (gset u64))) : iProp Σ.
    Admitted.

    Definition own_replica_backup_token
      γ (gid rid : u64) (ts rank : nat) (tgid : u64) : iProp Σ.
    Admitted.

    Lemma replica_backup_token_init {γ gid rid btm} ts :
      btm !! ts = None ->
      own_replica_backup_tokens_map γ gid rid btm ==∗
      own_replica_backup_tokens_map γ gid rid (<[ts := ∅]> btm).
    Admitted.

    Lemma replica_backup_token_insert {γ gid rid btm m} ts rank tgids :
      btm !! ts = Some m ->
      m !! rank = None ->
      own_replica_backup_tokens_map γ gid rid btm ==∗
      own_replica_backup_tokens_map γ gid rid (<[ts := (<[rank := tgids]> m)]> btm) ∗
      ([∗ set] tgid ∈ tgids, own_replica_backup_token γ gid rid ts rank tgid).
    Admitted.

    Lemma replica_backup_token_excl γ gid rid ts rank tgid :
      own_replica_backup_token γ gid rid ts rank tgid -∗
      own_replica_backup_token γ gid rid ts rank tgid -∗
      False.
    Admitted.

  End replica_backup_token.

End res.
