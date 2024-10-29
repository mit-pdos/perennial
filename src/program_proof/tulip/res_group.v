(** Global resources. *)
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip Require Import base.

Section res.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  (* TODO: rename this to [group_prepare]. *)
  Section group_prep.

    (** Mapping from transaction IDs to preparedness of transactions on a group. *)

    Definition own_group_prepm γ (gid : u64) (pm : gmap nat bool) : iProp Σ.
    Admitted.

    Definition is_group_prep γ (gid : u64) (ts : nat) (p : bool) : iProp Σ.
    Admitted.

    #[global]
    Instance is_group_prep_persistent γ gid ts p :
      Persistent (is_group_prep γ gid ts p).
    Admitted.

    Definition is_group_prepared γ gid ts :=
      is_group_prep γ gid ts true.

    Definition is_group_unprepared γ gid ts :=
      is_group_prep γ gid ts false.

    Lemma group_prep_agree γ gid ts p1 p2 :
      is_group_prep γ gid ts p1 -∗
      is_group_prep γ gid ts p2 -∗
      ⌜p2 = p1⌝.
    Admitted.

    Lemma group_prep_insert {γ gid pm} ts p :
      pm !! ts = None ->
      own_group_prepm γ gid pm ==∗
      own_group_prepm γ gid (<[ts := p]> pm) ∗ is_group_prep γ gid ts p.
    Admitted.

    Lemma group_prep_lookup γ gid pm ts p :
      own_group_prepm γ gid pm -∗
      is_group_prep γ gid ts p -∗
      ⌜pm !! ts = Some p⌝.
    Admitted.

  End group_prep.

  Section group_commit.

    (** Mapping from transaction IDs to committedness of transactions on a group. *)

    Definition own_group_commit_map γ (gid : u64) (pm : gmap nat bool) : iProp Σ.
    Admitted.

    Definition is_group_commit γ (gid : u64) (ts : nat) (c : bool) : iProp Σ.
    Admitted.

    #[global]
    Instance is_group_commit_persistent γ gid ts c :
      Persistent (is_group_commit γ gid ts c).
    Admitted.

    Definition is_group_committed γ gid ts :=
      is_group_commit γ gid ts true.

    Definition is_group_aborted γ gid ts :=
      is_group_commit γ gid ts false.

    Lemma group_commit_agree γ gid ts c1 c2 :
      is_group_commit γ gid ts c1 -∗
      is_group_commit γ gid ts c2 -∗
      ⌜c2 = c1⌝.
    Admitted.

    Lemma group_commit_insert {γ gid pm} ts c :
      pm !! ts = None ->
      own_group_commit_map γ gid pm ==∗
      own_group_commit_map γ gid (<[ts := c]> pm) ∗ is_group_commit γ gid ts c.
    Admitted.

    Lemma group_commit_witness γ gid pm ts c :
      pm !! ts = Some c ->
      own_group_commit_map γ gid pm -∗
      is_group_commit γ gid ts c.
    Admitted.

    Lemma group_commit_lookup γ gid pm ts c :
      own_group_commit_map γ gid pm -∗
      is_group_commit γ gid ts c -∗
      ⌜pm !! ts = Some c⌝.
    Admitted.

  End group_commit.

End res.
