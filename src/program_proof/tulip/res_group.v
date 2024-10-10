(** Global resources. *)
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip Require Import base.

Section res.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  Section group_prep.

    (** Mapping from transaction IDs to preparedness of transactions on a group. *)

    Definition own_group_prepm γ (gid : groupid) (pm : gmap nat bool) : iProp Σ.
    Admitted.

    Definition is_group_prep γ (gid : groupid) (ts : nat) (p : bool) : iProp Σ.
    Admitted.

    #[global]
    Instance is_group_prep_persistent γ gid ts p :
      Persistent (is_group_prep γ gid ts p).
    Admitted.

    Definition is_group_preped γ gid ts :=
      is_group_prep γ gid ts true.

    Definition is_group_unpreped γ gid ts :=
      is_group_prep γ gid ts false.

    Lemma group_prep_agree γ gid ts p1 p2 :
      is_group_prep γ gid ts p1 -∗
      is_group_prep γ gid ts p2 -∗
      ⌜p2 = p1⌝.
    Admitted.

    Lemma group_prep_insert {γ gid pm} ts p :
      pm !! ts = None ->
      own_group_prepm γ gid pm ==∗
      own_group_prepm γ gid (<[ts := p]> pm).
    Admitted.

    Lemma group_prep_witness γ gid pm ts p :
      pm !! ts = Some p ->
      own_group_prepm γ gid pm -∗
      is_group_prep γ gid ts p.
    Admitted.

    Lemma group_prep_lookup γ gid pm ts p :
      own_group_prepm γ gid pm -∗
      is_group_prep γ gid ts p -∗
      ⌜pm !! ts = Some p⌝.
    Admitted.

  End group_prep.

End res.
