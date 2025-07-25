From iris.algebra Require Import mono_nat mono_list gmap_view gset.
From iris.algebra.lib Require Import dfrac_agree.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip Require Import base.

Section res.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  (* TODO: rename this to [group_prepare]. *)
  Section group_prep.

    (** Mapping from transaction IDs to preparedness of transactions on a group. *)

    Definition is_group_prep γ (gid : u64) (ts : nat) (p : bool) : iProp Σ :=
      own γ.(group_prep) {[ gid := gmap_view_frag ts DfracDiscarded (to_agree p) ]}.

    Definition own_group_prepm_auth γ (gid : u64) (pm : gmap nat bool) : iProp Σ :=
      own γ.(group_prep) {[ gid := gmap_view_auth (DfracOwn 1) (to_agree <$> pm) ]}.

    Definition own_group_prepm γ (gid : u64) (pm : gmap nat bool) : iProp Σ :=
      own_group_prepm_auth γ gid pm ∗
      ([∗ map] ts ↦ p ∈ pm, is_group_prep γ gid ts p).

    #[global]
    Instance is_group_prep_persistent γ gid ts p :
      Persistent (is_group_prep γ gid ts p).
    Proof. apply _. Defined.

    Definition is_group_prepared γ gid ts :=
      is_group_prep γ gid ts true.

    Definition is_group_unprepared γ gid ts :=
      is_group_prep γ gid ts false.

    Lemma group_prep_agree γ gid ts p1 p2 :
      is_group_prep γ gid ts p1 -∗
      is_group_prep γ gid ts p2 -∗
      ⌜p2 = p1⌝.
    Proof.
      iIntros "Hfrag1 Hfrag2".
      iDestruct (own_valid_2 with "Hfrag1 Hfrag2") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      apply gmap_view_frag_op_valid in Hvalid as [_ Hvalid].
      by apply to_agree_op_inv_L in Hvalid.
    Qed.

    Lemma group_prep_insert {γ gid pm} ts p :
      pm !! ts = None ->
      own_group_prepm γ gid pm ==∗
      own_group_prepm γ gid (<[ts := p]> pm) ∗ is_group_prep γ gid ts p.
    Proof.
      iIntros (Hnotin) "[Hauth #Hfrags]".
      iAssert (own_group_prepm_auth γ gid (<[ts := p]> pm) ∗ is_group_prep γ gid ts p)%I
        with "[> Hauth]" as "[Hauth #Hfrag]".
      { iRevert "Hauth".
        rewrite -own_op.
        iApply own_update.
        rewrite singleton_op.
        apply singleton_update.
        rewrite fmap_insert. apply: gmap_view_alloc; [|done..].
        by rewrite lookup_fmap Hnotin.
      }
      iFrame "∗ #".
      by iApply big_sepM_insert_2.
    Qed.

    Lemma group_prep_lookup γ gid pm ts p :
      own_group_prepm γ gid pm -∗
      is_group_prep γ gid ts p -∗
      ⌜pm !! ts = Some p⌝.
    Proof.
      iIntros "[Hauth _] Hfrag".
      iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      apply gmap_view_both_dfrac_valid_discrete_total in Hvalid.
      destruct Hvalid as (v' & _ & _ & Hlookup & _ & Hincl).
      apply lookup_fmap_Some in Hlookup as (b & <- & Hb).
      apply to_agree_included_L in Hincl.
      by subst b.
    Qed.

    Lemma group_prep_witness γ gid pm ts p :
      pm !! ts = Some p ->
      own_group_prepm γ gid pm -∗
      is_group_prep γ gid ts p.
    Proof.
      iIntros (Hp) "[_ Hfrags]".
      by iApply (big_sepM_lookup with "Hfrags").
    Qed.

  End group_prep.

  Section group_prepare_proposal.

    (** Mapping from transaction IDs to proposals (i.e., pairs of rank and bool). *)

    Definition is_group_prepare_proposal γ (gid : u64) (ts : nat) (rk : nat) (p : bool) : iProp Σ :=
      own γ.(group_prepare_proposal)
              {[ gid := (gmap_view_frag (ts, rk) DfracDiscarded (to_agree p)) ]}.

    Definition own_group_ppsl_auth γ (gid : u64) (psm : gmap (nat * nat) bool) : iProp Σ :=
      own γ.(group_prepare_proposal) {[ gid := (gmap_view_auth (DfracOwn 1) (to_agree <$> psm)) ]}.

    Definition own_group_prepare_proposals_map
      γ (gid : u64) (psm : gmap nat (gmap nat bool)) : iProp Σ :=
      ∃ m : gmap (nat * nat) bool,
        own_group_ppsl_auth γ gid m ∗
        ([∗ map] tr ↦ p ∈ m, is_group_prepare_proposal γ gid tr.1 tr.2 p) ∗
        (⌜∀ t r p, m !! (t, r) = Some p ↔ ∃ im, psm !! t = Some im ∧ im !! r = Some p⌝).

    #[global]
    Instance is_group_prepare_proposal_persistent γ gid ts rk p :
      Persistent (is_group_prepare_proposal γ gid ts rk p).
    Proof. apply _. Defined.

    (* TODO: this doesn't need an update modality *)
    Lemma group_prepare_proposal_init {γ gid psm} ts :
      psm !! ts = None ->
      own_group_prepare_proposals_map γ gid psm ==∗
      own_group_prepare_proposals_map γ gid (<[ts := ∅]> psm).
    Proof.
      iIntros (Hnotin) "Hauth".
      iDestruct "Hauth" as (m) "(Hauth & Hppsl & %Heq)".
      iExists m.
      iFrame.
      iPureIntro.
      intros t r p.
      split.
      { intros Hp.
        specialize (Heq t r p).
        destruct Heq as [Hincl _].
        specialize (Hincl Hp).
        destruct Hincl as (im & Him & Himr).
        destruct (decide (t = ts)) as [-> | Hne]; first congruence.
        exists im.
        by rewrite lookup_insert_ne.
      }
      { intros (im & Him & Hp).
        specialize (Heq t r p).
        destruct Heq as [_ Hincl].
        apply Hincl.
        destruct (decide (ts = t)) as [-> | Hne].
        { rewrite lookup_insert_eq in Him. inv Him. }
        { rewrite lookup_insert_ne in Him; last done.
          by eauto.
        }
      }
    Qed.

    Lemma group_prepare_proposal_insert {γ gid psm} ts ps rk p :
      let ps' := <[rk := p]> ps in
      psm !! ts = Some ps ->
      ps !! rk = None ->
      own_group_prepare_proposals_map γ gid psm ==∗
      own_group_prepare_proposals_map γ gid (<[ts := ps']> psm).
    Proof.
      iIntros (ps' Hps Hnotin) "Hauth".
      iDestruct "Hauth" as (m) "(Hauth & Hppsl & %Heq)".
      iAssert (own_group_ppsl_auth γ gid (<[(ts, rk) := p]> m) ∗
               is_group_prepare_proposal γ gid ts rk p)%I
        with "[> Hauth]" as "[Hauth #Hfrag]".
      { iRevert "Hauth".
        rewrite -own_op.
        iApply own_update.
        rewrite singleton_op.
        apply singleton_update.
        rewrite fmap_insert. apply: gmap_view_alloc; [|done..].
        rewrite lookup_fmap.
        destruct (m !! (ts, rk)) as [p' |] eqn:Hin; last done.
        specialize (Heq ts rk p').
        destruct Heq as [Hincl _].
        specialize (Hincl Hin).
        destruct Hincl as (im & Him & Hp').
        rewrite Hps in Him. inv Him.
      }
      iExists (<[(ts, rk) := p]> m).
      iFrame.
      iModIntro.
      iSplit.
      { by iApply big_sepM_insert_2. }
      iPureIntro.
      intros t r p'.
      split.
      { intros Hp'.
        destruct (decide (t = ts)) as [-> | Hne].
        { rewrite lookup_insert_eq.
          exists ps'.
          split; first done.
          subst ps'.
          destruct (decide (r = rk)) as [-> | Hner].
          { rewrite lookup_insert_eq.
            by rewrite lookup_insert_eq in Hp'.
          }
          { rewrite lookup_insert_ne; last done.
            rewrite lookup_insert_ne in Hp'; last first.
            { intros Hcontra. inv Hcontra. }
            specialize (Heq ts r p').
            destruct Heq as [Hincl _].
            specialize (Hincl Hp').
            destruct Hincl as (im & Him & Himr).
            rewrite Hps in Him. by inv Him.
          }
        }
        { rewrite lookup_insert_ne; last done.
          rewrite lookup_insert_ne in Hp'; last first.
          { intros Hcontra. inv Hcontra. }
          by apply Heq.
        }
      }
      { intros Him.
        destruct Him as (im & Him & Hp').
        destruct (decide (t = ts)) as [-> | Hne].
        { rewrite lookup_insert_eq in Him. inv Him.
          destruct (decide (r = rk)) as [-> | Hner].
          { rewrite lookup_insert_eq.
            rewrite lookup_insert_eq in Hp'. by inv Hp'.
          }
          { rewrite lookup_insert_ne; last first.
            { intros Hcontra. inv Hcontra. }
            rewrite lookup_insert_ne in Hp'; last done.
            apply Heq.
            by eauto.
          }
        }
        { rewrite lookup_insert_ne; last first.
          { intros Hcontra. inv Hcontra. }
          rewrite lookup_insert_ne in Him; last done.
          apply Heq.
          by eauto.
        }
      }
    Qed.

    Lemma group_prepare_proposal_witness {γ gid psm} ts ps rk p :
      psm !! ts = Some ps ->
      ps !! rk = Some p ->
      own_group_prepare_proposals_map γ gid psm -∗
      is_group_prepare_proposal γ gid ts rk p.
    Proof.
      iIntros (Hps Hp) "Hauth".
      iDestruct "Hauth" as (im) "(_ & Hfrags & %Heq)".
      iApply (big_sepM_lookup _ _ (ts, rk) with "Hfrags").
      apply Heq.
      by eauto.
    Qed.

    Lemma group_prepare_proposal_lookup γ gid psm ts rk p :
      is_group_prepare_proposal γ gid ts rk p -∗
      own_group_prepare_proposals_map γ gid psm -∗
      ∃ ps, ⌜psm !! ts = Some ps ∧ ps !! rk = Some p⌝.
    Proof.
      iIntros "Hfrag Hauth".
      iDestruct "Hauth" as (im) "(Hauth & _ & %Heq)".
      iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      apply gmap_view_both_dfrac_valid_discrete_total in Hvalid.
      destruct Hvalid as (v' & _ & _ & Hlookup & _ & Hincl).
      apply lookup_fmap_Some in Hlookup as (b & <- & Hb).
      apply to_agree_included_L in Hincl.
      subst b.
      iPureIntro.
      by apply Heq.
    Qed.

  End group_prepare_proposal.

  Section group_commit.

    (** Mapping from transaction IDs to committedness of transactions on a group. *)

    Definition is_group_commit γ (gid : u64) (ts : nat) (c : bool) : iProp Σ :=
      own γ.(group_commit) {[ gid := (gmap_view_frag ts DfracDiscarded (to_agree c)) ]}.

    Definition own_group_commit_map_auth γ (gid : u64) (cm : gmap nat bool) : iProp Σ :=
      own γ.(group_commit) {[ gid := (gmap_view_auth (DfracOwn 1) (to_agree <$> cm)) ]}.

    Definition own_group_commit_map γ (gid : u64) (cm : gmap nat bool) : iProp Σ :=
      own_group_commit_map_auth γ gid cm ∗
      ([∗ map] ts ↦ c ∈ cm, is_group_commit γ gid ts c).

    #[global]
    Instance is_group_commit_persistent γ gid ts c :
      Persistent (is_group_commit γ gid ts c).
    Proof. apply _. Defined.

    Definition is_group_committed γ gid ts :=
      is_group_commit γ gid ts true.

    Definition is_group_aborted γ gid ts :=
      is_group_commit γ gid ts false.

    Lemma group_commit_agree γ gid ts c1 c2 :
      is_group_commit γ gid ts c1 -∗
      is_group_commit γ gid ts c2 -∗
      ⌜c2 = c1⌝.
    Proof.
      iIntros "Hfrag1 Hfrag2".
      iDestruct (own_valid_2 with "Hfrag1 Hfrag2") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      apply gmap_view_frag_op_valid in Hvalid as [_ Hvalid].
      by apply to_agree_op_inv_L in Hvalid.
    Qed.

    Lemma group_commit_insert {γ gid pm} ts c :
      pm !! ts = None ->
      own_group_commit_map γ gid pm ==∗
      own_group_commit_map γ gid (<[ts := c]> pm) ∗ is_group_commit γ gid ts c.
    Proof.
      iIntros (Hnotin) "[Hauth #Hfrags]".
      iAssert (own_group_commit_map_auth γ gid (<[ts := c]> pm) ∗ is_group_commit γ gid ts c)%I
        with "[> Hauth]" as "[Hauth #Hfrag]".
      { iRevert "Hauth".
        rewrite -own_op.
        iApply own_update.
        rewrite singleton_op.
        apply singleton_update.
        rewrite fmap_insert. apply: gmap_view_alloc; [|done..].
        by rewrite lookup_fmap Hnotin.
      }
      iFrame "∗ #".
      by iApply big_sepM_insert_2.
    Qed.

    Lemma group_commit_witness γ gid pm ts c :
      pm !! ts = Some c ->
      own_group_commit_map γ gid pm -∗
      is_group_commit γ gid ts c.
    Proof.
      iIntros (Hp) "[_ Hfrags]".
      by iApply (big_sepM_lookup with "Hfrags").
    Qed.

    Lemma group_commit_lookup γ gid pm ts c :
      own_group_commit_map γ gid pm -∗
      is_group_commit γ gid ts c -∗
      ⌜pm !! ts = Some c⌝.
    Proof.
      iIntros "[Hauth _] Hfrag".
      iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
      rewrite singleton_op singleton_valid in Hvalid.
      apply gmap_view_both_dfrac_valid_discrete_total in Hvalid.
      destruct Hvalid as (v' & _ & _ & Hlookup & _ & Hincl).
      apply lookup_fmap_Some in Hlookup as (b & <- & Hb).
      apply to_agree_included_L in Hincl.
      by subst b.
    Qed.

  End group_commit.

End res.
