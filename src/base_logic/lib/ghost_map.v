(* Just reexport Iris mdoule *)
From iris.base_logic.lib Require Export ghost_map.
From iris.algebra Require Import gmap_view.
From iris.proofmode Require Import proofmode.

(* Add some Perennial-specific stuff *)
From Perennial.algebra Require Import own_discrete atleast.
From Perennial.Helpers Require Import Map.

Set Default Proof Using "Type".

Local Existing Instance ghost_map_inG.

Section definitions.
  Context `{ghost_mapG Σ K V}.

  Local Definition ghost_map_auth_pers_def
      (γ : gname) (m : gmap K V) : iProp Σ :=
    own γ (gmap_view_auth (V:=agreeR $ leibnizO V) DfracDiscarded (to_agree <$> m)).
  Local Definition ghost_map_auth_pers_aux : seal (@ghost_map_auth_pers_def).
  Proof. by eexists. Qed.
  Definition ghost_map_auth_pers := ghost_map_auth_pers_aux.(unseal).
  Local Definition ghost_map_auth_pers_unseal :
    @ghost_map_auth_pers = @ghost_map_auth_pers_def := ghost_map_auth_pers_aux.(seal_eq).
End definitions.

Local Ltac unseal := rewrite
  ?ghost_map.ghost_map_auth_unseal /ghost_map.ghost_map_auth_def
  ?ghost_map.ghost_map_elem_unseal /ghost_map.ghost_map_elem_def
  ?ghost_map_auth_pers_unseal /ghost_map_auth_pers_def.

Section lemmas.
  Context `{ghost_mapG Σ K V}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V).

  Global Instance ghost_map_auth_pers_timeless γ m : Timeless (ghost_map_auth_pers γ m).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_map_auth_pers_persistent γ m : Persistent (ghost_map_auth_pers γ m).
  Proof. unseal. apply own_core_persistent. unfold CoreId. done. Qed.

  Lemma ghost_map_auth_persist γ q m :
    ghost_map_auth γ q m ⊢ |==> ghost_map_auth_pers γ m.
  Proof.
    unseal. apply own_update, gmap_view_auth_persist.
  Qed.

  Lemma ghost_map_pers_lookup {γ m k dq v} :
    ghost_map_auth_pers γ m -∗ k ↪[γ]{dq} v -∗ ⌜m !! k = Some v⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    iCombine "Hauth Hel" gives
      %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
    iPureIntro.
    apply lookup_fmap_Some in Hav' as [v' [<- Hv']].
    apply (@to_agree_included_L _) in Hincl.
    { by rewrite Hincl. }
    apply _.
  Qed.

  Lemma ghost_map_auth_pers_agree γ q1 m1 m2 :
    ghost_map_auth_pers γ m1 -∗ ghost_map_auth γ q1 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iCombine "H1 H2" gives %[? Heq]%gmap_view_auth_dfrac_op_valid.
    (* TODO: inj no longer works? *)
    (*
    apply (inj _) in Heq.
    iPureIntro. by fold_leibniz.
  Qed.
*)
  Admitted.

  Lemma ghost_map_auth_pers_pers_agree γ m1 m2 :
    ghost_map_auth_pers γ m1 -∗ ghost_map_auth_pers γ m2 -∗ ⌜m1 = m2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    (* TODO: inj no longer works? *)
    (*
    iCombine "H1 H2" gives %[? ?%(inj _)]%gmap_view_auth_dfrac_op_valid.
    iPureIntro. by fold_leibniz.
  Qed.
  *)
  Admitted.

  Lemma ghost_map_elem_big_exist γ m :
    ([∗ map] l↦_ ∈ m, ∃ v', l ↪[γ] v') -∗
    ∃ m', ⌜dom m' = dom m⌝ ∗
          [∗ map] l↦v ∈ m', l ↪[γ] v.
  Proof.
    induction m as [|l v m] using map_ind.
    - rewrite big_sepM_empty.
      iIntros "_". iExists ∅.
      iSplit; first done.
      rewrite big_sepM_empty; done.
    - rewrite big_sepM_insert //.
      iIntros "[Hl Hm]".
      iDestruct "Hl" as (v') "Hl".
      iDestruct (IHm with "Hm") as (m0 Hdom) "Hm".
      iExists (<[l:=v']> m0).
      iSplit.
      + iPureIntro.
        rewrite !dom_insert_L. congruence.
      + rewrite big_sepM_insert; [ by iFrame | ].
        apply not_elem_of_dom.
        match goal with | H: _ = None |- _ => apply not_elem_of_dom in H end.
        congruence.
  Qed.

  Lemma ghost_map_update_big_exist {γ m} m1 :
    ghost_map_auth γ 1 m -∗
    ( [∗ map] l↦v ∈ m1, ∃ v', l ↪[γ] v' ) ==∗
      ghost_map_auth γ 1 (m1 ∪ m) ∗
      ( [∗ map] l↦v ∈ m1, l ↪[γ] v ).
  Proof.
    iIntros "Hauth Hm0".
    iDestruct (ghost_map_elem_big_exist with "Hm0") as (m0 Hdom) "Hm0".
    iMod (ghost_map_update_big with "Hauth Hm0") as "[$ Hm]"; auto.
  Qed.

  Lemma ghost_map_apply_on {γ updates} base :
    ghost_map_auth γ 1 updates ==∗
    ghost_map_auth γ 1 (updates ∪ base) ∗
    [∗ map] k↦v ∈ base ∖ updates, k ↪[γ] v.
  Proof.
    iIntros "Hauth".
    iMod (ghost_map_insert_big (base ∖ updates) with "Hauth") as "[Hauth Hfrag]".
    { by apply map_disjoint_difference_l. }
    iEval (rewrite map_difference_union') in "Hauth".
    by iFrame.
  Qed.

  Global Instance ghost_map_auth_discrete γ q m : Discretizable (ghost_map_auth γ q m).
  Proof. rewrite ghost_map.ghost_map_auth_unseal. apply _. Qed.

  Global Instance ghost_map_auth_abs_timeless γ q m : AbsolutelyTimeless (ghost_map_auth γ q m).
  Proof. rewrite ghost_map.ghost_map_auth_unseal. apply _. Qed.

  Global Instance ghost_map_elem_discrete γ dq k v : Discretizable (k ↪[γ]{dq} v).
  Proof. rewrite ghost_map.ghost_map_elem_unseal. apply _. Qed.

  Global Instance ghost_map_elem_abs_timeless γ dq k v : AbsolutelyTimeless (k ↪[γ]{dq} v).
  Proof. rewrite ghost_map.ghost_map_elem_unseal. apply _. Qed.

End lemmas.
