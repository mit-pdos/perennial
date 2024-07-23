From iris.base_logic.lib Require Import ghost_map.
From iris.algebra Require Import gmap_view.
From iris.proofmode Require Import proofmode.

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
    apply to_agree_included_L in Hincl. by rewrite Hincl.
  Qed.

  Lemma ghost_map_auth_pers_agree γ q2 m1 m2 :
    ghost_map_auth_pers γ m1 -∗ ghost_map_auth γ q2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iCombine "H1 H2" gives %[? ?%(inj _)]%gmap_view_auth_dfrac_op_valid.
    iPureIntro. by fold_leibniz.
  Qed.

  Lemma ghost_map_auth_pers_pers_agree γ m1 m2 :
    ghost_map_auth_pers γ m1 -∗ ghost_map_auth_pers γ m2 -∗ ⌜m1 = m2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iCombine "H1 H2" gives %[? ?%(inj _)]%gmap_view_auth_dfrac_op_valid.
    iPureIntro. by fold_leibniz.
  Qed.

End lemmas.
