From Perennial.program_proof.pav Require Import prelude.
From Perennial.program_proof.pav Require Import core serde merkle.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Definition mono_maps (ms : list adtr_map_ty) :=
  ∀ (i j : w64) mi mj,
  ms !! (uint.nat i) = Some mi →
  ms !! (uint.nat j) = Some mj →
  uint.Z i ≤ uint.Z j →
  mi ⊆ mj.

Definition ok_epochs (ms : list adtr_map_ty) :=
  ∀ (ep : w64) m_ep k ep' comm,
  ms !! (uint.nat ep) = Some m_ep →
  m_ep !! k = Some (ep', comm) →
  uint.Z ep' ≤ uint.Z ep.

Definition map_lower (higher : adtr_map_ty) (lower : merkle_map_ty) :=
  map_Forall2 (λ _ x y, MapValPre.encodes x y) lower
    ((λ x, MapValPre.mk x.1 x.2) <$> higher).

Definition audit_gs_inv (gs : list (adtr_map_ty * dig_ty)) : iProp Σ :=
  "#His_digs" ∷ ([∗ list] x ∈ gs,
    ∃ lower,
    "%Hlower" ∷ ⌜ map_lower x.1 lower ⌝ ∗
    "#His_map" ∷ is_merkle_map lower x.2) ∗
  "%Hmono_maps" ∷ ⌜ mono_maps gs.*1 ⌝ ∗
  "%Hok_epochs" ∷ ⌜ ok_epochs gs.*1 ⌝.

Definition sigpred γ : (list w8 → iProp Σ) :=
  λ preByt,
  (∃ pre gs m,
  "%Henc" ∷ ⌜ PreSigDig.encodes preByt pre ⌝ ∗
  "#Hlb" ∷ mono_list_lb_own γ gs ∗
  "%Hlook_dig" ∷ ⌜ gs !! uint.nat pre.(PreSigDig.Epoch) = Some (m, pre.(PreSigDig.Dig)) ⌝ ∗
  "#Hinv_gs" ∷ audit_gs_inv gs)%I.

Lemma audit_gs_snoc gs upd lowered_new_map dig :
  let new_map := (upd ∪ (default ∅ (last gs.*1))) in
  upd ##ₘ (default ∅ (last gs.*1)) →
  map_lower new_map lowered_new_map →
  map_Forall (λ _ v, v.1 = W64 (length gs)) upd →
  audit_gs_inv gs -∗
  is_merkle_map lowered_new_map dig -∗
  audit_gs_inv (gs ++ [(new_map, dig)]).
Proof.
  simpl. iIntros (Hdisj Hlower Hok_epoch) "#Hold_inv #His_dig".
  iNamedSuffix "Hold_inv" "_old".
  iSplit; [|iPureIntro; split].
  - iApply big_sepL_snoc. iFrame "#%".
  - unfold mono_maps in *. intros * Hlook_gsi Hlook_gsj Heq_ep.
    rewrite fmap_app in Hlook_gsi Hlook_gsj.
    destruct (decide (uint.Z i = uint.Z j)).
    { by simplify_eq/=. }
    destruct (decide (uint.Z j < length gs)).
    { eapply Hmono_maps_old.
      { rewrite lookup_app_l in Hlook_gsi; [done|].
        rewrite length_fmap. word. }
      { rewrite lookup_app_l in Hlook_gsj; [done|].
        rewrite length_fmap. word. }
      done. }
    rewrite lookup_app_r in Hlook_gsj.
    2: { rewrite length_fmap. word. }
    simpl in *. eapply list_lookup_singleton_Some in Hlook_gsj as [Heq_ep1 <-].
    rewrite length_fmap in Heq_ep1.
    rewrite lookup_app_l in Hlook_gsi.
    2: { rewrite length_fmap. word. }
    destruct (last gs.*1) as [m_last|] eqn:Hlast.
    2: { apply last_None in Hlast. by rewrite Hlast in Hlook_gsi. }
    simpl in *. trans m_last.
    2: { by apply map_union_subseteq_r. }
    rewrite last_lookup in Hlast.
    refine (Hmono_maps_old _
      (W64 (pred $ length gs)) _ _ Hlook_gsi _ _); [|word].
    replace (uint.nat (W64 _)) with (pred $ length gs); [|word].
    by rewrite length_fmap in Hlast.
  - unfold ok_epochs in *. intros * Hlook_gs Hlook_m.
    rewrite fmap_app in Hlook_gs.
    destruct (decide (uint.Z ep < length gs)).
    { eapply Hok_epochs_old; [|done].
      rewrite lookup_app_l in Hlook_gs; [done|].
      rewrite length_fmap. word. }
    rewrite lookup_app_r in Hlook_gs.
    2: { rewrite length_fmap. word. }
    simpl in *. apply list_lookup_singleton_Some in Hlook_gs as [Heq_ep <-].
    apply lookup_union_Some_raw in Hlook_m as [Hlook_upd | [_ Hlook_last]].
    { pose proof (map_Forall_lookup_1 _ _ _ _ Hok_epoch Hlook_upd) as ?.
      simpl in *. subst. word. }
    destruct (last gs.*1) as [m_last|] eqn:Hlast; [|set_solver]. simpl in *.
    opose proof (Hok_epochs_old
      (W64 (pred $ length gs)) _ _ _ _ _ Hlook_last) as ?; [|word].
    replace (uint.nat (W64 _)) with (pred $ length gs); [|word].
    by rewrite last_lookup length_fmap in Hlast.
Qed.

Lemma audit_gs_prefix l l' :
  l' `prefix_of` l →
  audit_gs_inv l -∗
  audit_gs_inv l'.
Proof.
  iIntros (Hpref). iNamed 1. iSplit; [|iPureIntro; split].
  - opose proof (prefix_to_take _ _ Hpref) as ->.
    by iApply big_sepL_take.
  - intros ???? Hlook0 Hlook1 ?.
    apply (prefix_fmap fst) in Hpref.
    opose proof (prefix_lookup_Some _ _ _ _ Hlook0 Hpref) as Hlook0'.
    opose proof (prefix_lookup_Some _ _ _ _ Hlook1 Hpref) as Hlook1'.
    by apply (Hmono_maps _ _ _ _ Hlook0' Hlook1').
  - intros ????? Hlook0 Hlook1.
    apply (prefix_fmap fst) in Hpref.
    opose proof (prefix_lookup_Some _ _ _ _ Hlook0 Hpref) as Hlook0'.
    by apply (Hok_epochs _ _ _ _ _ Hlook0' Hlook1).
Qed.

End proof.
