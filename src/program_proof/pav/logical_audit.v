From Perennial.program_proof.pav Require Import prelude.
From Perennial.program_proof.pav Require Import core serde merkle.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Definition maps_mono (ms : list adtr_map_ty) :=
  ∀ (i j : w64) mi mj,
  ms !! (uint.nat i) = Some mi →
  ms !! (uint.nat j) = Some mj →
  uint.Z i ≤ uint.Z j →
  mi ⊆ mj.

Definition epochs_ok (ms : list adtr_map_ty) :=
  ∀ (ep : w64) m_ep k ep' comm,
  ms !! (uint.nat ep) = Some m_ep →
  m_ep !! k = Some (ep', comm) →
  uint.Z ep' ≤ uint.Z ep.

Definition lower_map (m : adtr_map_ty) : merkle_map_ty :=
  (λ v, MapValPre.encodesF (MapValPre.mk v.1 v.2)) <$> m.

Definition sigpred_gs_inv (gs : list (adtr_map_ty * dig_ty)) : iProp Σ :=
  "#His_digs" ∷ ([∗ list] x ∈ gs, is_merkle_map (lower_map x.1) x.2) ∗
  "%Hmono_maps" ∷ ⌜ maps_mono gs.*1 ⌝ ∗
  "%Hok_epochs" ∷ ⌜ epochs_ok gs.*1 ⌝.

Definition sigpred γ : (list w8 → iProp Σ) :=
  λ preByt,
  (∃ pre gs,
  "%Henc" ∷ ⌜ PreSigDig.encodes preByt pre ⌝ ∗
  "#Hlb" ∷ mono_list_lb_own γ gs ∗
  "%Hlook_dig" ∷ ⌜ gs.*2 !! uint.nat pre.(PreSigDig.Epoch) = Some pre.(PreSigDig.Dig) ⌝ ∗
  "#Hinv_gs" ∷ sigpred_gs_inv gs)%I.

Lemma sigpred_gs_snoc gs upd dig :
  let new_map := (upd ∪ (default ∅ (last gs.*1))) in
  sigpred_gs_inv gs -∗
  is_merkle_map (lower_map new_map) dig -∗
  ⌜ upd ##ₘ (default ∅ (last gs.*1)) ⌝ -∗
  ([∗ map] val ∈ upd, ⌜ val.1 = W64 (length gs) ⌝) -∗
  sigpred_gs_inv (gs ++ [(new_map, dig)]).
Proof.
  iIntros "* #Hold_inv #His_dig %Hdisj %Hok_epoch".
  iNamedSuffix "Hold_inv" "_old".
iSplit; [|iPureIntro; split].
  - iApply big_sepL_snoc. iFrame "#".
  - unfold maps_mono in *. intros * Hlook_gsi Hlook_gsj Heq_ep.
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
  - unfold epochs_ok in *. intros * Hlook_gs Hlook_m.
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

End proof.
