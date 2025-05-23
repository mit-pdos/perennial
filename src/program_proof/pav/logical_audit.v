From Perennial.program_proof.pav Require Import prelude.
From Perennial.program_proof.pav Require Import core serde merkle.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Definition mono_maps (ms : list merkle_map_ty) :=
  ∀ (i j : w64) mi mj,
  ms !! (uint.nat i) = Some mi →
  ms !! (uint.nat j) = Some mj →
  uint.Z i ≤ uint.Z j →
  mi ⊆ mj.

(* our "characterization" of monotonic maps. *)
Lemma mono_char ms :
  mono_maps ms →
  ∀ k,
  (* all flat. *)
  (∀ (ep : w64) m_ep,
    ms !! (uint.nat ep) = Some m_ep →
    m_ep !! k = None)
  ∨
  (∃ (insert_ep : w64) m_insert,
    (* flat. *)
    (∀ (ep : w64),
      uint.Z ep < uint.Z insert_ep →
      ∃ m_ep,
      ms !! (uint.nat ep) = Some m_ep ∧
      m_ep !! k = None) ∧
    (* until a spike. *)
    ms !! (uint.nat insert_ep) = Some m_insert ∧
    is_Some (m_insert !! k)).
Proof. Admitted.

Lemma mono_get_insertion ms (bound_ep : w64) m_bound k :
  mono_maps ms →
  ms !! (uint.nat bound_ep) = Some m_bound →
  is_Some (m_bound !! k) →

  ∃ (insert_ep : w64) m_insert,
  ms !! (uint.nat insert_ep) = Some m_insert ∧
  is_Some (m_insert !! k) ∧
  (
    uint.Z insert_ep = 0
    ∨
    ∀ m_pred,
    ms !! (Z.to_nat (uint.Z insert_ep - 1)) = Some m_pred →
    m_pred !! k = None
  ).
Proof.
  intros Hmono Hlook_end ?.
  opose proof (mono_char _ Hmono k) as [Hmono1 | Hmono1].
  - exfalso. ospecialize (Hmono1 _ _ Hlook_end).
    destruct (m_bound !! k); [done|].
    by eapply is_Some_None.
  - destruct Hmono1 as (insert_ep&?&Hflat&Hlook_insert&?).
    eexists insert_ep, _.
    repeat try split; [done..|].
    destruct (decide (uint.Z insert_ep = 0)); [naive_solver|].
    right. intros ? Hlook_pred0.
    remember (word.sub insert_ep (W64 1)) as i.
    replace (Z.to_nat _) with (uint.nat i) in Hlook_pred0 by word.
    opose proof (Hflat i _) as (?&Hlook_pred1&?); [word|].
    by simplify_eq/=.
Qed.

Definition audit_gs_inv (gs : list (merkle_map_ty * dig_ty)) : iProp Σ :=
  "#His_digs" ∷ ([∗ list] x ∈ gs,
    "#His_map" ∷ is_merkle_map x.1 x.2) ∗
  "%Hmono_maps" ∷ ⌜ mono_maps gs.*1 ⌝.

Definition sigpred γ : (list w8 → iProp Σ) :=
  λ preByt,
  (∃ pre gs m,
  "%Henc" ∷ ⌜ PreSigDig.encodes preByt pre ⌝ ∗
  "#Hlb" ∷ mono_list_lb_own γ gs ∗
  "%Hlook_dig" ∷ ⌜ gs !! uint.nat pre.(PreSigDig.Epoch) = Some (m, pre.(PreSigDig.Dig)) ⌝ ∗
  "#Hinv_gs" ∷ audit_gs_inv gs)%I.

Lemma audit_gs_snoc gs upd dig :
  let new_map := (upd ∪ (default ∅ (last gs.*1))) in
  upd ##ₘ (default ∅ (last gs.*1)) →
  audit_gs_inv gs -∗
  is_merkle_map new_map dig -∗
  audit_gs_inv (gs ++ [(new_map, dig)]).
Proof.
  simpl. iIntros (Hdisj) "#Hold_inv #His_dig".
  iNamedSuffix "Hold_inv" "_old".
  iSplit.
  - iApply big_sepL_snoc. iFrame "#%".
  - iPureIntro. unfold mono_maps in *. intros * Hlook_gsi Hlook_gsj Heq_ep.
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
Qed.

Lemma audit_gs_prefix l l' :
  l' `prefix_of` l →
  audit_gs_inv l -∗
  audit_gs_inv l'.
Proof.
  iIntros (Hpref). iNamed 1. iSplit.
  - opose proof (prefix_to_take _ _ Hpref) as ->.
    by iApply big_sepL_take.
  - iPureIntro. intros ???? Hlook0 Hlook1 ?.
    apply (prefix_fmap fst) in Hpref.
    opose proof (prefix_lookup_Some _ _ _ _ Hlook0 Hpref) as Hlook0'.
    opose proof (prefix_lookup_Some _ _ _ _ Hlook1 Hpref) as Hlook1'.
    by apply (Hmono_maps _ _ _ _ Hlook0' Hlook1').
Qed.

End proof.
