From iris.proofmode Require Import proofmode.
From iris.algebra Require Import big_op.

Section bi.
  Context {PROP : bi}.

  Lemma big_sepM_impl_dom_eq_res `{Countable K} {A B}
    (Φ : K → A → PROP) (Ψ : K → B → PROP) (R : PROP)
    (m1 : gmap K A) (m2 : gmap K B) :
    dom m2 = dom m1 →
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    R -∗
    □ (∀ (k : K) (x : A) (y : B),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ →
         Φ k x -∗ R -∗ Ψ k y ∗ R) -∗
    ([∗ map] k↦y ∈ m2, Ψ k y) ∗ R.
  Proof.
    iInduction m2 as [| k x m2 Hm2k] "IH" using map_ind forall (m1).
    { iIntros (Hdom) "Hm HR #Himpl".
      iFrame.
      iApply big_sepM_empty.
      rewrite dom_empty_L in Hdom. symmetry in Hdom.
      apply dom_empty_inv_L in Hdom.
      by rewrite Hdom big_sepM_empty.
    }
    iIntros (Hdom) "Hm1 HR #Himpl".
    rewrite dom_insert_L in Hdom.
    assert (Hm1k : k ∈ dom m1) by set_solver.
    rewrite elem_of_dom in Hm1k. destruct Hm1k as [y Hy].
    apply insert_delete_id in Hy. rewrite -Hy.
    set m0 := delete _ _.
    iDestruct (big_sepM_insert with "Hm1") as "[HΦ Hm1]".
    { by rewrite lookup_delete_eq. }
    rewrite big_sepM_insert; last done.
    iDestruct ("Himpl" with "[] [] HΦ HR") as "[HΨ HR]".
    { by rewrite lookup_insert_eq. }
    { by rewrite lookup_insert_eq. }
    iDestruct ("IH" with "[] Hm1 HR []") as "[Hm2 HR]"; last by iFrame.
    { iPureIntro. subst m0. apply not_elem_of_dom_2 in Hm2k. set_solver. }
    iIntros "!>" (i p q Hp Hq) "HΦ HR".
    iDestruct ("Himpl" with "[] [] HΦ HR") as "HH".
    { rewrite lookup_insert_ne; [done | set_solver]. }
    { rewrite lookup_insert_ne; [done | set_solver]. }
    iFrame.
  Qed.

  Lemma big_sepM_impl_dom_eq `{Countable K} {A B}
    (Φ : K → A → PROP) (Ψ : K → B → PROP) (m1 : gmap K A) (m2 : gmap K B) :
    dom m2 = dom m1 →
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    □ (∀ (k : K) (x : A) (y : B),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ →
         Φ k x -∗ Ψ k y) -∗
    ([∗ map] k↦y ∈ m2, Ψ k y).
  Proof.
    iIntros (Hdom) "Hm1 #Himpl".
    iDestruct (big_sepM_impl_dom_eq_res _ Ψ emp _ m2 with "Hm1 [] []")
      as "[Hm2 _ ]"; [done | done | | iFrame].
    iIntros "!>" (k x y Hx Hy) "HΦ".
    iDestruct ("Himpl" with "[] [] HΦ") as "HΨ"; [done | done | by auto].
  Qed.

  Lemma big_sepM_sepM2_impl_res `{Countable K} {A B}
    (Φ : K → A → PROP) (Ψ : K → A -> B → PROP) (R : PROP)
    (m1 : gmap K A) (m2 : gmap K B) :
    dom m2 = dom m1 →
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    R -∗
    □ (∀ (k : K) (x : A) (y : B),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ →
         Φ k x -∗ R -∗ Ψ k x y ∗ R) -∗
    ([∗ map] k↦x;y ∈ m1;m2, Ψ k x y) ∗ R.
  Proof.
    iIntros (Hdom) "Hm1 HR #Himpl".
    rewrite big_sepM2_alt.
    iDestruct (big_sepM_impl_dom_eq_res _ (λ k xy, Ψ k xy.1 xy.2) R _ (map_zip m1 m2)
                with "Hm1 HR []") as "[HΨ Hm2]"; last by iFrame.
    { rewrite dom_map_zip_with_L. set_solver. }
    iIntros "!>" (k x p Hm1 Hm1m2) "HΦ HR".
    rewrite map_lookup_zip_Some in Hm1m2.
    destruct Hm1m2 as [Hm1' Hm2].
    rewrite Hm1' in Hm1. inversion_clear Hm1.
    by iDestruct ("Himpl" with "[] [] HΦ HR") as "[HΨ HR]"; last iFrame.
  Qed.

  Lemma big_sepM2_sepM_impl_res `{Countable K} {A B C}
    (Φ : K → A -> B → PROP) (Ψ : K → C → PROP) (R : PROP)
    (m1 : gmap K A) (m2 : gmap K B) (m3 : gmap K C) :
    dom m3 = dom m1 ->
    ([∗ map] k↦x;y ∈ m1;m2, Φ k x y) -∗
    R -∗
    □ (∀ (k : K) (x : A) (y : B) (z : C),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ → ⌜m3 !! k = Some z⌝ →
         Φ k x y -∗ R -∗ Ψ k z ∗ R) -∗
    ([∗ map] k↦z ∈ m3, Ψ k z) ∗ R.
  Proof.
    iIntros (Hdom) "Hm1m2 HR #Himpl".
    rewrite big_sepM2_alt.
    iDestruct "Hm1m2" as "[%Hdom' Hm1m2]".
    iDestruct (big_sepM_impl_dom_eq_res (λ k xy, Φ k xy.1 xy.2) Ψ R (map_zip m1 m2) m3
                with "[Hm1m2] HR []") as "[HΨ Hm3]"; [| iFrame | | iFrame].
    { rewrite dom_map_zip_with_L. set_solver. }
    iIntros "!>" (k p z Hm1m2 Hm3) "HΦ HR".
    rewrite map_lookup_zip_Some in Hm1m2.
    destruct Hm1m2 as [Hm1 Hm2].
    by iDestruct ("Himpl" with "[] [] [] HΦ HR") as "[HΨ HR]"; last iFrame.
  Qed.

  Lemma big_sepM2_impl_dom_eq_res `{Countable K} {A B C D}
    (Φ : K → A -> B → PROP) (Ψ : K → C → D -> PROP) (R : PROP)
    (m1 : gmap K A) (m2 : gmap K B) (m3 : gmap K C) (m4 : gmap K D) :
    dom m3 = dom m1 ->
    dom m4 = dom m1 ->
    ([∗ map] k↦x;y ∈ m1;m2, Φ k x y) -∗
    R -∗
    □ (∀ (k : K) (x : A) (y : B) (z : C) (w : D),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ →
         ⌜m3 !! k = Some z⌝ → ⌜m4 !! k = Some w⌝ →
         Φ k x y -∗ R -∗ Ψ k z w ∗ R) -∗
    ([∗ map] k↦z;w ∈ m3;m4, Ψ k z w) ∗ R.
  Proof.
    iIntros (Hdomm3 Hdomm4) "Hm1m2 HR #Himpl".
    rewrite 2!big_sepM2_alt.
    iDestruct "Hm1m2" as "[%Hdom' Hm1m2]".
    iDestruct (big_sepM_impl_dom_eq_res (λ k xy, Φ k xy.1 xy.2) (λ k zw, Ψ k zw.1 zw.2)
                 R (map_zip m1 m2) (map_zip m3 m4)
                with "[Hm1m2] HR []") as "[HΨ Hm3]"; [| iFrame | | ]; last 1 first.
    { iFrame. iSplit; last done. iPureIntro. by rewrite Hdomm3 Hdomm4. }
    { rewrite 2!dom_map_zip_with_L. set_solver. }
    iIntros "!>" (k [x y] [z w] Hm1m2 Hm3m4) "HΦ HR".
    rewrite map_lookup_zip_Some in Hm1m2.
    destruct Hm1m2 as [Hm1 Hm2].
    rewrite map_lookup_zip_Some in Hm3m4.
    destruct Hm3m4 as [Hm3 Hm4].
    by iDestruct ("Himpl" with "[] [] [] [] HΦ HR") as "[HΨ HR]"; last iFrame.
  Qed.

  Lemma big_sepM_sepM2_impl `{Countable K} {A B}
    (Φ : K → A → PROP) (Ψ : K → A -> B → PROP)
    (m1 : gmap K A) (m2 : gmap K B) :
    dom m2 = dom m1 →
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    □ (∀ (k : K) (x : A) (y : B),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ →
         Φ k x -∗ Ψ k x y) -∗
    ([∗ map] k↦x;y ∈ m1;m2, Ψ k x y).
  Proof.
    iIntros (Hdom) "Hm1 #Himpl".
    iDestruct (big_sepM_sepM2_impl_res Φ Ψ emp with "Hm1 [] []")
      as "[HΨ _]"; [done | done | | by iFrame].
    iIntros "!>" (k x y Hx Hy) "HΦ _".
    by iDestruct ("Himpl" with "[] [] HΦ") as "HΨ"; last iFrame.
  Qed.

  Lemma big_sepM2_sepM_impl `{Countable K} {A B C}
    (Φ : K → A -> B → PROP) (Ψ : K → C → PROP)
    (m1 : gmap K A) (m2 : gmap K B) (m3 : gmap K C) :
    dom m3 = dom m1 ->
    ([∗ map] k↦x;y ∈ m1;m2, Φ k x y) -∗
    □ (∀ (k : K) (x : A) (y : B) (z : C),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ → ⌜m3 !! k = Some z⌝ →
         Φ k x y -∗ Ψ k z) -∗
    ([∗ map] k↦z ∈ m3, Ψ k z).
  Proof.
    iIntros (Hdom) "Hm1m2 #Himpl".
    iDestruct (big_sepM2_sepM_impl_res Φ Ψ emp _ _ m3 with "Hm1m2 [] []")
      as "[HΨ _]"; [done | done | | by iFrame].
    iIntros "!>" (k x y z Hx Hy Hz) "HΦ _".
    by iDestruct ("Himpl" with "[] [] [] HΦ") as "HΨ"; last iFrame.
  Qed.

  Lemma big_sepM2_impl_dom_eq `{Countable K} {A B C D}
    (Φ : K → A -> B → PROP) (Ψ : K → C → D -> PROP)
    (m1 : gmap K A) (m2 : gmap K B) (m3 : gmap K C) (m4 : gmap K D) :
    dom m3 = dom m1 ->
    dom m4 = dom m1 ->
    ([∗ map] k↦x;y ∈ m1;m2, Φ k x y) -∗
    □ (∀ (k : K) (x : A) (y : B) (z : C) (w : D),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ →
         ⌜m3 !! k = Some z⌝ → ⌜m4 !! k = Some w⌝ →
         Φ k x y -∗ Ψ k z w) -∗
    ([∗ map] k↦z;w ∈ m3;m4, Ψ k z w).
  Proof.
    iIntros (Hdomm3 Hdomm4) "Hm1m2 #Himpl".
    iDestruct (big_sepM2_impl_dom_eq_res Φ Ψ emp _ _ m3 m4 with "Hm1m2 [] []")
      as "[HΨ _]"; [done | done | done | | by iFrame].
    iIntros "!>" (k x y z w Hx Hy Hz Hw) "HΦ _".
    by iDestruct ("Himpl" with "[] [] [] [] HΦ") as "HΨ"; last iFrame.
  Qed.

  Lemma big_sepM_impl_res `{Countable K} {A}
    (Φ : K → A → PROP) (Ψ : K → A → PROP) (R : PROP) (m : gmap K A) :
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    R -∗
    □ (∀ (k : K) (x : A),
         ⌜m !! k = Some x⌝ →
         Φ k x -∗ R -∗ Ψ k x ∗ R) -∗
    ([∗ map] k↦y ∈ m, Ψ k y) ∗ R.
  Proof.
    iIntros "Hm HR #Himpl".
    iDestruct (big_sepM_impl_dom_eq_res _ Ψ _ m m with "Hm HR []")
      as "[HΨ Hm]"; [done | | iFrame].
    iIntros "!>" (k x y Hx Hy) "HΦ HR".
    rewrite Hx in Hy. inversion Hy. subst y.
    by iApply ("Himpl" with "[] HΦ HR").
  Qed.

  Lemma big_sepM2_impl_res `{Countable K} {A B}
    (Φ : K → A → B -> PROP) (Ψ : K → A -> B → PROP) (R : PROP)
    (m1 : gmap K A) (m2 : gmap K B) :
    ([∗ map] k↦x;y ∈ m1;m2, Φ k x y) -∗
    R -∗
    □ (∀ (k : K) (x : A) (y : B),
         ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ →
         Φ k x y -∗ R -∗ Ψ k x y ∗ R) -∗
    ([∗ map] k↦x;y ∈ m1;m2, Ψ k x y) ∗ R.
  Proof.
    iIntros "HΦ HR #Himpl".
    rewrite 2!big_sepM2_alt.
    iDestruct "HΦ" as "[%Hdom HΦ]".
    iDestruct (big_sepM_impl_res _ (λ k xy, Ψ k xy.1 xy.2) with "HΦ HR []") as "[HΨ Hm]".
    { iIntros "!>" (k xy Hxy) "HΦ HR".
      destruct xy as [x y].
      rewrite map_lookup_zip_Some in Hxy.
      destruct Hxy as [Hx Hy].
      by iDestruct ("Himpl" with "[] [] HΦ HR") as "[HΨ HR]"; last iFrame.
    }
    iFrame "∗ %".
  Qed.

  Lemma big_sepS_impl_res `{Countable A}
    (Φ : A → PROP) (Ψ : A → PROP) (R : PROP) (X : gset A) :
    ([∗ set] x ∈ X, Φ x) -∗
    R -∗
    □ (∀ (x : A), ⌜x ∈ X⌝ → Φ x -∗ R -∗ Ψ x ∗ R) -∗
    ([∗ set] x ∈ X, Ψ x) ∗ R.
  Proof.
    iInduction X as [| x X Hnotin] "IH" using set_ind_L.
    { iIntros "HX HR #Himpl". by iFrame "HR". }
    iIntros "HX HR #Himpl".
    do 2 (rewrite big_sepS_union; last set_solver).
    rewrite 2!big_sepS_singleton.
    iDestruct "HX" as "[Hx HX]".
    iDestruct ("IH" with "HX HR []") as "[HX HR]".
    { iIntros "!>" (y Hy) "Hy HR".
      iDestruct ("Himpl" with "[] Hy HR") as "[Hx HR]".
      { iPureIntro. set_solver. }
      iFrame.
    }
    iDestruct ("Himpl" with "[] Hx HR") as "[Hx HR]".
    { iPureIntro. set_solver. }
    iFrame.
  Qed.

  Lemma big_sepM_dom_subseteq_difference `{Countable K} {A}
    (Φ : K -> A -> PROP) (m : gmap K A) (s : gset K) :
    s ⊆ dom m ->
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    ∃ m', ⌜dom m' = s ∧ m' ⊆ m⌝ ∗
          ([∗ map] k↦x ∈ m', Φ k x) ∗ ([∗ map] k↦x ∈ m ∖ m', Φ k x).
  Proof.
    iInduction s as [| k s] "IH" using set_ind_L forall (m).
    { iIntros (_) "Hm".
      iExists ∅. iSplit.
      { iPureIntro. split; [done | apply map_empty_subseteq]. }
      rewrite big_sepM_empty map_difference_empty.
      by auto.
    }
    iIntros (Hsubseteq) "Hm".
    rewrite union_subseteq -elem_of_subseteq_singleton elem_of_dom in Hsubseteq.
    destruct Hsubseteq as [Hk Hs].
    destruct Hk as [v Hk].
    iDestruct (big_sepM_delete with "Hm") as "[Hk Hm]"; first apply Hk.
    iDestruct ("IH" with "[] Hm") as (m') "(Hdom & Hm' & Hm)".
    { iPureIntro. set_solver. }
    iDestruct "Hdom" as %[Hdom Hsubseteq].
    iExists (insert k v m').
    iSplit.
    { iPureIntro.
      split; first set_solver.
      apply insert_subseteq_l; first done.
      transitivity (delete k m); [done | apply delete_subseteq].
    }
    rewrite big_sepM_insert; last by rewrite -not_elem_of_dom Hdom.
    iFrame.
    iApply (big_sepM_impl_dom_eq with "Hm"); first set_solver.
    iIntros "!>" (i x y Hx Hy) "HΦ".
    replace y with x; first done.
    rewrite lookup_difference in Hx. rewrite lookup_difference in Hy.
    destruct (decide (i = k)) as [-> | Hne]; first by rewrite lookup_insert_eq in Hy.
    rewrite lookup_insert_ne in Hy; last done.
    destruct (m' !! i) as [? |]; first done.
    rewrite lookup_delete_ne in Hx; last done.
    rewrite Hx in Hy.
    by inversion Hy.
  Qed.

  Lemma big_sepM_subseteq_difference_1 `{Countable K} {A}
    (Φ : K -> A -> PROP) (m1 m2 : gmap K A) :
    m1 ⊆ m2 ->
    ([∗ map] k↦x ∈ m2, Φ k x) -∗
    ([∗ map] k↦x ∈ m1, Φ k x) ∗ ([∗ map] k↦x ∈ m2 ∖ m1, Φ k x).
  Proof.
    iIntros (Hsubseteq) "Hm2".
    rewrite -{1}(map_difference_union _ _ Hsubseteq) big_sepM_union; last first.
    { by apply map_disjoint_difference_r1. }
    iFrame.
  Qed.

  Lemma big_sepM_subseteq_difference_2 `{Countable K} {A}
    (Φ : K -> A -> PROP) (m1 m2 : gmap K A) :
    m1 ⊆ m2 ->
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    ([∗ map] k↦x ∈ m2 ∖ m1, Φ k x) -∗
    ([∗ map] k↦x ∈ m2, Φ k x).
  Proof.
    iIntros (Hsubseteq) "Hm1 Hm2m1".
    rewrite -{2}(map_difference_union _ _ Hsubseteq) big_sepM_union; last first.
    { by apply map_disjoint_difference_r1. }
    iFrame.
  Qed.

  Lemma big_sepM_dom_subseteq_acc `{Countable K} {A}
    (Φ : K -> A -> PROP) (m : gmap K A) (s : gset K) :
    s ⊆ dom m ->
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    ∃ m', ⌜dom m' = s⌝ ∗ ([∗ map] k↦x ∈ m', Φ k x) ∗
          (([∗ map] k↦x ∈ m', Φ k x) -∗ ([∗ map] k↦x ∈ m, Φ k x)).
  Proof.
    iInduction s as [| k s] "IH" using set_ind_L forall (m).
    { iIntros (_) "Hm".
      iExists ∅. iSplit; first done.
      rewrite big_sepM_empty.
      by auto.
    }
    iIntros (Hsubseteq) "Hm".
    rewrite union_subseteq -elem_of_subseteq_singleton elem_of_dom in Hsubseteq.
    destruct Hsubseteq as [Hk Hs].
    destruct Hk as [v Hk].
    iDestruct (big_sepM_delete with "Hm") as "[Hk Hm]"; first apply Hk.
    iDestruct ("IH" with "[] Hm") as (m') "(Hdom & Hm' & Hacc)".
    { iPureIntro. set_solver. }
    (* not sure why % doesn't work on the above ipat *)
    iDestruct "Hdom" as "%Hdom".
    iExists (insert k v m').
    iSplit.
    { iPureIntro. set_solver. }
    rewrite big_sepM_insert; last by rewrite -not_elem_of_dom Hdom.
    iFrame.
    iIntros "[Hk Hm']".
    iDestruct ("Hacc" with "Hm'") as "Hm".
    iApply big_sepM_delete; first apply Hk.
    iFrame.
  Qed.

  Lemma big_sepS_big_sepM `{Countable K} {A} (Φ : K -> PROP) (m : gmap K A) :
    ([∗ set] k ∈ dom m, Φ k) ⊣⊢ ([∗ map] k ↦ v ∈ m, Φ k).
  Proof.
    iInduction m as [| k x m Hnone] "IH" using map_ind.
    { rewrite dom_empty_L. by iSplit; iIntros "_". }
    rewrite dom_insert_L big_sepS_insert; last first.
    { by apply not_elem_of_dom_2. }
    rewrite big_sepM_insert; last apply Hnone.
    by iSplit; iIntros "Hm"; iDestruct "Hm" as "[Hk Hm]";  iFrame; iApply "IH".
  Qed.

  Lemma big_sepM_sepS_impl `{Countable K} {A}
    (Φ : K → A → PROP) (Ψ : K → PROP) (m : gmap K A) (s : gset K) :
    dom m = s →
    ([∗ map] k ↦ x ∈ m, Φ k x) -∗
    □ (∀ (k : K) (x : A), ⌜m !! k = Some x⌝ → Φ k x -∗ Ψ k) -∗
    ([∗ set] k ∈ s, Ψ k).
  Proof.
    iIntros (Hdom) "Hm #Himpl".
    rewrite -Hdom big_sepS_big_sepM.
    by iApply (big_sepM_impl with "Hm").
  Qed.

  Lemma big_sepS_sepM_impl `{Countable K} {A}
    (Φ : K → PROP) (Ψ : K → A -> PROP) (s : gset K) (m : gmap K A) :
    dom m = s →
    ([∗ set] k ∈ s, Φ k) -∗
    □ (∀ (k : K) (x : A), ⌜m !! k = Some x⌝ → Φ k -∗ Ψ k x) -∗
    ([∗ map] k ↦ x ∈ m, Ψ k x).
  Proof.
    iIntros (Hdom) "Hs #Himpl".
    rewrite -Hdom big_sepS_big_sepM.
    by iApply (big_sepM_impl with "Hs").
  Qed.

  Lemma big_sepM_big_sepM2_1 `{Countable K} {A B}
    (Φ : K -> A -> PROP) (m1 : gmap K A) (m2 : gmap K B) :
    dom m2 = dom m1 ->
    ([∗ map] k ↦ v ∈ m1, Φ k v) -∗
    ([∗ map] k ↦ v;_ ∈ m1;m2, Φ k v).
  Proof.
    iIntros (Hdom) "Hm1".
    iApply (big_sepM_sepM2_impl with "Hm1"); first apply Hdom.
    by iIntros "!>" (k x y Hx Hy) "HΦ".
  Qed.

  Lemma big_sepM_big_sepM2_2 `{Countable K} {A B}
    (Φ : K -> A -> PROP) (m1 : gmap K A) (m2 : gmap K B) :
    ([∗ map] k ↦ v;_ ∈ m1;m2, Φ k v) -∗
    ([∗ map] k ↦ v ∈ m1, Φ k v).
  Proof.
    iIntros "Hm1m2".
    iApply (big_sepM2_sepM_impl with "Hm1m2"); first done.
    iIntros "!>" (k x y z Hx Hy Hz) "HΦ".
    rewrite Hx in Hz.
    by inv Hz.
  Qed.

  Lemma big_sepM_big_sepM2 `{Countable K} {A B}
    (Φ : K -> A -> PROP) (m1 : gmap K A) (m2 : gmap K B) :
    dom m2 = dom m1 ->
    ([∗ map] k ↦ v ∈ m1, Φ k v) ⊣⊢ ([∗ map] k ↦ v;_ ∈ m1;m2, Φ k v).
  Proof.
    iIntros (Hdom).
    by iSplit; [iApply big_sepM_big_sepM2_1 | iApply big_sepM_big_sepM2_2].
  Qed.

  Lemma big_sepM_exists_sepM2 `{Countable K} {A B}
    (Φ : K -> A -> B -> PROP) (m : gmap K A) :
    ([∗ map] k ↦ x ∈ m, ∃ y, Φ k x y) -∗
    ∃ m', ([∗ map] k ↦ x; y ∈ m; m', Φ k x y).
  Proof.
    iIntros "Hm".
    iInduction m as [| k x m Hmk] "IH" using map_ind.
    { iExists ∅. by rewrite big_sepM2_empty. }
    iDestruct (big_sepM_insert with "Hm") as "[[%y Hy] Hm]"; first apply Hmk.
    iSpecialize ("IH" with "Hm").
    iDestruct "IH" as (m') "Hm".
    iExists (<[k := y]> m').
    iDestruct (big_sepM2_dom with "Hm") as %Hdom.
    iApply big_sepM2_insert.
    { apply Hmk. }
    { rewrite -not_elem_of_dom -Hdom. by apply not_elem_of_dom in Hmk. }
    iFrame.
  Qed.

  Lemma big_sepS_subseteq_difference_1 `{Countable A} (Φ : A -> PROP) (X Y : gset A) :
    Y ⊆ X ->
    ([∗ set] x ∈ X, Φ x) -∗
    ([∗ set] x ∈ Y, Φ x) ∗ ([∗ set] x ∈ X ∖ Y, Φ x).
  Proof.
    iIntros (Hsubseteq) "HX".
    rewrite {1}(union_difference_L _ _ Hsubseteq).
    iDestruct (big_sepS_union with "HX") as "[HY Hacc]"; first set_solver.
    iFrame.
  Qed.

  Lemma big_sepS_subseteq_difference_2 `{Countable A} (Φ : A -> PROP) (X Y : gset A) :
    Y ⊆ X ->
    ([∗ set] x ∈ Y, Φ x) -∗
    ([∗ set] x ∈ X ∖ Y, Φ x) -∗
    ([∗ set] x ∈ X, Φ x).
  Proof.
    iIntros (Hsubseteq) "HY HXY".
    rewrite {2}(union_difference_L _ _ Hsubseteq).
    rewrite big_sepS_union; last set_solver.
    iFrame.
  Qed.

  Lemma big_sepS_subseteq_acc `{Countable A} (Φ : A -> PROP) (X Y : gset A) :
    Y ⊆ X ->
    ([∗ set] x ∈ X, Φ x) -∗
    ([∗ set] x ∈ Y, Φ x) ∗
    (([∗ set] x ∈ Y, Φ x) -∗ ([∗ set] x ∈ X, Φ x)).
  Proof.
    iIntros (Hsubseteq) "HX".
    iDestruct (big_sepS_subseteq_difference_1 with "HX") as "[HY HXY]"; first apply Hsubseteq.
    iFrame. iIntros "HY".
    by iDestruct (big_sepS_subseteq_difference_2 with "HY HXY") as "HX"; first apply Hsubseteq.
  Qed.

  Lemma big_sepS_partition_1
    `{!BiAffine PROP} `{Countable A} (Φ : A -> PROP) (X : gset A) `{Countable B} (Y : gset B)
    (P : A -> B -> Prop) `{∀ x y, Decision (P x y)} :
    (∀ x y1 y2, y1 ≠ y2 -> P x y1 -> not (P x y2)) ->
    ([∗ set] x ∈ X, Φ x) -∗
    ([∗ set] y ∈ Y, [∗ set] x ∈ filter (λ x', P x' y) X, Φ x).
  Proof.
    iIntros (Hpart) "HX".
    iInduction X as [| x X] "IH" using set_ind_L.
    { rewrite big_sepS_sepS. by iApply big_sepS_empty. }
    iDestruct (big_sepS_insert with "HX") as "[Hx HX]"; first done.
    iSpecialize ("IH" with "HX").
    iAssert ([∗ set] y ∈ filter (λ y', P x y') Y, Φ x)%I with "[Hx]" as "Hx".
    { destruct (decide (filter (λ y', P x y') Y = ∅)) as [-> | Hne].
      { by iApply big_sepS_empty. }
      apply set_choose_L in Hne as [y Hy].
      (* rewrite elem_of_filter in Hy. *)
      replace (filter _ Y) with ({[y]} : gset B); last first.
      { apply set_eq.
        intros y'.
        split; intros Hy'.
        { rewrite elem_of_singleton in Hy'. by subst y'. }
        apply elem_of_filter in Hy as [HP Hy].
        apply elem_of_filter in Hy' as [HP' Hy'].
        destruct (decide (y = y')) as [-> | Hne]; first by rewrite elem_of_singleton.
        exfalso.
        by specialize (Hpart _ _ _ Hne HP).
      }
      by rewrite big_sepS_singleton.
    }
    rewrite big_sepS_filter'.
    iCombine "IH Hx" as "HX".
    rewrite -big_sepS_sep.
    iApply (big_sepS_mono with "HX").
    iIntros (y Hy) "[HX Hx]".
    rewrite filter_union_L.
    case_decide as HP; last first.
    { rewrite filter_singleton_False_L; [by rewrite union_empty_l_L | apply HP]. }
    rewrite filter_singleton_True_L; last apply HP.
    iApply (big_sepS_insert_2 with "Hx HX").
  Qed.

  Lemma big_sepS_partition_2
    `{!BiAffine PROP} `{Countable A} (Φ : A -> PROP) (X : gset A) `{Countable B} (Y : gset B)
    (P : A -> B -> Prop) `{∀ x y, Decision (P x y)} :
    (∀ x, x ∈ X -> ∃ y, y ∈ Y ∧ P x y) ->
    ([∗ set] y ∈ Y, [∗ set] x ∈ filter (λ x', P x' y) X, Φ x) -∗
    ([∗ set] x ∈ X, Φ x).
  Proof.
    iIntros (Hpart) "HYX".
    iInduction X as [| x X Hnotin] "IH" using set_ind_L.
    { by iApply big_sepS_empty. }
    rewrite big_sepS_union; last set_solver.
    assert (Hx : x ∈ {[x]} ∪ X) by set_solver.
    pose proof (Hpart _ Hx) as (y & Hy & HP).
    iDestruct (big_sepS_elem_of_acc_impl with "HYX") as "[HΦ HYX]"; first apply Hy.
    rewrite filter_union_L big_sepS_union; last set_solver.
    iDestruct "HΦ" as "[Hx HX]".
    (* rewrite filter_union_L elem_of_union in Hpart. *)
    (* destruct Hpart as [Hin | Hcontra]; last set_solver. *)
    rewrite filter_singleton_True_L; last apply HP.
    iFrame "Hx".
    iSpecialize ("HYX" $! (λ y, [∗ set] x ∈ filter (λ x', P x' y) X, Φ x)%I with "[] HX").
    { iIntros "!>" (y' _ _) "HΦ".
      rewrite filter_union_L big_sepS_union; last set_solver.
      by iDestruct "HΦ" as "[_ HΦ]".
    }
    iApply ("IH" with "[] HYX").
    iPureIntro.
    intros x' Hx'.
    assert (Hin : x' ∈ {[x]} ∪ X) by set_solver.
    by apply Hpart.
  Qed.

  Lemma big_sepS_delete_affine `{Countable A} `{!BiAffine PROP}
    (Φ : A -> PROP) (s : gset A) (x : A) :
    ([∗ set] y ∈ s, Φ y) -∗
    ([∗ set] y ∈ s ∖ {[x]}, Φ y).
  Proof.
    iIntros "Hs".
    iApply (big_sepS_subseteq with "Hs").
    set_solver.
  Qed.

  Lemma big_sepM_delete_affine `{Countable K} {A}
    `{!BiAffine PROP} (Φ : K -> A -> PROP) (m : gmap K A) (k : K) :
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    ([∗ map] k↦x ∈ (delete k m), Φ k x).
  Proof.
    iIntros "Hm".
    destruct (m !! k) as [x |] eqn:Hm; last first.
    { by rewrite delete_id. }
    iDestruct (big_sepM_delete with "Hm") as "[_ Hm]".
    { apply Hm. }
    done.
  Qed.

  Lemma big_sepM2_delete_affine `{Countable K} {A B}
    `{!BiAffine PROP} (Φ : K -> A -> B -> PROP) (m1 : gmap K A) (m2 : gmap K B) (k : K) :
    ([∗ map] k↦x;y ∈ m1; m2, Φ k x y) -∗
    ([∗ map] k↦x;y ∈ (delete k m1); (delete k m2), Φ k x y).
  Proof.
    iIntros "Hm".
    iDestruct (big_sepM2_dom with "Hm") as %Hdom.
    destruct (m1 !! k) as [x |] eqn:Hm1; last first.
    { assert (Hm2 : m2 !! k = None).
      { by rewrite -not_elem_of_dom -Hdom not_elem_of_dom. }
      do 2 (rewrite delete_id; last done).
      done.
    }
    assert (is_Some (m2 !! k)) as [y Hm2].
    { by rewrite -elem_of_dom -Hdom elem_of_dom. }
    iDestruct (big_sepM2_delete with "Hm") as "[Hxy Hm]".
    { apply Hm1. }
    { apply Hm2. }
    by iFrame "Hm".
  Qed.

End bi.
