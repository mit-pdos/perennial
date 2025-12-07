From New.golang.defn Require Export array.
From New.golang.theory Require Export predeclared.

Section lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {core_sem : go.CoreSemantics}
  {pre_sem : go.PredeclaredSemantics}
  {array_sem : go.ArraySemantics}.

Context `{!ZeroVal V} `{!go.GoZeroValEq t V}.
Context `{!TypedPointsto (Σ:=Σ) V}.
Context `{!IntoValTyped V t}.

Program Global Instance typed_pointsto_array n :
  TypedPointsto (array.t t V n) :=
  {|
    typed_pointsto_def l dq v :=
      (⌜ Z.of_nat $ length (array.arr v) = n ⌝ ∗
       [∗ list] i ↦ ve ∈ (array.arr v), array_index_ref t (Z.of_nat i) l ↦{dq} ve)%I;
  |}.
Final Obligation.
Proof.
  intros. iIntros "* [%Hlen1 H1] [%Hlen2 H2]".
  destruct v1 as [vs1], v2 as [vs2]. simpl in *.
  assert (length vs1 = length vs2) as Hlen by lia.
  clear -Hlen IntoValTyped0 core_sem array_sem.
  (iInduction vs1 as [|v1 vs1] "IH" forall (l vs2 Hlen)).
  { simpl in Hlen.
    destruct vs2; simpl in Hlen; try congruence.
    auto. }
  destruct vs2; simpl in Hlen; first by congruence.
  simpl.
  iDestruct "H1" as "[Hx1 H1]".
  iDestruct "H2" as "[Hx2 H2]".
  iCombine "Hx1 Hx2" gives %->.
  setoid_rewrite Nat2Z.inj_succ.
  setoid_rewrite <- Z.add_1_l.
  setoid_rewrite go.array_index_ref_add.
  iDestruct ("IH" $! _ vs2 with "[] H1 H2") as %H; auto.
  by simplify_eq.
Qed.

Lemma array_len ptr dq n vs :
  ptr ↦{dq} (array.mk t n vs) -∗ ⌜ n = Z.of_nat $ length vs ⌝.
Proof.
  rewrite typed_pointsto_unseal. simpl. iIntros "[% _] !%". done.
Qed.

Lemma seqZ_succ start n :
  0 ≤ n →
  seqZ start (Z.succ n) = seqZ start n ++ [start + n].
Proof.
  intros Hle. rewrite /seqZ Z2Nat.inj_succ; last lia.
  rewrite seq_S fmap_app /=. f_equal. f_equal. lia.
Qed.

Global Instance into_val_typed_array n : IntoValTyped (array.t t V n) (go.ArrayType n t).
Proof.
  split.
  - apply _.
  - admit.
  - iIntros "* Hl HΦ".
    rewrite go.load_array. case_decide.
    { wp_pures. wp_apply wp_AngelicExit. }
    wp_pure. wp_pure.
    assert (∃ m, n = m ∧ 0 ≤ m ≤ n) as (m & Heq & Hm) by (exists n; lia).
    rewrite [in #(W64 n)]Heq.
    simpl. destruct v as [vs]. simpl in *.
    iDestruct (array_len with "Hl") as "%Hlen".
    iApply (wp_wand _ _ _
                    (λ v, ∃ vs' ,
                        "Hl" ∷ l ↦{dq} array.mk t n vs ∗
                        "->" ∷ ⌜ v = #(array.mk t n vs') ⌝ ∗
                        "%Hagree" ∷ ⌜ take (Z.to_nat m) vs = take (Z.to_nat m) vs' ⌝ ∗
                        "%Hlen'" ∷ ⌜ length vs = length vs' ⌝
                    )%I
             with "[-HΦ] [HΦ]").
    2:{ iIntros "% H". iNamed "H". subst.
        rewrite !take_ge in Hagree; [|len..]. subst.
        by iApply "HΦ". }
    clear Heq Φ.
    set (f := #(func.mk _ _ _)).
    iLöb as "IH" forall (m Hm).
    wp_pures.
    case_bool_decide as Heq.
    { wp_pures. rewrite go.go_zero_val_eq. simpl. iFrame. iPureIntro.
      replace m with 0 by word. setoid_rewrite take_0. eexists _; split; first done.
      split; [done|len]. }
    wp_pure. wp_pure. set (m':=m-1).
    replace (word.sub _ _) with (W64 m') by word.
    progress replace (Z.to_nat m) with (S (Z.to_nat m'))%nat by word.
    pose proof (list_lookup_lt vs (Z.to_nat m')) as [ve Hlookup]; first word.
    erewrite take_S_r; last done.
    iSpecialize ("IH" with "[] Hl"); last wp_apply (wp_wand with "IH"); first word.
    iIntros "% H". iNamed "H". wp_pures. rewrite go.index_ref_array. wp_pures.
    rewrite typed_pointsto_unseal.
    iDestruct "Hl" as "[% Hl]".
    iDestruct (big_sepL_lookup_acc with "Hl") as "[H Hl]"; first done.
    replace (sint.Z (word.sub _ _)) with m' by word.
    replace (Z.of_nat (Z.to_nat m')) with m' by word.
    wp_apply (wp_load with "H"). iIntros "H". iSpecialize ("Hl" with "H").
    wp_pures. iExists _. iFrame. iPureIntro.
    split_and!; try done; last len.
    erewrite take_S_r.
    2:{ replace (sint.nat _) with (Z.to_nat m') by word.
        rewrite list_lookup_insert_eq //.
        word. }
    f_equal. rewrite take_insert_ge; last len. done.
  - admit.
    Unshelve. Fail idtac.
Admitted.

Lemma array_empty ptr dq :
  ⊢ ptr ↦{dq} (array.mk t 0 []).
Proof.
  rewrite typed_pointsto_unseal. simpl. iPureIntro. done.
Qed.

Lemma array_acc p (i : Z) dq n (a : array.t t V n) (v: V) :
  0 ≤ i →
  array.arr a !! (Z.to_nat i) = Some v →
  p ↦{dq} a -∗
  array_index_ref t i p ↦{dq} v ∗
  (∀ v', array_index_ref t i p ↦{dq} v' -∗
        p ↦{dq} (array.mk t n $ <[(Z.to_nat i) := v']> $ array.arr a)).
Proof.
  iIntros (Hpos Hlookup) "Harr".
  rewrite [in _ (array.t _ _ _)]typed_pointsto_unseal /=.
  iDestruct "Harr" as "[% Harr]".
  iDestruct (big_sepL_insert_acc _ _ (Z.to_nat i) with "Harr") as "[Hptsto Harr]".
  { done. }
  nat_cleanup. iFrame "Hptsto". iIntros (?) "Hptsto".
  iSpecialize ("Harr" with "Hptsto").
  iFrame. rewrite length_insert. done.
Qed.

Lemma array_split (k : w64) l dq n (a : array.t t V n) :
  0 ≤ sint.Z k ≤ sint.Z n →
  l ↦{dq} a ⊣⊢
  l ↦{dq} (array.mk t (sint.Z k) $ take (sint.nat k) $ array.arr a) ∗
  array_index_ref t (sint.Z k) l ↦{dq} (array.mk t (n - sint.Z k) $ drop (sint.nat k) $ array.arr a).
Proof.
  intros Hle. rewrite typed_pointsto_unseal /=. destruct a as [arr]. simpl.
  rewrite -{1}(take_drop (sint.nat k) arr).
  setoid_rewrite <- go.array_index_ref_add. len.
  iSplit.
  - iIntros "[% H]". subst. rewrite -!assoc. iSplitR; first len.
    rewrite comm. rewrite -assoc. iSplitR; first word.
    rewrite -{1}(take_drop (sint.nat k) arr).
    rewrite big_sepL_app. iDestruct "H" as "[H1 H2]".
    iFrame. iApply (big_sepL_impl with "H2").
    iIntros "!# * % H". iExactEq "H". f_equal.
    f_equal. len.
  - iIntros "([% H1] & [% H2])".
    iSplitR; first word.
    rewrite -{3}(take_drop (sint.nat k) arr).
    rewrite big_sepL_app. iFrame.
    iApply (big_sepL_impl with "H2").
    iIntros "!# * % H". iExactEq "H". f_equal.
    f_equal. len.
Qed.

Global Instance pure_wp_slice_array elem_type n p low high :
  PureWp (0 ≤ word.signed low ≤ word.signed high ≤ n)
    (Slice (go.ArrayType n elem_type) (#p, (#low, #high))%V)
       #(slice.mk (array_index_ref elem_type (word.signed low) p)
           (word.sub high low)
           (word.sub (W64 n) low)).
Proof.
  pose proof go.slice_array_step. pure_wp_start.
  rewrite decide_True //. wp_pures. iApply "HΦ".
Qed.

End lemmas.
