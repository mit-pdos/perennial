From Perennial.Helpers Require Import List ListLen Fractional NamedProps.
From iris.algebra Require Import dfrac.
From New.golang.defn Require Export slice.
From New.golang.theory Require Export list mem exception loop typing auto.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Transparent slice.ptr slice.len slice.cap slice.make3 slice.make2
  slice.elem_ref slice.slice slice.full_slice slice.for_range
  slice.copy slice.append slice.literal.

Module slice.
Definition slice_f (sl : slice.t) (t : go_type) (n1 n2 : u64) : slice.t :=
  slice.mk (sl.(slice.ptr_f) +ₗ[t] uint.Z n1) (word.sub n2 n1) (word.sub sl.(slice.cap_f) n1).

Definition elem_ref_f (sl : slice.t) (t : go_type) (i : u64) : loc :=
  sl.(slice.ptr_f) +ₗ[t] (uint.Z i).

End slice.

Section defns_and_lemmas.
Context `{ffi_syntax} `{ffi_interp}.
Context `{!heapGS Σ}.

Definition own_slice_def `{!IntoVal V} `{!IntoValTyped V t} (s : slice.t) (dq : dfrac) (vs : list V): iProp Σ :=
  ([∗ list] i ↦ v ∈ vs, (s.(slice.ptr_f) +ₗ[t] i) ↦{dq} v ) ∗
  ⌜length vs = uint.nat s.(slice.len_f) ∧ uint.Z s.(slice.len_f) ≤ uint.Z s.(slice.cap_f)⌝.
Program Definition own_slice := unseal (_:seal (@own_slice_def)). Obligation 1. by eexists. Qed.
Definition own_slice_unseal : own_slice = _ := seal_eq _.

Global Arguments own_slice {_ _ _ _} (s dq vs).

Notation "s ↦* dq vs" := (own_slice s dq vs)
                            (at level 20, dq custom dfrac at level 50, format "s  ↦* dq  vs").

Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Implicit Type (vs : list V).
Definition own_slice_cap_def (s : slice.t) : iProp Σ :=
  ⌜ uint.Z s.(slice.len_f) ≤ uint.Z s.(slice.cap_f) ⌝ ∗
  [∗ list] i ∈ (seq (uint.nat s.(slice.len_f)) (uint.nat s.(slice.cap_f) - uint.nat s.(slice.len_f))),
    (s.(slice.ptr_f) +ₗ[t] Z.of_nat i) ↦ (default_val V).
Program Definition own_slice_cap := unseal (_:seal (@own_slice_cap_def)). Obligation 1. by eexists. Qed.
Definition own_slice_cap_unseal : own_slice_cap = _ := seal_eq _.

Ltac unseal := rewrite ?own_slice_unseal /own_slice_def
                 ?own_slice_cap_unseal /own_slice_cap_def.

Lemma own_slice_cap_none s :
  s.(slice.len_f) = s.(slice.cap_f) →
  ⊢ own_slice_cap s.
Proof.
  destruct s; simpl; intros ->. rewrite own_slice_cap_unseal /own_slice_cap_def Nat.sub_diag //.
  simpl. iPureIntro. lia.
Qed.

Lemma own_slice_len s dq vs :
  s ↦*{dq} vs -∗ ⌜length vs = uint.nat s.(slice.len_f)⌝.
Proof.
  unseal. iIntros "(_&[%%]) !% //".
Qed.

Lemma replicate_0 A (x:A) : replicate 0 x = [].
Proof. reflexivity. Qed.

Instance own_slice_fractional s vs :
  fractional.Fractional (λ q, s ↦*{#q} vs).
Proof. unseal; apply _. Qed.

Instance own_slice_as_fractional s q vs :
  fractional.AsFractional (s ↦*{#q} vs) (λ q, s ↦*{#q} vs) q.
Proof. unseal; split; auto; apply _. Qed.

Lemma loc_add_stride_Sn l n :
  l +ₗ[t] S n = (l +ₗ go_type_size t) +ₗ[t] n.
Proof.
  replace (Z.mul (go_type_size t) (S n)) with (go_type_size t + Z.mul (go_type_size t) n).
  { rewrite loc_add_assoc //. }
  replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
  rewrite Z.mul_add_distr_l.
  f_equal.
  rewrite Z.mul_1_r //.
Qed.

Lemma own_slice_agree s dq1 dq2 vs1 vs2 :
  s ↦*{dq1} vs1 -∗
  s ↦*{dq2} vs2 -∗
  ⌜vs1 = vs2⌝.
Proof using Type*.
  unseal.
  iIntros "[Hs1 [%%]] [Hs2 [%%]]".
  assert (length vs1 = length vs2) by congruence.
  generalize (slice.ptr_f s). intros l.
  assert (length vs1 = length vs2) as Hlen by done.
  clear -Hlen IntoValTyped0.
  (iInduction vs1 as [|v1 vs1] "IH" forall (l vs2 Hlen)).
  { simpl in Hlen.
    destruct vs2; simpl in Hlen; try congruence.
    auto. }
  destruct vs2; simpl in Hlen; first by congruence.
  simpl.
  iDestruct "Hs1" as "[Hx1 Ha1]".
  iDestruct "Hs2" as "[Hx2 Ha2]".
  iCombine "Hx1 Hx2" gives %[_ ->].
  setoid_rewrite loc_add_stride_Sn.
  iDestruct ("IH" $! _ vs2 with "[] Ha1 Ha2") as %->; auto.
Qed.

Global Instance own_slice_persistent s vs : Persistent (s ↦*□ vs).
Proof. unseal; apply _. Qed.

Lemma own_slice_persist s dq vs:
  s ↦*{dq} vs ==∗ s ↦*□ vs.
Proof.
  unseal.
  iIntros "[Hs %Hl]".
  iSplitL; last done.
  iApply big_sepL_bupd.
  iApply (big_sepL_impl with "Hs").
  iModIntro. iIntros "* % ?".
  iApply (typed_pointsto_persist with "[$]").
Qed.

Global Instance own_slice_timeless s dq vs : Timeless (s ↦*{dq} vs).
Proof. unseal; apply _. Qed.

Lemma own_slice_not_null s dq vs :
  go_type_size t > 0 →
  length vs > 0 ->
  s ↦*{dq} vs -∗
  ⌜ s.(slice.ptr_f) ≠ null ⌝.
Proof using Type*.
  unseal.
  iIntros (Hbt Hvs) "[Hs %]".
  destruct s; destruct vs; simpl in *; try lia.
  iDestruct "Hs" as "[Hptr _]".
  rewrite Z.mul_0_r loc_add_0.
  unshelve (by iApply (typed_pointsto_not_null with "[$]")).
  done.
Qed.

Lemma own_slice_cap_wf s :
  own_slice_cap s -∗ ⌜uint.Z s.(slice.len_f) ≤ uint.Z s.(slice.cap_f)⌝.
Proof.
  unseal. by iIntros "[% Hcap]".
Qed.

Lemma own_slice_wf s dq vs :
  s ↦*{dq} vs -∗ ⌜uint.Z s.(slice.len_f) ≤ uint.Z s.(slice.cap_f)⌝.
Proof.
  unseal.
  iIntros "[? %]". naive_solver.
Qed.

Lemma own_slice_nil dq :
  ⊢ slice.nil ↦*{dq} ([] : list V).
Proof.
  unseal. simpl. iPureIntro. split_and!; done.
Qed.

Lemma own_slice_empty dq s :
  uint.Z s.(slice.len_f) = 0 ->
  ⊢ s ↦*{dq} ([] : list V).
Proof.
  unseal. intros Hsz. destruct s. simpl in *.
  iPureIntro. split_and!; [done|word|word].
Qed.

Lemma own_slice_cap_nil :
  ⊢ own_slice_cap slice.nil.
Proof.
  unseal. simpl. rewrite right_id.
  rewrite (nil_length_inv (seq _ _)).
  2:{ rewrite length_seq. word. }
  simpl. word.
Qed.

Lemma own_slice_elem_acc i v s dq vs :
  vs !! (uint.nat i) = Some v →
  s ↦*{dq} vs -∗
  slice.elem_ref_f s t i ↦{dq} v ∗
  (∀ v', slice.elem_ref_f s t i ↦{dq} v' -∗
        s ↦*{dq} (<[uint.nat i := v']> vs)).
Proof.
  iIntros (Hlookup) "Hsl".
  rewrite own_slice_unseal /own_slice_def.
  iDestruct "Hsl" as "[Hsl %]".
  iDestruct (big_sepL_insert_acc _ _ (uint.nat i) with "Hsl") as "[Hptsto Hsl]".
  { done. }
  rewrite u64_Z_through_nat.
  iFrame "Hptsto".
  iIntros (?) "Hptsto".
  iSpecialize ("Hsl" with "Hptsto").
  iFrame. rewrite length_insert. done.
Qed.

End defns_and_lemmas.

Global Notation "s ↦* dq vs" := (own_slice s dq vs)
                            (at level 20, dq custom dfrac at level 50, format "s  ↦* dq  vs").

Global Arguments own_slice_cap {_ _ _ _ _} (V) {_ _ _} (s).

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Lemma wp_slice_len stk E (s : slice.t) (Φ : val -> iProp Σ) :
    Φ #(s.(slice.len_f)) -∗ WP slice.len (#s) @ stk; E {{ v, Φ v }}.
Proof.
  rewrite to_val_unseal. iIntros "HΦ".
  wp_call. rewrite to_val_unseal. iApply "HΦ".
Qed.

Lemma wp_slice_cap stk E (s : slice.t) (Φ : val -> iProp Σ) :
    Φ #(s.(slice.cap_f)) -∗ WP slice.cap (#s) @ stk; E {{ v, Φ v }}.
Proof.
  rewrite to_val_unseal. iIntros "HΦ".
  wp_call. rewrite to_val_unseal. iApply "HΦ".
Qed.

Lemma slice_val_fold (ptr: loc) (sz: u64) (cap: u64) :
  InjLV (#ptr, #sz, #cap)%V = #(slice.mk ptr sz cap).
Proof. repeat rewrite to_val_unseal //=. Qed.

Lemma seq_replicate_fmap {A} y n (a : A) :
  (λ _, a) <$> seq y n = replicate n a.
Proof.
  revert y. induction n.
  { done. }
  { simpl. intros. f_equal. by erewrite IHn. }
Qed.

Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.

Lemma wp_slice_make3 stk E (len cap : w64) :
  uint.nat len ≤ uint.nat cap →
  {{{ True }}}
    slice.make3 t #len #cap @ stk; E
  {{{ sl, RET #sl;
      sl ↦* (replicate (uint.nat len) (default_val V)) ∗
      own_slice_cap V sl ∗
      ⌜ sl.(slice.cap_f) = cap ⌝
  }}}.
Proof.
  iIntros (? Φ) "_ HΦ".
  wp_call.

  destruct bool_decide eqn:Hlt;
    [apply bool_decide_eq_true_1 in Hlt|apply bool_decide_eq_false_1 in Hlt];
    wp_pures.
  { exfalso. word. }

  destruct bool_decide eqn:Hlt2;
    [apply bool_decide_eq_true_1 in Hlt2|apply bool_decide_eq_false_1 in Hlt2];
    wp_pures.
  {
    wp_bind ArbitraryInt.
    iApply (wp_ArbitraryInt with "[//]"). iNext.
    iIntros (?) "_".
    replace (LitV x) with (#x).
    2:{ rewrite to_val_unseal //. }
    wp_pures.
    rewrite slice_val_fold.
    iApply "HΦ".
    rewrite own_slice_unseal own_slice_cap_unseal.
    assert (len = W64 0) by word; subst.
    unfold own_slice_def. unfold own_slice_cap_def. simpl.
    assert (uint.nat (W64 0) = 0)%nat as -> by word.
    simpl. done.
  }
  wp_pures.
  wp_bind (AllocN _ _).
  rewrite [in #cap]to_val_unseal.
  iApply (wp_allocN_seq with "[//]").
  { word. }
  iNext.
  iIntros (?) "Hp".
  wp_pures.
  replace (LitV l) with (#l); last by rewrite to_val_unseal //.
  replace (LitV cap) with (#cap); last by rewrite to_val_unseal //.
  rewrite slice_val_fold. iApply "HΦ".
  rewrite own_slice_unseal own_slice_cap_unseal.
  assert (uint.nat cap = uint.nat len + (uint.nat cap - uint.nat len))%nat as Hsplit by word.
  rewrite Hsplit seq_app.
  iDestruct "Hp" as "[Hsl Hcap]".
  iSplitL "Hsl".
  {
    iSplitL.
    2:{ iPureIntro. simpl. rewrite length_replicate. word. }
    erewrite <- (seq_replicate_fmap O).
    iApply (big_sepL_fmap with "[Hsl]").
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros.
    rewrite /pointsto_vals typed_pointsto_unseal /typed_pointsto_def /=.
    rewrite default_val_eq_zero_val.
    erewrite has_go_type_len.
    2:{ apply zero_val_has_go_type. }
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros. iFrame.
    apply lookup_seq in H0 as [? ?].
    subst. iFrame.
  }
  {
    iSplitL.
    2:{ iPureIntro. done. }
    rewrite /own_slice_cap_def /=.
    iSplitR; first iPureIntro.
    { word. }
    rewrite default_val_eq_zero_val.
    erewrite has_go_type_len.
    2:{ apply zero_val_has_go_type. }
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros.
    rewrite /pointsto_vals typed_pointsto_unseal /typed_pointsto_def /=.
    rewrite default_val_eq_zero_val.
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros. iFrame.
  }
Qed.

Lemma wp_slice_make2 stk E (len : u64) :
  {{{ True }}}
    slice.make2 t #len @ stk; E
  {{{ sl, RET #sl;
      sl ↦* (replicate (uint.nat len) (default_val V)) ∗
      own_slice_cap V sl
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply wp_slice_make3.
  { done. }
  iIntros (?) "(? & ? & ?)".
  iApply "HΦ". iFrame.
Qed.

Global Instance pure_slice_ptr (s : slice.t) :
  PureWp True (slice.ptr (#s)) #(slice.ptr_f s).
Proof.
  rewrite to_val_unseal.
  iIntros (?????) "HΦ".
  wp_call_lc "?". rewrite to_val_unseal.
  by iApply "HΦ".
Qed.

Global Instance pure_slice_len (s : slice.t) :
  PureWp True (slice.len (#s)) #(slice.len_f s).
Proof.
  rewrite to_val_unseal.
  iIntros (?????) "HΦ".
  wp_call_lc "?". rewrite to_val_unseal. by iApply "HΦ".
Qed.

Global Instance pure_slice_cap (s : slice.t) :
  PureWp True (slice.cap (#s)) #(slice.cap_f s).
Proof.
  rewrite to_val_unseal.
  iIntros (?????) "HΦ".
  wp_call_lc "?". rewrite to_val_unseal. by iApply "HΦ".
Qed.

Global Instance wp_slice_elem_ref s (i : w64) :
  PureWp (uint.Z i < uint.Z s.(slice.len_f)) (slice.elem_ref t #s #i)
    #(slice.elem_ref_f s t i).
Proof.
  iIntros (?????) "HΦ".
  wp_call.
  rewrite bool_decide_true; last done.
  wp_pure_lc "?". wp_pures. by iApply "HΦ".
Qed.

Lemma wp_slice_for_range {stk E} sl dq (vs : list V) (body : val) Φ :
  sl ↦*{dq} vs -∗
  (fold_right (λ v P (i : w64),
                 WP body #i #v @ stk ; E {{ v', ⌜ v' = execute_val #()%V ⌝ ∗ P (word.add i 1) }})
    (λ (_ : w64), sl ↦*{dq} vs -∗ Φ (execute_val #()))
    vs) (W64 0) -∗
  WP slice.for_range t #sl body @ stk ; E {{ Φ }}
.
Proof.
  iIntros "Hsl HΦ".
  wp_call.
  wp_apply wp_ref_ty.
  iIntros (j_ptr) "Hi".
  wp_pures.
  iAssert (
      ∃ (j : u64),
        "Hi" ∷ j_ptr ↦ j ∗
        "Hiters" ∷ (fold_right _ _ (drop (uint.nat j) vs)) j
    )%I with "[Hi HΦ]" as "Hinv".
  { iExists (W64 0). iFrame. }
  wp_for "Hinv".
  iDestruct (own_slice_len with "Hsl") as %Hlen.
  case_bool_decide as Hlt.
  - (* Case: execute loop body *)
    wp_pures.
    wp_load.
    wp_pures.
    pose proof (list_lookup_lt vs (uint.nat j) ltac:(word)) as [w Hlookup].
    iDestruct (own_slice_elem_acc with "[$]") as "[Helem Hown]"; [eassumption|].
    wp_load.
    iDestruct ("Hown" with "Helem") as "Hown".
    rewrite list_insert_id; [|assumption].
    wp_load.
    erewrite drop_S; last eassumption.
    simpl.
    wp_apply (wp_wand with "Hiters").
    iIntros (?) "[-> Hiters]".
    iApply wp_for_post_do.
    wp_pures.
    wp_load.
    wp_pures.
    wp_store. wp_pures.
    iFrame.
    replace (uint.nat (word.add _ $ W64 1)) with (S $ uint.nat j) by word.
    iFrame.
  - simpl.  (* Case: done with loop body. *)
    rewrite drop_ge.
    2:{ word. }
    iApply "Hiters". by iFrame.
Qed.

Lemma wp_slice_literal {stk E} (l : list V) :
  {{{ True }}}
    slice.literal t #l @ stk ; E
  {{{ sl, RET #sl; sl ↦* l }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply wp_list_Length.
  iIntros "%Hlen".
  wp_pures.
  wp_apply wp_slice_make2.
  iIntros (?) "[Hsl Hcap]".
  wp_pures.
  wp_bind (ref _)%E.
  iApply (wp_alloc_untyped with "[//]").
  { instantiate (1:=#l). rewrite to_val_unseal /=. by destruct l. }
  iNext. iIntros (l_ptr) "Hl".
  wp_pures.
  wp_alloc i_ptr as "Hi".
  wp_pures.
  iDestruct (own_slice_len with "Hsl") as %Hsz.
  rewrite length_replicate in Hsz.
  iAssert (∃ (i : w64),
      "%Hi" ∷ ⌜ uint.Z i <= uint.Z (W64 (length l)) ⌝ ∗
      "Hi" ∷ i_ptr ↦ i ∗
      "Hl" ∷ heap_pointsto l_ptr (DfracOwn 1) (# (drop (uint.nat i) l)) ∗
      "Hsl" ∷ sl ↦* (take (uint.nat i) l ++ replicate (length l - uint.nat i) (default_val V))
    )%I
    with "[Hi Hl Hsl]" as "Hloop".
  {
    iExists _; iFrame.
    autorewrite with list in *.
    simpl.
    rewrite drop_0 take_0 Nat.sub_0_r -Hlen /=.
    iFrame. word.
  }
  wp_for.
  iNamed "Hloop".
  wp_pures.
  wp_load.
  wp_pures.
  autorewrite with list in *.
  case_bool_decide as Hlt.
  {
    simpl.
    rewrite decide_True //.
    wp_pures.
    wp_bind (! _)%E.
    iApply (wp_load with "[$]").
    iNext. iIntros "Hl".
    wp_pures.
    destruct (drop _ _) eqn:Hdrop.
    { exfalso. apply (f_equal length) in Hdrop.
      rewrite length_drop /= in Hdrop.
      autorewrite with list in *. word. }
    simpl.
    wp_pures.
    wp_apply (wp_store with "[$]").
    iIntros "Hl".
    wp_pures.
    wp_load.
    autorewrite with list in *.
    apply Z2Nat.inj in Hsz. 2-3: word.
    rewrite Hsz in Hlt.
    wp_pure.
    iDestruct (own_slice_elem_acc i with "Hsl") as "[Hptsto Hsl]".
    {
      rewrite lookup_app_r.
      2:{ rewrite length_take. word. }
      rewrite length_take.
      rewrite lookup_replicate.
      split; first done.
      word.
    }
    wp_store.
    wp_pures.
    iApply wp_for_post_do.
    wp_pures.
    wp_load.
    wp_pures.
    wp_store. wp_pures.
    iFrame.
    replace (uint.nat (word.add i (W64 1))) with (uint.nat i + 1)%nat by word.
    rewrite -drop_drop.
    rewrite Hdrop.
    rewrite /= drop_0.
    iFrame.
    iSpecialize ("Hsl" with "Hptsto").
    iSplitR.
    { word. }
    iApply to_named.
    iExactEq "Hsl".
    repeat f_equal.
    rewrite insert_app_r_alt.
    2:{ rewrite length_take. word. }
    rewrite take_more.
    2:{ word. }
    rewrite -app_assoc.
    f_equal.
    rewrite insert_replicate_lt.
    2:{ rewrite length_take. word. }
    rewrite length_take.
    rewrite Nat.min_l.
    2:{ word. }
    rewrite Nat.sub_diag Hdrop.
    simpl.
    f_equal.
    f_equal.
    word.
  }
  {
    simpl.
    rewrite decide_False; last naive_solver.
    rewrite decide_True; last naive_solver.
    wp_pures.
    iApply "HΦ".
    replace (uint.Z i) with (uint.Z (length l)).
    2:{ word. }
    rewrite -Hlen Nat.sub_diag.
    rewrite replicate_0 app_nil_r firstn_all. iFrame.
  }
Qed.

Global Instance points_to_access_slice_elem_ref s (i : w64) (vs : list V) dq v
  {Hlookup : TCSimpl (vs !! (uint.nat i)) (Some v)}
  : PointsToAccess (slice.elem_ref_f s t i) v dq (s ↦*{dq} vs)
      (λ v', s ↦*{dq} <[(uint.nat i) := v']> vs).
Proof.
  constructor.
  - inv Hlookup.
    iIntros "Hs".
    iDestruct (own_slice_elem_acc with "Hs") as "Hs"; eauto.
  - inv Hlookup.
    rewrite list_insert_id //.
Qed.

Lemma wp_load_slice_elem s (i: w64) (vs: list V) dq v :
  {{{ s ↦*{dq} vs ∗ ⌜vs !! (uint.nat i) = Some v⌝ }}}
    ![t] #(slice.elem_ref_f s t i)
  {{{ RET #v; s ↦*{dq} vs }}}.
Proof.
  iIntros (Φ) "[Hs %Hlookup] HΦ".
  iDestruct (own_slice_elem_acc with "Hs") as "[Hv Hs]"; [ by eauto | ].
  (* NOTE: cannot use [wp_load] because we need to strip a later *)
  wp_apply (wp_load_ty with "Hv"). iIntros "Hv".
  iApply "HΦ".
  iDestruct ("Hs" with "Hv") as "Hs".
  rewrite -> list_insert_id by auto.
  iFrame.
Qed.

Lemma wp_store_slice_elem s (i: w64) (vs: list V) (v': V) :
  {{{ s ↦* vs ∗ ⌜uint.Z i < Z.of_nat (length vs)⌝ }}}
    store_ty t #(slice.elem_ref_f s t i) #v'
  {{{ RET #(); s ↦* (<[uint.nat i := v']> vs) }}}.
Proof.
  iIntros (Φ) "[Hs %bound] HΦ".
  list_elem vs i as v.
  iDestruct (own_slice_elem_acc with "Hs") as "[Hv Hs]"; [ by eauto | ].
  (* NOTE: cannot use [wp_store] because we need to strip a later *)
  wp_apply (wp_store_ty with "Hv"). iIntros "Hv".
  iApply "HΦ".
  iDestruct ("Hs" with "Hv") as "Hs".
  iFrame.
Qed.

End wps.

Notation "s ↦* dq vs" := (own_slice s dq vs)
                            (at level 20, dq custom dfrac at level 50,
                              vs constr at next level, format "s  ↦* dq  vs").
