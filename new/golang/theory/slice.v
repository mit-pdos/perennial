From RecordUpdate Require Import RecordSet.
From Perennial.Helpers Require Import List Fractional.
From iris.algebra Require Import dfrac.
From Perennial.goose_lang Require Import proofmode.
From New.golang.defn Require Export slice.
From New.golang.theory Require Export mem typing exception.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Module slice.
Definition slice_f (sl : slice.t) (t : go_type) (n1 n2 : u64) : slice.t :=
  slice.mk (sl.(slice.ptr_f) +ₗ[t] uint.Z n1) (word.sub n2 n1) (word.sub sl.(slice.cap_f) n1).
End slice.

Section defns_and_lemmas.
Context `{heapGS Σ}.
Definition own_slice_def (s : slice.t) (t : go_type) (dq : dfrac) (vs : list val): iProp Σ :=
  ([∗ list] i ↦ v ∈ vs, (s.(slice.ptr_f) +ₗ[t] i) ↦[t]{dq} v ) ∗
  ⌜length vs = uint.nat s.(slice.len_f) ∧ uint.Z s.(slice.len_f) ≤ uint.Z s.(slice.cap_f)⌝.
Program Definition own_slice := unseal (_:seal (@own_slice_def)). Obligation 1. by eexists. Qed.
Definition own_slice_unseal : own_slice = _ := seal_eq _.

Definition own_slice_cap_def (s : slice.t) (t : go_type): iProp Σ :=
  ⌜ uint.Z s.(slice.len_f) ≤ uint.Z s.(slice.cap_f) ⌝ ∗
  [∗ list] i ∈ (seq (uint.nat s.(slice.len_f)) (uint.nat s.(slice.cap_f) - uint.nat s.(slice.len_f))),
    (s.(slice.ptr_f) +ₗ[t] Z.of_nat i) ↦[t] (zero_val t).
Program Definition own_slice_cap := unseal (_:seal (@own_slice_cap_def)). Obligation 1. by eexists. Qed.
Definition own_slice_cap_unseal : own_slice_cap = _ := seal_eq _.

Ltac unseal := rewrite ?own_slice_unseal /own_slice_def
                 ?own_slice_cap_unseal /own_slice_cap_def.

Lemma own_slice_cap_none s t :
  s.(slice.len_f) = s.(slice.cap_f) →
  ⊢ own_slice_cap s t.
Proof.
  destruct s; simpl; intros ->. rewrite own_slice_cap_unseal /own_slice_cap_def Nat.sub_diag //.
  simpl. iPureIntro. lia.
Qed.

Lemma own_slice_sz s t q vs :
  own_slice s t q vs -∗ ⌜length vs = uint.nat s.(slice.len_f)⌝.
Proof.
  unseal. iIntros "(_&[%%]) !% //".
Qed.

Lemma replicate_0 A (x:A) : replicate 0 x = [].
Proof. reflexivity. Qed.

Instance own_slice_fractional s t vs :
  fractional.Fractional (λ q, own_slice s t (DfracOwn q) vs).
Proof. unseal; apply _. Qed.

Instance own_slice_as_fractional s q t vs :
  fractional.AsFractional (own_slice s t (DfracOwn q) vs) (λ q, own_slice s t (DfracOwn q) vs) q.
Proof. unseal; split; auto; apply _. Qed.

Lemma loc_add_stride_Sn l t n :
  l +ₗ[t] S n = (l +ₗ go_type_size t) +ₗ[t] n.
Proof.
  replace (Z.mul (go_type_size t) (S n)) with (go_type_size t + Z.mul (go_type_size t) n).
  { rewrite loc_add_assoc //. }
  replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
  rewrite Z.mul_add_distr_l.
  f_equal.
  rewrite Z.mul_1_r //.
Qed.

Lemma own_slice_agree s t q1 q2 vs1 vs2 :
  own_slice s t q1 vs1 -∗
  own_slice s t q2 vs2 -∗
  ⌜vs1 = vs2⌝.
Proof.
  unseal.
  iIntros "[Hs1 [%%]] [Hs2 [%%]]".
  assert (length vs1 = length vs2) by congruence.
  generalize (slice.ptr_f s). intros l.
  assert (length vs1 = length vs2) as Hlen by done.
  clear -Hlen.
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

Global Instance own_slice_persistent s t vs : Persistent (own_slice s t DfracDiscarded vs).
Proof. unseal; apply _. Qed.

Lemma own_slice_persist s t dq vs:
  own_slice s t dq vs ==∗ own_slice s t DfracDiscarded vs.
Proof.
  unseal.
  iIntros "[Hs %Hl]".
  iSplitL; last done.
  iApply big_sepL_bupd.
  iApply (big_sepL_impl with "Hs").
  iModIntro. iIntros "* % ?".
  iApply (typed_pointsto_persist with "[$]").
Qed.

Global Instance own_slice_timeless s t q vs : Timeless (own_slice s t q vs).
Proof. unseal; apply _. Qed.

Lemma own_slice_not_null s t q vs :
  go_type_size t > 0 →
  length vs > 0 ->
  own_slice s t q vs -∗
  ⌜ s.(slice.ptr_f) ≠ null ⌝.
Proof.
  unseal.
  iIntros (Hbt Hvs) "[Hs %]".
  destruct s; destruct vs; simpl in *; try lia.
  iDestruct "Hs" as "[Hptr _]".
  rewrite Z.mul_0_r loc_add_0.
  by iApply typed_pointsto_not_null.
Qed.

Lemma own_slice_cap_wf s t :
  own_slice_cap s t -∗ ⌜uint.Z s.(slice.len_f) ≤ uint.Z s.(slice.cap_f)⌝.
Proof.
  unseal. by iIntros "[% Hcap]".
Qed.

Lemma own_slice_wf s t q vs :
  own_slice s t q vs -∗ ⌜uint.Z s.(slice.len_f) ≤ uint.Z s.(slice.cap_f)⌝.
Proof.
  unseal.
  iIntros "[? %]". naive_solver.
Qed.

Lemma own_slice_nil t q :
  ⊢ own_slice slice.nil_f t q [].
Proof.
  unseal. simpl. iPureIntro. split_and!; done.
Qed.

Lemma own_slice_empty t q s :
  uint.Z s.(slice.len_f) = 0 ->
  ⊢ own_slice s t q [].
Proof.
  unseal. intros Hsz. destruct s. simpl in *.
  iPureIntro. split_and!; [done|word|word].
Qed.

Lemma own_slice_cap_nil t :
  ⊢ own_slice_cap slice.nil_f t.
Proof.
  unseal. simpl. rewrite right_id.
  rewrite (nil_length_inv (seq _ _)).
  2:{ rewrite length_seq. word. }
  simpl. iPureIntro. word.
Qed.

End defns_and_lemmas.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Lemma wp_slice_len stk E (s : slice.t) (Φ : val -> iProp Σ) :
    Φ #(s.(slice.len_f)) -∗ WP slice.len (slice.val s) @ stk; E {{ v, Φ v }}.
Proof.
  rewrite slice.val_unseal. iIntros "HΦ".
  wp_rec. wp_pures.
  iApply "HΦ".
Qed.

Lemma wp_slice_cap stk E (s : slice.t) (Φ : val -> iProp Σ) :
    Φ #(s.(slice.cap_f)) -∗ WP slice.cap (slice.val s) @ stk; E {{ v, Φ v }}.
Proof.
  rewrite slice.val_unseal. iIntros "HΦ".
  wp_rec. wp_pures.
  iApply "HΦ".
Qed.

Lemma slice_val_fold (ptr: loc) (sz: u64) (cap: u64) :
  InjLV (#ptr, #sz, #cap)%V = slice.val (slice.mk ptr sz cap).
Proof. rewrite slice.val_unseal. done. Qed.

Lemma seq_replicate_fmap {A} y n (a : A) :
  (λ _, a) <$> seq y n = replicate n a.
Proof.
  revert y. induction n.
  { done. }
  { simpl. intros. f_equal. by erewrite IHn. }
Qed.

Lemma wp_slice_make3 stk E t (len cap : u64) :
  uint.nat len ≤ uint.nat cap →
  {{{ True }}}
    slice.make3 t #len #cap @ stk; E
  {{{ sl, RET slice.val sl;
      own_slice sl t (DfracOwn 1) (replicate (uint.nat len) (zero_val t)) ∗
      own_slice_cap sl t ∗
      ⌜ sl.(slice.cap_f) = cap ⌝
  }}}.
Proof.
  iIntros (? Φ) "_ HΦ".
  wp_rec. wp_pures.
  wp_if_destruct.
  { exfalso. word. }
  wp_pures.
  wp_if_destruct.
  {
    wp_apply wp_ArbitraryInt.
    iIntros (?) "_".
    wp_pures.
    rewrite slice_val_fold.
    iApply "HΦ".
    iModIntro.
    rewrite own_slice_unseal own_slice_cap_unseal.
    assert (len = W64 0); subst.
    {
      assert (uint.Z (W64 0) = uint.Z len ∨ uint.Z (W64 0) < uint.Z len) as [|] by word; try word.
      apply word.unsigned_inj. done.
    }
    unfold own_slice_def. unfold own_slice_cap_def. simpl.
    assert (uint.nat (W64 0) = 0)%nat as -> by word.
    simpl. done.
  }
  wp_pures.
  wp_apply wp_allocN_seq.
  { (* FIXME(word): tedious *)
    destruct (decide (uint.Z cap = 0)).
    - subst. exfalso. assert (cap = W64 0) by word. congruence.
    - word.
  }
  iIntros (?) "Hp".
  wp_pures.
  rewrite slice_val_fold. iApply "HΦ".
  rewrite own_slice_unseal own_slice_cap_unseal.
  assert (uint.nat cap = uint.nat len + (uint.nat cap - uint.nat len))%nat as Hsplit by word.
  rewrite Hsplit seq_app.
  iDestruct "Hp" as "[Hsl Hcap]".
  iSplitL "Hsl".
  {
    iModIntro. iSplitL.
    2:{ iPureIntro. simpl. rewrite length_replicate. word. }
    erewrite <- (seq_replicate_fmap O).
    iApply (big_sepL_fmap with "[Hsl]").
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros.
    rewrite /pointsto_vals typed_pointsto_unseal /typed_pointsto_def /=.
    erewrite has_go_type_len.
    2:{ apply zero_val_has_go_type. }
    iSplitL.
    2:{ iPureIntro. apply zero_val_has_go_type. }
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros. iFrame.
    apply lookup_seq in H0 as [? ?].
    subst. iFrame.
  }
  {
    iModIntro. iSplitL.
    2:{ iPureIntro. done. }
    rewrite /own_slice_cap_def /=.
    iSplitR; first iPureIntro.
    { word. }
    erewrite has_go_type_len.
    2:{ apply zero_val_has_go_type. }
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros.
    rewrite /pointsto_vals typed_pointsto_unseal /typed_pointsto_def /=.
    iSplitL.
    2:{ iPureIntro. apply zero_val_has_go_type. }
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros. iFrame.
  }
Qed.

Lemma wp_slice_make2 stk E t (len : u64) :
  {{{ True }}}
    slice.make2 t #len @ stk; E
  {{{ sl, RET slice.val sl;
      own_slice sl t (DfracOwn 1) (replicate (uint.nat len) (zero_val t)) ∗
      own_slice_cap sl t
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec. wp_pures.
  wp_apply wp_slice_make3.
  { done. }
  iIntros (?) "(? & ? & ?)".
  iApply "HΦ". iFrame.
Qed.

(* PureExecs *)

Global Instance pure_slice_ptr (s : slice.t) :
  PureWpVal True (slice.ptr (slice.val s)) #(slice.ptr_f s).
Proof.
  rewrite slice.val_unseal.
  iIntros (???) "_ HΦ".
  wp_rec. wp_pures. by iApply "HΦ".
Qed.

Global Instance pure_slice_len (s : slice.t) :
  PureWpVal True (slice.len (slice.val s)) #(slice.len_f s).
Proof.
  rewrite slice.val_unseal.
  iIntros (???) "_ HΦ".
  wp_rec. wp_pures. by iApply "HΦ".
Qed.

Global Instance pure_slice_cap (s : slice.t) :
  PureWpVal True (slice.cap (slice.val s)) #(slice.cap_f s).
Proof.
  rewrite slice.val_unseal.
  iIntros (???) "_ HΦ".
  wp_rec. wp_pures. by iApply "HΦ".
Qed.

End wps.
