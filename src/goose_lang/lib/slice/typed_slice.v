From Perennial.goose_lang Require Import notation proofmode typing.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Import slice.impl.
From Perennial.goose_lang.lib Require Import slice.slice.
From Perennial.goose_lang.lib Require Import into_val.

From iris_string_ident Require Import ltac2_string_ident.

Set Default Proof Using "Type".

Module list.
  Definition untype `{IntoVal V}:
    list V -> list val := fun l => to_val <$> l.
End list.

Lemma list_untype_length `{IntoVal V} (l: list V) :
  length (list.untype l) = length l.
Proof.
  rewrite /list.untype fmap_length //.
Qed.

Hint Rewrite @list_untype_length : len.

Section heap.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
Context {ext_ty: ext_types ext}.

Context `{!IntoVal V}.

Implicit Types (s:Slice.t) (vs: list V) (v:V).
Implicit Types (t:ty).

Definition is_slice s t q vs := slice.is_slice s t q (list.untype vs).
Definition is_slice_small s t q vs := slice.is_slice_small s t q (list.untype vs).

Lemma is_slice_small_acc s t q vs :
  is_slice s t q vs -∗ is_slice_small s t q vs ∗ (∀ vs', is_slice_small s t q vs' -∗ is_slice s t q vs').
Proof.
  iIntros "Hs".
  iDestruct (slice.is_slice_small_acc with "Hs") as "[$ Hs]".
  iIntros (vs') "Hsmall".
  iApply ("Hs" with "[$]").
Qed.

Lemma is_slice_small_read s t q vs :
  is_slice s t q vs -∗ is_slice_small s t q vs ∗ (is_slice_small s t q vs -∗ is_slice s t q vs).
Proof.
  iIntros "Hs".
  iDestruct (slice.is_slice_small_read with "Hs") as "[$ Hs]".
  iIntros "Hsmall".
  iApply ("Hs" with "[$]").
Qed.

Lemma untype_replicate n x :
  list.untype (replicate n x) = replicate n (to_val x).
Proof.
  rewrite /list.untype fmap_replicate //.
Qed.

Lemma is_slice_to_small s t q vs :
  is_slice s t q vs -∗ is_slice_small s t q vs.
Proof.
  rewrite /is_slice /is_slice_small.
  iIntros "Hs".
  iDestruct (slice.is_slice_to_small with "Hs") as "Hs".
  done.
Qed.

Theorem is_slice_zero t q :
  ⊢ is_slice Slice.nil t q [].
Proof.
  rewrite /is_slice /=.
  iApply slice.is_slice_zero.
Qed.

Theorem is_slice_small_nil t q s :
  int.val s.(Slice.sz) = 0 ->
  ⊢ is_slice_small s t q [].
Proof.
  intros Hsz.
  rewrite /is_slice_small /=.
  iApply slice.is_slice_small_nil; auto.
Qed.

Lemma wp_NewSlice stk E t `{!IntoValForType IntoVal0 t} (sz: u64) :
  {{{ True }}}
    NewSlice t #sz @ stk; E
  {{{ s, RET slice_val s; is_slice s t 1 (replicate (int.nat sz) IntoVal_def) }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_apply slice.wp_new_slice.
  { apply to_val_has_zero. }
  iIntros (s) "Hs".
  iApply "HΦ".
  rewrite /is_slice.
  rewrite untype_replicate.
  rewrite def_is_zero.
  iApply "Hs".
Qed.

Lemma wp_SliceGet stk E s t q vs (i: u64) v0 :
  {{{ is_slice_small s t q vs ∗ ⌜ vs !! int.nat i = Some v0 ⌝ }}}
    SliceGet t (slice_val s) #i @ stk; E
  {{{ RET to_val v0; is_slice_small s t q vs }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  iApply (slice.wp_SliceGet with "[$Hs]").
  { iPureIntro.
    rewrite /list.untype list_lookup_fmap.
    rewrite H; eauto. }
  iIntros "!> [Hs _]".
  iApply ("HΦ" with "[$]").
Qed.

Lemma wp_SliceAppend' stk E s t `{!IntoValForType IntoVal0 t} vs (x: V) :
  {{{ is_slice s t 1 vs }}}
    SliceAppend t (slice_val s) (to_val x) @ stk; E
  {{{ s', RET slice_val s'; is_slice s' t 1 (vs ++ [x]) }}}.
Proof.
  iIntros (Φ) "Hs HΦ".
  wp_apply (slice.wp_SliceAppend' with "Hs").
  { apply to_val_has_zero. }
  { apply to_val_ty. }
  iIntros (s') "Hs".
  rewrite /list.untype.
  change [to_val x] with (to_val <$> [x]).
  rewrite -fmap_app.
  iApply ("HΦ" with "Hs").
Qed.

Lemma wp_SliceAppend stk E s t `{!IntoValForType IntoVal0 t} vs (x: V) :
  {{{ is_slice s t 1 vs ∗ ⌜int.val s.(Slice.sz) + 1 < 2^64⌝ }}}
    SliceAppend t (slice_val s) (to_val x) @ stk; E
  {{{ s', RET slice_val s'; is_slice s' t 1 (vs ++ [x]) }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  wp_apply (wp_SliceAppend' with "Hs"); auto.
Qed.

Lemma wp_SliceAppend_to_zero stk E t `{!IntoValForType IntoVal0 t} v (x: val) :
  x = to_val v ->
  {{{ True }}}
    SliceAppend t (zero_val (slice.T t)) x @ stk; E
  {{{ s', RET slice_val s'; is_slice s' t 1 [v] }}}.
Proof.
  intros ->.
  iIntros (Φ) "_ HΦ".
  wp_apply slice.wp_SliceAppend_to_zero.
  { apply to_val_ty. }
  { apply to_val_has_zero. }
  iIntros (s') "Hs".
  iApply ("HΦ" with "Hs").
Qed.

Theorem untype_lookup_Some vs (i: nat) (x: val) :
  list.untype vs !! i = Some x ->
  ∃ (v:V), vs !! i = Some v ∧ x = to_val v.
Proof.
  rewrite /list.untype list_lookup_fmap.
  intros [v [Hlookup ->]]%fmap_Some_1.
  eauto.
Qed.

Theorem wp_forSlice (I: u64 -> iProp Σ) stk E s t q vs (body: val) :
  (∀ (i: u64) (x: V),
      {{{ I i ∗ ⌜int.val i < int.val s.(Slice.sz)⌝ ∗
                ⌜vs !! int.nat i = Some x⌝ }}}
        body #i (to_val x) @ stk; E
      {{{ RET #(); I (word.add i (U64 1)) }}}) -∗
    {{{ I (U64 0) ∗ is_slice_small s t q vs }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); I s.(Slice.sz) ∗ is_slice_small s t q vs }}}.
Proof.
  iIntros "#Hbody".
  iIntros "!>" (Φ) "[HI Hs] HΦ".
  wp_apply (slice.wp_forSlice I with "[] [$HI $Hs]").
  { clear.
    iIntros (i x).
    iIntros "!>" (Φ) "[HI [% %Hlookup]] HΦ".
    apply untype_lookup_Some in Hlookup as [v [Hlookup ->]].
    wp_apply ("Hbody" with "[$HI //]").
    iApply "HΦ". }
  iApply "HΦ".
Qed.

Theorem wp_forSlicePrefix (P: list V -> list V -> iProp Σ) stk E s t q vs (body: val) :
  (∀ (i: u64) (x: V) (vs: list V) (vs': list V),
      {{{ P vs (x :: vs') }}}
        body #i (to_val x) @ stk; E
      {{{ RET #(); P (vs ++ [x]) vs' }}}) -∗
    {{{ is_slice_small s t q vs ∗ P nil vs }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); is_slice_small s t q vs ∗ P vs nil }}}.
Proof.
  iIntros "#Hind".
  iIntros (Φ) "!> [Hs Hi0] HΦ".
  iApply (wp_forSlice (λ i, P (take (int.nat i) vs) (drop (int.nat i) vs))
    with "[] [$Hs $Hi0]").
  {
    iIntros (i x). iModIntro.
    iIntros (Φ0) "(HP & % & %) HΦ0".
    wp_apply ("Hind" with "[HP]").
    { eapply drop_S in H0. rewrite H0. iFrame. }
    iIntros "HP".
    iApply "HΦ0".
    iExactEq "HP". f_equal.
    { apply take_S_r in H0. rewrite -H0. f_equal. word. }
    f_equal. word.
  }

  iModIntro. iIntros "[HP Hs]".
  iDestruct (is_slice_small_sz with "Hs") as %<-.
  iApply "HΦ". iFrame.
  rewrite /list.untype fmap_length.
  rewrite firstn_all.
  rewrite drop_all. done.
Qed.

End heap.
