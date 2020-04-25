From Perennial.goose_lang Require Import notation proofmode typing.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Import slice.impl.
From Perennial.goose_lang.lib Require Import slice.slice.
From Perennial.goose_lang.lib Require Import into_val.

From iris_string_ident Require Import ltac2_string_ident.

Module list.
  Definition untype `{IntoVal V}:
    list V -> list val := fun l => to_val <$> l.
End list.

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

Lemma wp_SliceAppend stk E s t `{!IntoValForType IntoVal0 t} vs (x: V) :
  {{{ is_slice s t 1 vs ∗ ⌜int.val s.(Slice.sz) + 1 < 2^64⌝ }}}
    SliceAppend t (slice_val s) (to_val x) @ stk; E
  {{{ s', RET slice_val s'; is_slice s' t 1 (vs ++ [x]) }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  wp_apply (slice.wp_SliceAppend with "[$Hs]").
  { apply to_val_has_zero. }
  { iSplit; first by auto.
    iPureIntro.
    apply to_val_ty. }
  iIntros (s') "Hs".
  rewrite /list.untype.
  change [to_val x] with (to_val <$> [x]).
  rewrite -fmap_app.
  iApply ("HΦ" with "Hs").
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
  iIntros "#Hbody".
  iIntros "!>" (Φ) "[Hs HP] HΦ".
  wp_apply (wp_forSlicePrefix
              (λ l1 l2, ∃ vs1 vs2,
                  ⌜l1 = list.untype vs1 ∧ l2 = list.untype vs2⌝ ∗
                  P vs1 vs2) with "[] [$Hs HP]")%I.
  { clear.
    iIntros (i x vs vs').
    iIntros "!>" (Φ) "HP HΦ".
    iDestruct "HP" as (vs1 vs2 [-> Heq2]) "HP".
    admit.
  }
Admitted.

End heap.
