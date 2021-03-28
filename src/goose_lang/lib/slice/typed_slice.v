From Perennial.Helpers Require Import List.
From Perennial.goose_lang Require Import notation proofmode typing.
From Perennial.goose_lang.lib Require Import typed_mem persistent_readonly.
From Perennial.goose_lang.lib Require Import slice.impl slice.slice.
From Perennial.goose_lang.lib Require Import into_val.


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

Lemma is_slice_small_sz s t q vs :
  is_slice_small s t q vs -∗ ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof.
  iIntros "(_&%) !%".
  rewrite fmap_length // in H.
Qed.

Lemma is_slice_to_small s t q vs :
  is_slice s t q vs -∗ is_slice_small s t q vs.
Proof.
  rewrite /is_slice /is_slice_small.
  iIntros "Hs".
  iDestruct (slice.is_slice_to_small with "Hs") as "Hs".
  done.
Qed.

Lemma is_slice_sz s t q vs :
  is_slice s t q vs -∗ ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof.
  rewrite is_slice_to_small is_slice_small_sz //.
Qed.

Theorem is_slice_zero t q :
  ⊢ is_slice Slice.nil t q [].
Proof.
  rewrite /is_slice /=.
  iApply slice.is_slice_zero.
Qed.

Theorem is_slice_small_nil t q s :
  int.Z s.(Slice.sz) = 0 ->
  ⊢ is_slice_small s t q [].
Proof.
  intros Hsz.
  rewrite /is_slice_small /=.
  iApply slice.is_slice_small_nil; auto.
Qed.

Lemma slice_small_split s (n: u64) t q vs :
  int.Z n <= length vs →
  is_slice_small s t q vs -∗ is_slice_small (slice_take s t n) t q (take (int.nat n) vs) ∗
           is_slice_small (slice_skip s t n) t q (drop (int.nat n) vs).
Proof.
  iIntros (Hbounds) "Hs".
  rewrite /is_slice_small.
  iDestruct (slice.slice_small_split with "Hs") as "[Hs1 Hs2]".
  { rewrite fmap_length //. }
  rewrite -fmap_take -fmap_drop.
  iFrame.
Qed.

Theorem is_slice_small_take_drop s t q n vs :
  (int.nat n <= int.nat s.(Slice.sz))%nat ->
  is_slice_small (slice_skip s t n) t q (drop (int.nat n) vs) ∗
  is_slice_small (slice_take s t n) t q (take (int.nat n) vs) ⊣⊢
  is_slice_small s t q vs.
Proof.
  intros Hbound.
  rewrite /is_slice_small.
  rewrite /list.untype fmap_drop fmap_take.
  rewrite slice.is_slice_small_take_drop //.
Qed.

Theorem is_slice_combine s t q n vs1 vs2 :
  (int.nat n ≤ int.nat s.(Slice.sz))%nat →
  is_slice_small (slice_take s t n) t q vs1 -∗
  is_slice_small (slice_skip s t n) t q vs2 -∗
  is_slice_small s t q (vs1 ++ vs2).
Proof.
  iIntros (Hbound).
  rewrite /is_slice_small /list.untype fmap_app.
  rewrite slice.is_slice_combine //.
Qed.

Global Instance is_slice_small_Fractional s q t vs :
  fractional.AsFractional (is_slice_small s t q vs) (λ q, is_slice_small s t q vs) q.
Proof.
  split; auto; apply _.
  Unshelve.
  exact 1%Qp.
Qed.

Global Instance is_slice_small_as_mapsto s t vs :
  AsMapsTo (is_slice_small s t 1 vs) (λ q, is_slice_small s t q vs).
Proof.
  constructor; auto; intros; apply _.
  Unshelve.
  exact 1%Qp.
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

Lemma wp_SliceSet stk E s t `{!IntoValForType IntoVal0 t} vs (i: u64) v :
  {{{ is_slice_small s t 1 vs ∗ ⌜ is_Some (vs !! int.nat i) ⌝ }}}
    SliceSet t (slice_val s) #i (to_val v) @ stk; E
  {{{ RET #(); is_slice_small s t 1 (<[int.nat i:=v]> vs) }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  iApply (slice.wp_SliceSet with "[$Hs]").
  { iPureIntro; intuition.
    { destruct H. rewrite /is_Some /list.untype list_lookup_fmap.
      rewrite H. eauto. }
    apply to_val_ty.
  }
  iIntros "!> Hs".
  iApply "HΦ".
  rewrite /is_slice_small /list.untype list_fmap_insert. iFrame.
Qed.

Lemma wp_SliceAppend'' stk E s t `{!IntoValForType IntoVal0 t} vs1 vs2 (x: V) (q : Qp) (n : u64) :
  0 ≤ int.Z n ≤ int.Z (Slice.sz s) ≤ int.Z (Slice.cap s) ->
  (q < 1)%Qp ->
  {{{ is_slice_small (slice_take s t n) t q vs1 ∗
      is_slice (slice_skip s t n) t 1 vs2 }}}
    SliceAppend t (slice_val s) (to_val x) @ stk; E
  {{{ s', RET slice_val s';
      is_slice_small (slice_take s' t n) t q vs1 ∗
      is_slice (slice_skip s' t n) t 1 (vs2 ++ [x]) ∗
      ⌜int.Z (Slice.sz s') ≤ int.Z (Slice.cap s') ∧
       int.Z (Slice.sz s') = (int.Z (Slice.sz s) + 1)%Z⌝}}}.
Proof.
  iIntros (Hn Hq Φ) "[Hsm Hs] HΦ".
  wp_apply (slice.wp_SliceAppend'' with "[$Hsm $Hs]").
  { apply to_val_has_zero. }
  { apply to_val_ty. }
  { eassumption. }
  { eassumption. }
  iIntros (s') "[Hsm Hs]".
  rewrite /list.untype.
  change [to_val x] with (to_val <$> [x]).
  rewrite -fmap_app.
  iApply ("HΦ" with "[$Hsm $Hs]").
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
  {{{ is_slice s t 1 vs }}}
    SliceAppend t (slice_val s) (to_val x) @ stk; E
  {{{ s', RET slice_val s'; is_slice s' t 1 (vs ++ [x]) }}}.
Proof.
  iIntros (Φ) "Hs HΦ".
  wp_apply (wp_SliceAppend' with "Hs"); auto.
Qed.

Lemma wp_SliceAppendSlice stk E s1 s2 t `{!IntoValForType IntoVal0 t} (vs1 vs2: list V) :
  {{{ is_slice s1 t 1 vs1 ∗ is_slice s2 t 1 vs2 }}}
    SliceAppendSlice t (slice_val s1) (slice_val s2) @ stk; E
  {{{ s', RET slice_val s'; is_slice s' t 1 (vs1 ++ vs2) }}}.
Proof.
  iIntros (Φ) "[Hs1 Hs2] HΦ".
Admitted.

(** subslice and produce a new [is_slice_small], dropping the other elements of
the slice. Most useful in read-only contexts. *)
(* TODO: these subslicing theorems are still really messy as far as preserving
the rest of the slice *)
Lemma wp_SliceSubslice_drop_rest {stk E} s t q `{!IntoVal V} (vs: list V) (n m: u64) :
  (int.nat n ≤ int.nat m ≤ length vs)%nat →
  {{{ is_slice_small s t q vs }}}
    SliceSubslice t (slice_val s) #n #m @ stk; E
  {{{ s', RET slice_val s'; is_slice_small s' t q (subslice (int.nat n) (int.nat m) vs) }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  iDestruct (is_slice_small_sz with "Hs") as %Hsz.
  wp_apply wp_SliceSubslice.
  { iPureIntro; word. }
  iApply "HΦ".
  rewrite /is_slice_small /slice.is_slice_small /=.
  iDestruct "Hs" as "[Ha _]".
  rewrite /list.untype.
  rewrite fmap_length.
  rewrite -> subslice_length by lia.
  iSplit; last by iPureIntro; word.
  rewrite -{1}(take_drop (int.nat m) vs) fmap_app.
  rewrite /subslice.
  iDestruct (array.array_app with "Ha") as "[Ha1 _]".
  set (vs':=take (int.nat m) vs).
  rewrite -{1}(take_drop (int.nat n) vs') fmap_app.
  iDestruct (array.array_app with "Ha1") as "[_ Ha2]".
  rewrite fmap_length take_length.
  iExactEq "Ha2".
  repeat f_equal.
  subst vs'; rewrite take_length.
  word.
Qed.

Transparent SliceCopy.
Lemma wp_SliceCopy stk E sl t q vs dst vs' :
  (length vs' ≥ length vs) →
  {{{ is_slice_small sl t q vs ∗ is_slice_small dst t 1 vs' }}}
    SliceCopy t (slice_val dst) (slice_val sl) @ stk; E
  {{{ RET #(U64 (length vs)); is_slice_small sl t q vs ∗ is_slice_small dst t 1 (vs ++ drop (length vs) vs') }}}.
Proof.
  iIntros (Hbound Φ) "(Hsrc&Hdst) HΦ".
  wp_call.
  iDestruct "Hsrc" as "[Hsrc %Hsrclen]".
  iDestruct "Hdst" as "[Hdst %Hdstlen]".
  autorewrite with len in Hsrclen, Hdstlen.
  wp_apply wp_slice_len.
  wp_apply wp_slice_len.
  wp_bind (If _ _ _).
  wp_pures.
  wp_if_destruct; first by iExFalso; word.
  wp_apply wp_slice_len.
  wp_pures.
  rewrite /slice.ptr; wp_pures.
  iEval (rewrite -(take_drop (length vs) (list.untype vs'))) in "Hdst".
  iDestruct (array.array_app with "Hdst") as "[Hdst1 Hdst2]".
  wp_apply (wp_MemCpy_rec with "[$Hsrc $Hdst1]").
  { iPureIntro.
    rewrite take_length !fmap_length.
    word. }
  iIntros "[Hdst1 Hsrc]".
  iDestruct (array.array_app with "[$Hdst1 Hdst2]") as "Hdst".
  { iExactEq "Hdst2".
    rewrite !take_length !fmap_length.
    repeat (f_equal; try lia). }
  wp_pures.
  replace (Slice.sz sl) with (U64 (length vs)) by word.
  iApply "HΦ".
  iFrame. iModIntro.
  iSplit.
  { iPureIntro.
    rewrite fmap_length; word. }
  rewrite /is_slice_small.
  rewrite /list.untype fmap_app fmap_drop.
  iSplitL.
  { iExactEq "Hdst".
    f_equal.
    rewrite take_ge //.
    rewrite fmap_length; word. }
  iPureIntro.
  rewrite !app_length !drop_length !fmap_length.
  word.
Qed.
Opaque SliceCopy.

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
      {{{ I i ∗ ⌜int.Z i < int.Z s.(Slice.sz)⌝ ∗
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
  (∀ (i: u64) (x: V) (done: list V) (todo: list V),
      ⌜done ++ x::todo = vs⌝ →
      {{{ P done (x :: todo) }}}
        body #i (to_val x) @ stk; E
      {{{ RET #(); P (done ++ [x]) todo }}}) -∗
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
    assert (drop (int.nat i) vs = x::drop (S (int.nat i)) vs) as Hdrop_S.
    { eapply drop_S in H0; eauto. }
    wp_apply ("Hind" with "[%] [HP]").
    { rewrite -[vs in _ = vs](take_drop (int.nat i)).
      rewrite Hdrop_S //. }
    { rewrite Hdrop_S; iFrame. }
    iIntros "HP".
    iApply "HΦ0".
    iExactEq "HP". f_equal.
    { apply take_S_r in H0. rewrite -H0. f_equal. word. }
    f_equal. word.
  }

  iModIntro. iIntros "[HP Hs]".
  iDestruct (is_slice_small_sz with "Hs") as %<-.
  iApply "HΦ". iFrame.
  rewrite firstn_all drop_all //.
Qed.

End heap.
