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

#[global]
Hint Rewrite @list_untype_length : len.

Section heap.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Context `{!IntoVal V}.

Implicit Types (s:Slice.t) (vs: list V) (v:V).
Implicit Types (t:ty).

(* We need to break this abstraction. *)
Typeclasses Transparent slice.own_slice_small.

Definition own_slice s t q vs := slice.own_slice s t q (list.untype vs).
Definition own_slice_small s t q vs := slice.own_slice_small s t q (list.untype vs).

Lemma own_slice_small_acc s t q vs :
  own_slice s t q vs -∗ own_slice_small s t q vs ∗ (∀ vs', own_slice_small s t q vs' -∗ own_slice s t q vs').
Proof.
  iIntros "Hs".
  iDestruct (slice.own_slice_small_acc with "Hs") as "[$ Hs]".
  iIntros (vs') "Hsmall".
  iApply ("Hs" with "[$]").
Qed.

Lemma own_slice_small_read s t q vs :
  own_slice s t q vs -∗ own_slice_small s t q vs ∗ (own_slice_small s t q vs -∗ own_slice s t q vs).
Proof.
  iIntros "Hs".
  iDestruct (slice.own_slice_small_read with "Hs") as "[$ Hs]".
  iIntros "Hsmall".
  iApply ("Hs" with "[$]").
Qed.

Lemma untype_replicate n (x : V) :
  list.untype (replicate n x) = replicate n (to_val x).
Proof.
  rewrite /list.untype fmap_replicate //.
Qed.

Lemma own_slice_small_sz s t q vs :
  own_slice_small s t q vs ⊢@{_} ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof.
  iIntros "(_&[%%]) !%".
  rewrite fmap_length // in H.
Qed.

Lemma own_slice_to_small s t q vs :
  own_slice s t q vs ⊢@{_} own_slice_small s t q vs.
Proof.
  rewrite /own_slice /own_slice_small.
  iIntros "Hs".
  iDestruct (slice.own_slice_to_small with "Hs") as "Hs".
  done.
Qed.

Lemma own_slice_sz s t q vs :
  own_slice s t q vs ⊢@{_} ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof.
  rewrite own_slice_to_small own_slice_small_sz //.
Qed.

Theorem own_slice_zero t q :
  ⊢ own_slice Slice.nil t q [].
Proof.
  rewrite /own_slice /=.
  iApply slice.own_slice_zero.
Qed.

Theorem own_slice_small_nil t q s :
  int.Z s.(Slice.sz) = 0 ->
  ⊢ own_slice_small s t q [].
Proof.
  intros Hsz.
  rewrite /own_slice_small /=.
  iApply slice.own_slice_small_nil; auto.
Qed.

Lemma slice_small_split s (n: u64) t q vs :
  int.Z n <= length vs →
  own_slice_small s t q vs -∗ own_slice_small (slice_take s n) t q (take (int.nat n) vs) ∗
           own_slice_small (slice_skip s t n) t q (drop (int.nat n) vs).
Proof.
  iIntros (Hbounds) "Hs".
  rewrite /own_slice_small.
  iDestruct (slice.slice_small_split with "Hs") as "[Hs1 Hs2]".
  { rewrite fmap_length //. }
  rewrite -fmap_take -fmap_drop.
  iFrame.
Qed.

Theorem own_slice_small_take_drop s t q n vs :
  (int.nat n <= int.nat s.(Slice.sz))%nat ->
  own_slice_small (slice_skip s t n) t q (drop (int.nat n) vs) ∗
  own_slice_small (slice_take s n) t q (take (int.nat n) vs) ⊣⊢
  own_slice_small s t q vs.
Proof.
  intros Hbound.
  rewrite /own_slice_small.
  rewrite /list.untype fmap_drop fmap_take.
  rewrite slice.own_slice_small_take_drop //.
Qed.

Theorem own_slice_combine s t q n vs1 vs2 :
  (int.nat n ≤ int.nat s.(Slice.sz))%nat →
  own_slice_small (slice_take s n) t q vs1 ⊢@{_}
  own_slice_small (slice_skip s t n) t q vs2 -∗
  own_slice_small s t q (vs1 ++ vs2).
Proof.
  iIntros (Hbound).
  rewrite /own_slice_small /list.untype fmap_app.
  rewrite slice.own_slice_combine //.
Qed.

Global Instance own_slice_small_Fractional s t vs :
  fractional.Fractional (λ q, own_slice_small s t q vs).
Proof. apply _. Qed.

Global Instance own_slice_small_AsFractional s q t vs :
  fractional.AsFractional (own_slice_small s t q vs) (λ q, own_slice_small s t q vs) q.
Proof. split; auto; apply _. Qed.

Global Instance own_slice_small_as_mapsto s t vs :
  AsMapsTo (own_slice_small s t 1 vs) (λ q, own_slice_small s t q vs).
Proof. constructor; auto; intros; apply _. Qed.

Lemma wp_NewSlice stk E t `{!IntoValForType V t} (sz: u64) :
  {{{ True }}}
    NewSlice t #sz @ stk; E
  {{{ s, RET slice_val s; own_slice s t 1 (replicate (int.nat sz) (IntoVal_def V)) }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_apply slice.wp_new_slice.
  { apply to_val_has_zero. }
  iIntros (s) "Hs".
  iApply "HΦ".
  rewrite /own_slice.
  rewrite untype_replicate.
  rewrite def_is_zero.
  iApply "Hs".
Qed.

Lemma wp_NewSliceWithCap stk E t `{!IntoValForType V t} (sz cap : u64) :
  int.Z sz ≤ int.Z cap →
  {{{ True }}}
    NewSliceWithCap t #sz #cap @ stk; E
  {{{ ptr, RET slice_val (Slice.mk ptr sz cap);
    own_slice (Slice.mk ptr sz cap) t 1 (replicate (int.nat sz) (IntoVal_def V))
  }}}.
Proof.
  iIntros (? Φ) "_ HΦ".
  wp_apply slice.wp_new_slice_cap.
  { apply to_val_has_zero. }
  { done. }
  iIntros (s) "Hs".
  iApply "HΦ".
  rewrite /own_slice.
  rewrite untype_replicate.
  rewrite def_is_zero.
  iApply "Hs".
Qed.

Lemma wp_SliceGet stk E s t q vs (i: u64) v0 :
  {{{ own_slice_small s t q vs ∗ ⌜ vs !! int.nat i = Some v0 ⌝ }}}
    SliceGet t (slice_val s) #i @ stk; E
  {{{ RET to_val v0; own_slice_small s t q vs }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  iApply (slice.wp_SliceGet with "[$Hs]").
  { iPureIntro.
    rewrite /list.untype list_lookup_fmap.
    rewrite H; eauto. }
  iIntros "!> [Hs _]".
  iApply ("HΦ" with "[$]").
Qed.

Lemma wp_SliceSet stk E s t `{!IntoValForType V t} vs (i: u64) v :
  {{{ own_slice_small s t 1 vs ∗ ⌜ is_Some (vs !! int.nat i) ⌝ }}}
    SliceSet t (slice_val s) #i (to_val v) @ stk; E
  {{{ RET #(); own_slice_small s t 1 (<[int.nat i:=v]> vs) }}}.
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
  rewrite /own_slice_small /list.untype list_fmap_insert. iFrame.
Qed.

Lemma wp_SliceAppend'' stk E s t `{!IntoValForType V t} vs1 vs2 (x: V) (q : Qp) (n : u64) :
  0 ≤ int.Z n ≤ int.Z (Slice.sz s) ≤ int.Z (Slice.cap s) ->
  (q < 1)%Qp ->
  {{{ own_slice_small (slice_take s n) t q vs1 ∗
      own_slice (slice_skip s t n) t 1 vs2 }}}
    SliceAppend t (slice_val s) (to_val x) @ stk; E
  {{{ s', RET slice_val s';
      own_slice_small (slice_take s' n) t q vs1 ∗
      own_slice (slice_skip s' t n) t 1 (vs2 ++ [x]) ∗
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

Lemma wp_SliceAppend stk E s t `{!IntoValForType V t} vs (x: V) :
  {{{ own_slice s t 1 vs }}}
    SliceAppend t (slice_val s) (to_val x) @ stk; E
  {{{ s', RET slice_val s'; own_slice s' t 1 (vs ++ [x]) }}}.
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

(** Only works with the full fraction since some of the ownership is moved from
the slice part to the extra part *)
Lemma wp_SliceSubslice_full {stk E} s t `{!IntoVal V} (vs: list V) (n m: u64) :
  (int.nat n ≤ int.nat m ≤ length vs)%nat →
  {{{ own_slice s t 1 vs }}}
    SliceSubslice t (slice_val s) #n #m @ stk; E
  {{{ s', RET slice_val s'; own_slice s' t 1 (subslice (int.nat n) (int.nat m) vs) }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  wp_apply wp_SliceSubslice.
  { word. }
  iApply "HΦ".
  rewrite /own_slice /slice.own_slice /=.
  iDestruct "Hs" as "[Hs Hcap]".
  iDestruct "Hs" as "[Ha _]".
  rewrite /list.untype.
  rewrite -{1}(take_drop (int.nat m) vs) fmap_app.
  rewrite /subslice.
  iDestruct (array.array_app with "Ha") as "[Ha1 Htail]".
  set (vs':=take (int.nat m) vs).
  rewrite -{1}(take_drop (int.nat n) vs') fmap_app.
  iDestruct (array.array_app with "Ha1") as "[_ Ha2]". (* the part before the subslice we can dtop *)
  rewrite fmap_length take_length.
  iSplitL "Ha2".
  { iSplit.
    - iExactEq "Ha2".
      repeat f_equal.
      subst vs'; rewrite fmap_length. rewrite !take_length.
      rewrite //=.
      rewrite min_l; last word.
      rewrite u64_Z_through_nat. eauto.
    - iPureIntro. rewrite fmap_length /=.
      split; last word.
      subst vs'. rewrite drop_length take_length. word.
  }
  rewrite /own_slice_cap. simpl.
  iDestruct "Hcap" as (old_extra) "[% Htail2]".
  rewrite min_l; last word.
  iExists (_ ++ _).
  iSplit; last first.
  - iApply array.array_app.
    rewrite loc_add_assoc.
    replace (ty_size t * int.Z n + ty_size t * int.Z (word.sub m n)) with
      (ty_size t * int.nat m) by word.
    iFrame "Htail".
    iExactEq "Htail2". f_equal.
    rewrite fmap_length drop_length.
    rewrite loc_add_assoc.
    rewrite Hsz.
    rewrite -Z.mul_add_distr_l.
    rewrite ->Nat2Z.inj_sub by word.
    rewrite Zplus_minus.
    replace (int.Z (Slice.sz s)) with (Z.of_nat $ int.nat (Slice.sz s)) at 1 by word.
    done.
  - iPureIntro. rewrite app_length fmap_length drop_length. word.
Qed.

Lemma wp_SliceSubslice_small {stk E} s t q `{!IntoVal V} (vs: list V) (n m: u64) :
  (int.nat n ≤ int.nat m ≤ length vs)%nat →
  {{{ own_slice_small s t q vs }}}
    SliceSubslice t (slice_val s) #n #m @ stk; E
  {{{ s', RET slice_val s'; own_slice_small s' t q (subslice (int.nat n) (int.nat m) vs) }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  iDestruct (own_slice_small_wf with "Hs") as %Hwf.
  wp_apply wp_SliceSubslice.
  { word. }
  iApply "HΦ".
  rewrite /own_slice_small /slice.own_slice_small /=.
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
  {{{ own_slice_small sl t q vs ∗ own_slice_small dst t 1 vs' }}}
    SliceCopy t (slice_val dst) (slice_val sl) @ stk; E
  {{{ RET #(U64 (length vs)); own_slice_small sl t q vs ∗ own_slice_small dst t 1 (vs ++ drop (length vs) vs') }}}.
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
  rewrite /own_slice_small.
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

Lemma wp_SliceAppend_to_zero stk E t `{!IntoValForType V t} v (x: val) :
  x = to_val v ->
  {{{ True }}}
    SliceAppend t (zero_val (slice.T t)) x @ stk; E
  {{{ s', RET slice_val s'; own_slice s' t 1 [v] }}}.
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

Theorem wp_forSlice_mut (I: u64 -> iProp Σ) stk E s t q vs (body: val) :
  □ (∀ (i: u64),
        I i -∗ ∃ vs', ⌜ length vs' = length vs ⌝ ∗
                      ⌜ vs' !! int.nat i = vs !! int.nat i ⌝ ∗
                      own_slice_small s t q vs' ∗
                      (own_slice_small s t q vs' -∗ I i)) -∗
  (∀ (i: u64) (x: V),
      {{{ I i ∗ ⌜int.Z i < int.Z s.(Slice.sz)⌝ ∗
                ⌜vs !! int.nat i = Some x⌝ }}}
        body #i (to_val x) @ stk; E
      {{{ (v : val), RET v; I (word.add i (U64 1)) }}}) -∗
    {{{ I (U64 0) }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); I s.(Slice.sz) }}}.
Proof.
  iIntros "#Hslice_acc #Hbody".
  iIntros "!>" (Φ) "HI HΦ".
  wp_apply (slice.wp_forSlice_mut I _ _ _ _ _ (map to_val vs) with "[] [] [$HI]").
  {
    iModIntro. iIntros. iDestruct ("Hslice_acc" with "[$]" ) as (vs' Hlen Hlookup) "[Hs Hclo]".
    iExists (map to_val vs').
    rewrite ?map_length; iSplit; first auto.
    rewrite ?list_lookup_fmap Hlookup; iSplit; first auto.
    iFrame.
  }
  { clear.
    iIntros (i x).
    iIntros "!>" (Φ) "[HI [% %Hlookup]] HΦ".
    apply untype_lookup_Some in Hlookup as [v [Hlookup ->]].
    wp_apply ("Hbody" with "[$HI //]").
    iApply "HΦ". }
  iApply "HΦ".
Qed.

Theorem wp_forSlice (I: u64 -> iProp Σ) stk E s t q vs (body: val) :
  (∀ (i: u64) (x: V),
      {{{ I i ∗ ⌜int.Z i < int.Z s.(Slice.sz)⌝ ∗
                ⌜vs !! int.nat i = Some x⌝ }}}
        body #i (to_val x) @ stk; E
      {{{ (v : val), RET v; I (word.add i (U64 1)) }}}) -∗
    {{{ I (U64 0) ∗ own_slice_small s t q vs }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); I s.(Slice.sz) ∗ own_slice_small s t q vs }}}.
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
      {{{ (v : val), RET v; P (done ++ [x]) todo }}}) -∗
    {{{ own_slice_small s t q vs ∗ P nil vs }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); own_slice_small s t q vs ∗ P vs nil }}}.
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
    iIntros (v) "HP".
    iApply "HΦ0".
    iExactEq "HP". f_equal.
    { apply take_S_r in H0. rewrite -H0. f_equal. word. }
    f_equal. word.
  }

  iModIntro. iIntros "[HP Hs]".
  iDestruct (own_slice_small_sz with "Hs") as %<-.
  iApply "HΦ". iFrame.
  rewrite firstn_all drop_all //.
Qed.

End heap.
