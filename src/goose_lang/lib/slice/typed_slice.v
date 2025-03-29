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
  rewrite /list.untype length_fmap //.
Qed.

Lemma list_untype_app `{IntoVal V} (l1 l2: list V) :
  list.untype (l1 ++ l2) = list.untype l1 ++ list.untype l2.
Proof.
  rewrite /list.untype fmap_app //.
Qed.

Lemma list_untype_take `{IntoVal V} (l: list V) n :
  list.untype (take n l) = take n (list.untype l).
Proof.
  rewrite /list.untype fmap_take //.
Qed.

Lemma list_untype_drop `{IntoVal V} (l: list V) n :
  list.untype (drop n l) = drop n (list.untype l).
Proof.
  rewrite /list.untype fmap_drop //.
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

Lemma own_slice_split s t q vs :
  own_slice s t q vs ⊣⊢
  own_slice_small s t q vs ∗ own_slice_cap s t.
Proof. by rewrite /own_slice /own_slice_small. Qed.

Lemma own_slice_split_1 s t q vs :
  own_slice s t q vs -∗
  own_slice_small s t q vs ∗ own_slice_cap s t.
Proof. rewrite own_slice_split. iIntros "$". Qed.

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
  own_slice_small s t q vs ⊢@{_} ⌜length vs = uint.nat s.(Slice.sz)⌝.
Proof.
  iIntros "(_&[%%]) !%".
  rewrite length_fmap // in H.
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
  own_slice s t q vs ⊢@{_} ⌜length vs = uint.nat s.(Slice.sz)⌝.
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
  uint.Z s.(Slice.sz) = 0 ->
  ⊢ own_slice_small s t q [].
Proof.
  intros Hsz.
  rewrite /own_slice_small /=.
  iApply slice.own_slice_small_nil; auto.
Qed.

Lemma slice_small_split s (n: u64) t q vs :
  uint.Z n <= length vs →
  own_slice_small s t q vs -∗ own_slice_small (slice_take s n) t q (take (uint.nat n) vs) ∗
           own_slice_small (slice_skip s t n) t q (drop (uint.nat n) vs).
Proof.
  iIntros (Hbounds) "Hs".
  rewrite /own_slice_small.
  iDestruct (slice.slice_small_split with "Hs") as "[Hs1 Hs2]".
  { rewrite length_fmap //. }
  rewrite -fmap_take -fmap_drop.
  iFrame.
Qed.

Theorem own_slice_small_take_drop s t q n vs :
  (uint.nat n <= uint.nat s.(Slice.sz))%nat ->
  own_slice_small (slice_skip s t n) t q (drop (uint.nat n) vs) ∗
  own_slice_small (slice_take s n) t q (take (uint.nat n) vs) ⊣⊢
  own_slice_small s t q vs.
Proof.
  intros Hbound.
  rewrite /own_slice_small.
  rewrite /list.untype fmap_drop fmap_take.
  rewrite slice.own_slice_small_take_drop //.
Qed.

Theorem own_slice_combine s t q n vs1 vs2 :
  (uint.nat n ≤ uint.nat s.(Slice.sz))%nat →
  own_slice_small (slice_take s n) t q vs1 ⊢@{_}
  own_slice_small (slice_skip s t n) t q vs2 -∗
  own_slice_small s t q (vs1 ++ vs2).
Proof.
  iIntros (Hbound).
  rewrite /own_slice_small /list.untype fmap_app.
  rewrite slice.own_slice_combine //.
Qed.

Global Instance own_slice_small_Fractional s t vs :
  fractional.Fractional (λ q, own_slice_small s t (DfracOwn q) vs).
Proof. apply _. Qed.

Global Instance own_slice_small_AsFractional s q t vs :
  fractional.AsFractional (own_slice_small s t (DfracOwn q) vs) (λ q, own_slice_small s t (DfracOwn q) vs) q.
Proof. split; auto; apply _. Qed.

Global Instance own_slice_small_as_pointsto s t vs :
  AsMapsTo (own_slice_small s t (DfracOwn 1) vs) (λ q, own_slice_small s t (DfracOwn q) vs).
Proof. constructor; auto; intros; apply _. Qed.

Global Instance own_slice_small_persistent s t vs : Persistent (own_slice_small s t DfracDiscarded vs).
Proof. apply _. Qed.

Lemma own_slice_small_persist s t dq vs:
  own_slice_small s t dq vs ==∗ own_slice_small s t DfracDiscarded vs.
Proof.
  iIntros "Hs".
  iMod (slice.own_slice_small_persist with "Hs") as "Hs".
  iModIntro.
  iFrame.
Qed.

#[global]
Instance own_slice_small_persistently s t dq vs :
  UpdateIntoPersistently (own_slice_small s t dq vs) (own_slice_small s t DfracDiscarded vs).
Proof.
  rewrite /UpdateIntoPersistently.
  iIntros "H".
  iMod (own_slice_small_persist with "H") as "#H".
  done.
Qed.

Lemma wp_NewSlice stk E t `{!IntoValForType V t} (sz: u64) :
  {{{ True }}}
    NewSlice t #sz @ stk; E
  {{{ s, RET slice_val s; own_slice s t (DfracOwn 1) (replicate (uint.nat sz) (IntoVal_def V)) }}}.
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

Lemma wp_NewSlice_0 stk E t `{!IntoValForType V t} :
  {{{ True }}}
    NewSlice t #(W64 0) @ stk; E
  {{{ s, RET slice_val s; own_slice s t (DfracOwn 1) [] }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "_".
  wp_apply wp_NewSlice. iIntros (s) "Hs".
  iApply "HΦ".
  iExact "Hs".
Qed.

Lemma wp_NewSliceWithCap stk E t `{!IntoValForType V t} (sz cap : u64) :
  uint.Z sz ≤ uint.Z cap →
  {{{ True }}}
    NewSliceWithCap t #sz #cap @ stk; E
  {{{ ptr, RET slice_val (Slice.mk ptr sz cap);
    own_slice (Slice.mk ptr sz cap) t (DfracOwn 1) (replicate (uint.nat sz) (IntoVal_def V))
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

Lemma wp_NewSliceWithCap_0 stk E t `{!IntoValForType V t} (cap : u64) :
  {{{ True }}}
    NewSliceWithCap t #(W64 0) #cap @ stk; E
  {{{ s, RET slice_val s;
    own_slice s t (DfracOwn 1) [] ∗ ⌜Slice.cap s = cap⌝
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_apply wp_NewSliceWithCap.
  { word. }
  iIntros (ptr) "Hs".
  rewrite replicate_0.
  iApply "HΦ".
  iFrame.
  rewrite //=.
Qed.

Theorem wp_SliceSingleton stk E t `{!IntoValForType V t} (x : V) :
  {{{ True }}}
    SliceSingleton (to_val x) @ stk; E
  {{{ s, RET slice_val s; own_slice s t (DfracOwn 1) [x] }}}.
Proof.
  iIntros (Hty) "_ HΦ".
  wp_apply wp_SliceSingleton.
  { apply to_val_ty. }
  iIntros (?).
  iIntros "Hsl". iApply "HΦ".
  rewrite /own_slice /list.untype //.
Qed.

Lemma wp_SliceGet stk E s t q vs (i: u64) v0 :
  {{{ own_slice_small s t q vs ∗ ⌜ vs !! uint.nat i = Some v0 ⌝ }}}
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

Lemma wp_SliceTake_small {stk E s} t q vs (n: u64):
  uint.Z n ≤ length vs →
  {{{ own_slice_small s t q vs }}}
    SliceTake (slice_val s) #n @ stk; E
  {{{ RET (slice_val (slice_take s n)); own_slice_small (slice_take s n) t q (take (uint.nat n) vs) }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  rewrite /own_slice_small.
  wp_apply (slice.wp_SliceTake_small with "[$Hs]").
  { rewrite list_untype_length //. }
  rewrite /list.untype fmap_take //.
Qed.

Lemma wp_SliceSkip_small s t q vs (n : u64) :
  uint.Z n ≤ length vs →
  {{{ own_slice_small s t q vs }}}
    SliceSkip t (slice_val s) #n
  {{{ s', RET (slice_val s'); own_slice_small s' t q (drop (uint.nat n) vs) }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  rewrite /own_slice_small. rewrite /list.untype fmap_drop.
  wp_apply (slice.wp_SliceSkip_small with "[$Hs]").
  { rewrite length_fmap; auto. }
  auto.
Qed.

Lemma wp_SliceSkip_full s t q vs (n : u64) :
  uint.Z n ≤ length vs →
  {{{ own_slice s t q vs }}}
    SliceSkip t (slice_val s) #n
  {{{ s', RET (slice_val s'); own_slice s' t q (drop (uint.nat n) vs) }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  wp_apply slice.wp_SliceSkip.
  { word. }
  iApply "HΦ".
  iApply own_slice_split.
  iDestruct (own_slice_split_1 with "Hs") as "[Hs Hcap]".
  rewrite /own_slice_small. rewrite /list.untype fmap_drop.
  iDestruct (slice.slice_small_split with "Hs") as "[Hs1 $]".
  { rewrite length_fmap; word. }
  iApply (own_slice_cap_skip with "[$Hcap]").
  { word. }
Qed.

(* construct the capacity of a slice_take expression from ownership over the
rest of the slice (expressed using [slice_skip]) and the original capacity. *)
Lemma own_slice_cap_take s t n vs :
  uint.Z n ≤ uint.Z s.(Slice.sz) →
  own_slice_small (slice_skip s t n) t (DfracOwn 1) (drop (uint.nat n) vs) ∗
    own_slice_cap s t -∗
  own_slice_cap (slice_take s n) t.
Proof.
  iIntros (Hn) "[Hskip Hcap]".
  rewrite /own_slice_small.
  iApply (slice.own_slice_cap_take with "[Hskip $Hcap]").
  { auto. }
  rewrite /list.untype fmap_drop. iFrame.
Qed.

(* Take a prefix s[:n] while retaining the capacity, which now includes the
elements from n to the original length. Since the capacity must be fully owned,
this variant requires full ownership of the slice and not a partial fraction. *)
Lemma wp_SliceTake_full {stk E s} t vs (n: u64):
  uint.Z n ≤ length vs →
  {{{ own_slice s t (DfracOwn 1) vs }}}
    SliceTake (slice_val s) #n @ stk; E
  {{{ RET (slice_val (slice_take s n)); own_slice (slice_take s n) t (DfracOwn 1) (take (uint.nat n) vs) }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  iDestruct (own_slice_split_1 with "Hs") as "[Hs Hcap]".
  iDestruct (own_slice_cap_wf with "Hcap") as %Hcap.
  wp_apply (slice.wp_SliceTake).
  { word. }
  iApply "HΦ".
  iDestruct (slice_small_split with "Hs") as "[$ Hdrop]".
  { word. }
  iApply own_slice_cap_take; [ word | ]. iFrame.
Qed.

Lemma wp_SliceSet stk E s t `{!IntoValForType V t} vs (i: u64) v :
  {{{ own_slice_small s t (DfracOwn 1) vs ∗ ⌜ is_Some (vs !! uint.nat i) ⌝ }}}
    SliceSet t (slice_val s) #i (to_val v) @ stk; E
  {{{ RET #(); own_slice_small s t (DfracOwn 1) (<[uint.nat i:=v]> vs) }}}.
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
  0 ≤ uint.Z n ≤ uint.Z (Slice.sz s) ≤ uint.Z (Slice.cap s) ->
  (q < 1)%Qp ->
  {{{ own_slice_small (slice_take s n) t (DfracOwn q) vs1 ∗
      own_slice (slice_skip s t n) t (DfracOwn 1) vs2 }}}
    SliceAppend t (slice_val s) (to_val x) @ stk; E
  {{{ s', RET slice_val s';
      own_slice_small (slice_take s' n) t (DfracOwn q) vs1 ∗
      own_slice (slice_skip s' t n) t (DfracOwn 1) (vs2 ++ [x]) ∗
      ⌜uint.Z (Slice.sz s') ≤ uint.Z (Slice.cap s') ∧
       uint.Z (Slice.sz s') = (uint.Z (Slice.sz s) + 1)%Z⌝}}}.
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
  {{{ own_slice s t (DfracOwn 1) vs }}}
    SliceAppend t (slice_val s) (to_val x) @ stk; E
  {{{ s', RET slice_val s'; own_slice s' t (DfracOwn 1) (vs ++ [x]) }}}.
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

(* TODO: why is this opaque? *)
Transparent SliceAppendSlice.

Lemma wp_SliceAppendSlice stk E s1 s2 t vs1 vs2 q2 :
  has_zero t →
  {{{ own_slice s1 t (DfracOwn 1) vs1 ∗ own_slice_small s2 t q2 vs2 }}}
    SliceAppendSlice t s1 s2 @ stk; E
  {{{
    s', RET slice_val s';
    own_slice s' t (DfracOwn 1) (vs1 ++ vs2) ∗
    own_slice_small s2 t q2 vs2
  }}}.
Proof.
  intros Hzero.
  iIntros (Φ) "[Hs1 Hs2] HΦ".
  wp_apply (slice.wp_SliceAppendSlice with "[$Hs1 $Hs2]"); [ auto | ].
  iIntros (sl') "[Hs' Hs2]".
  iApply "HΦ".
  rewrite /own_slice /own_slice_small.
  rewrite list_untype_app.
  iFrame.
Qed.

Opaque SliceAppendSlice.

Local Ltac simplify_nonlinear :=
  rewrite -?Z.mul_add_distr_l ?Zred_factor3.

(** Only works with the full fraction since some of the ownership is moved from
the slice part to the extra part *)
Lemma wp_SliceSubslice_full {stk E} s t `{!IntoVal V} (vs: list V) (n m: u64) :
  (uint.nat n ≤ uint.nat m ≤ length vs)%nat →
  {{{ own_slice s t (DfracOwn 1) vs }}}
    SliceSubslice t (slice_val s) #n #m @ stk; E
  {{{ s', RET slice_val s'; own_slice s' t (DfracOwn 1) (subslice (uint.nat n) (uint.nat m) vs) }}}.
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
  rewrite -{1}(take_drop (uint.nat m) vs) fmap_app.
  rewrite /subslice.
  iDestruct (array.array_app with "Ha") as "[Ha1 Htail]".
  set (vs':=take (uint.nat m) vs).
  rewrite -{1}(take_drop (uint.nat n) vs') fmap_app.
  iDestruct (array.array_app with "Ha1") as "[_ Ha2]". (* the part before the subslice we can dtop *)
  rewrite length_fmap length_take.
  iSplitL "Ha2".
  { iSplit.
    - iExactEq "Ha2".
      repeat f_equal.
      subst vs'; rewrite length_fmap. rewrite !length_take.
      rewrite //=.
      rewrite min_l; last word.
      rewrite u64_Z_through_nat. eauto.
    - iPureIntro. rewrite length_fmap /=.
      split; last word.
      subst vs'. rewrite length_drop length_take. word.
  }
  rewrite /own_slice_cap. simpl.
  iDestruct "Hcap" as (old_extra) "[% Htail2]".
  rewrite min_l; last word.
  iExists (_ ++ _).
  iSplit; last first.
  - iApply array.array_app.
    rewrite loc_add_assoc.
    replace (ty_size t * uint.Z n + ty_size t * uint.Z (word.sub m n)) with
      (ty_size t * uint.nat m).
    2:{ simplify_nonlinear. f_equal. word. }
    iFrame "Htail".
    iExactEq "Htail2". f_equal.
    rewrite length_fmap length_drop.
    rewrite loc_add_assoc.
    rewrite Hsz.
    rewrite -Z.mul_add_distr_l.
    rewrite ->Nat2Z.inj_sub by word.
    rewrite Zplus_minus.
    replace (uint.Z (Slice.sz s)) with (Z.of_nat $ uint.nat (Slice.sz s)) at 1 by word.
    done.
  - iPureIntro. rewrite length_app length_fmap length_drop. word.
Qed.

Lemma wp_SliceSubslice_small {stk E} s t q `{!IntoVal V} (vs: list V) (n m: u64) :
  (uint.nat n ≤ uint.nat m ≤ length vs)%nat →
  {{{ own_slice_small s t q vs }}}
    SliceSubslice t (slice_val s) #n #m @ stk; E
  {{{ s', RET slice_val s'; own_slice_small s' t q (subslice (uint.nat n) (uint.nat m) vs) }}}.
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
  rewrite length_fmap.
  rewrite -> subslice_length by lia.
  iSplit; last by word.
  rewrite -{1}(take_drop (uint.nat m) vs) fmap_app.
  rewrite /subslice.
  iDestruct (array.array_app with "Ha") as "[Ha1 _]".
  set (vs':=take (uint.nat m) vs).
  rewrite -{1}(take_drop (uint.nat n) vs') fmap_app.
  iDestruct (array.array_app with "Ha1") as "[_ Ha2]".
  rewrite length_fmap length_take.
  iExactEq "Ha2".
  repeat f_equal.
  subst vs'; rewrite length_take.
  word.
Qed.

Transparent SliceCopy.
Lemma wp_SliceCopy stk E sl t q vs dst vs' :
  (length vs' ≥ length vs) →
  {{{ own_slice_small sl t q vs ∗ own_slice_small dst t (DfracOwn 1) vs' }}}
    SliceCopy t (slice_val dst) (slice_val sl) @ stk; E
  {{{ RET #(W64 (length vs)); own_slice_small sl t q vs ∗ own_slice_small dst t (DfracOwn 1) (vs ++ drop (length vs) vs') }}}.
Proof.
  iIntros (Hbound Φ) "(Hsrc&Hdst) HΦ".
  wp_rec. wp_pures.
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
    rewrite length_take !length_fmap.
    word. }
  iIntros "[Hdst1 Hsrc]".
  iDestruct (array.array_app with "[$Hdst1 Hdst2]") as "Hdst".
  { iExactEq "Hdst2".
    rewrite !length_take !length_fmap.
    repeat (f_equal; try lia). }
  wp_pures.
  replace (Slice.sz sl) with (W64 (length vs)) by word.
  iApply "HΦ".
  iFrame. iModIntro.
  iSplit.
  { iPureIntro.
    rewrite length_fmap; word. }
  rewrite /own_slice_small.
  rewrite /list.untype fmap_app fmap_drop.
  iSplitL.
  { iExactEq "Hdst".
    f_equal.
    rewrite take_ge //.
    rewrite length_fmap; word. }
  iPureIntro.
  rewrite !length_app !length_drop !length_fmap.
  word.
Qed.

Lemma wp_SliceCopy_full stk E sl t q vs dst vs' :
  {{{ own_slice_small sl t q vs ∗ own_slice_small dst t (DfracOwn 1) vs' ∗ ⌜length vs = length vs'⌝}}}
    SliceCopy t (slice_val dst) (slice_val sl) @ stk; E
  {{{ (l: w64), RET #l; ⌜uint.nat l = length vs⌝ ∗ own_slice_small sl t q vs ∗ own_slice_small dst t (DfracOwn 1) vs }}}.
Proof.
  iIntros (Φ) "(Hsrc & Hdst & %Hlen) HΦ".
  iDestruct (own_slice_small_sz with "Hsrc") as %Hsz.
  wp_apply (wp_SliceCopy with "[$Hsrc $Hdst]"); [lia|].
  iIntros "(? & ?)".
  rewrite Hlen.
  rewrite drop_all.
  list_simplifier.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  word.
Qed.

Lemma wp_SliceCopy_SliceSkip_src stk E src (n : u64) t q vs dst vs' :
  (uint.nat n ≤ length vs)%nat ->
  length vs' = (length vs - uint.nat n)%nat ->
  {{{ own_slice_small src t q vs ∗ own_slice_small dst t (DfracOwn 1) vs' }}}
    SliceCopy t (slice_val dst) (SliceSkip t (slice_val src) #n) @ stk; E
  {{{ RET #(W64 (length vs'));
      own_slice_small src t q vs ∗ own_slice_small dst t (DfracOwn 1) (drop (uint.nat n) vs)
  }}}.
Proof.
  iIntros (Hn Hlen Φ) "[Hsrc Hdst] HΦ".
  wp_apply (slice.wp_SliceCopy_SliceSkip_src with "[$Hsrc $Hdst]").
  { by rewrite list_untype_length. }
  { by rewrite 2!list_untype_length. }
  iIntros "[Hsrc Hdst]".
  rewrite list_untype_length.
  iApply "HΦ".
  rewrite -list_untype_drop.
  iFrame.
Qed.

Lemma wp_SliceCopy_subslice stk E sl (n1 n2: u64) t q vs dst vs' :
  {{{ own_slice_small sl t q vs ∗
      ⌜uint.Z n1 ≤ uint.Z n2 ≤ Z.of_nat (length vs')⌝ ∗
      own_slice_small dst t (DfracOwn 1) vs' ∗
        (* requires source to exactly fit (mostly to simplify the spec) *)
      ⌜Z.of_nat (length vs) = (uint.Z n2 - uint.Z n1)⌝ }}}
    SliceCopy t (SliceSubslice t (slice_val dst) #n1 #n2)
                (slice_val sl) @ stk; E
  {{{ (n: w64), RET #n;
      ⌜uint.Z n = uint.Z n2 - uint.Z n1⌝ ∗
      own_slice_small dst t (DfracOwn 1)
        (take (uint.nat n1) vs' ++
         vs ++
         drop (uint.nat n2)%nat vs') ∗
      own_slice_small sl t q vs }}}.
Proof.
  iIntros (Φ) "(Hsrc & % & Hdst & %) HΦ".
  wp_apply (slice.wp_SliceCopy_subslice with "[$Hsrc $Hdst]").
  { rewrite !list_untype_length. iPureIntro. auto. }
  iIntros (n) "(% & Hdst & Hsrc)".
  iApply "HΦ".
  iSplit; [ auto | ].
  iFrame "Hsrc".
  iExactEq "Hdst".
  rewrite /own_slice_small.
  rewrite !list_untype_app !list_untype_take !list_untype_drop //.
Qed.

Opaque SliceCopy.

Lemma wp_SliceAppend_to_zero stk E t `{!IntoValForType V t} v (x: val) :
  x = to_val v ->
  {{{ True }}}
    SliceAppend t (zero_val (slice.T t)) x @ stk; E
  {{{ s', RET slice_val s'; own_slice s' t (DfracOwn 1) [v] }}}.
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
                      ⌜ vs' !! uint.nat i = vs !! uint.nat i ⌝ ∗
                      own_slice_small s t q vs' ∗
                      (own_slice_small s t q vs' -∗ I i)) -∗
  (∀ (i: u64) (x: V),
      {{{ I i ∗ ⌜uint.Z i < uint.Z s.(Slice.sz)⌝ ∗
                ⌜vs !! uint.nat i = Some x⌝ }}}
        body #i (to_val x) @ stk; E
      {{{ (v : val), RET v; I (word.add i (W64 1)) }}}) -∗
    {{{ I (W64 0) }}}
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
      {{{ I i ∗ ⌜uint.Z i < uint.Z s.(Slice.sz)⌝ ∗
                ⌜vs !! uint.nat i = Some x⌝ }}}
        body #i (to_val x) @ stk; E
      {{{ (v : val), RET v; I (word.add i (W64 1)) }}}) -∗
    {{{ I (W64 0) ∗ own_slice_small s t q vs }}}
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

Lemma wp_forSlice' I ϕ sl ty q (l:list V) (body:val) :
  (∀ (i:u64) (v:V),
    {{{
          ⌜uint.nat i < length l⌝ ∗ ⌜l !! (uint.nat i) = Some v⌝ ∗ ϕ (uint.nat i) v ∗ I i
    }}}
      body #i (to_val v)
    {{{
          RET #(); I (word.add i 1)
    }}}
  ) -∗
  {{{
        own_slice_small sl ty q l ∗
        ([∗ list] i ↦ v ∈ l, ϕ i v) ∗
        I 0
  }}}
    forSlice ty body (slice_val sl)
  {{{
        RET #(); I (length l)
  }}}
.
Proof.
  iIntros "#Hwp".
  iIntros (?) "!# (Hsl & Hl & HI) HΦ".
  iDestruct (own_slice_small_sz with "Hsl") as %Hsz.
  wp_apply (wp_forSlice (λ i, I i ∗ [∗ list] j ↦ v ∈ (drop (uint.nat i) l), ϕ (j + uint.nat i)%nat v) %I
             with "[] [$Hsl Hl HI]").
  2: { rewrite drop_0.
       replace (uint.nat (W64 0)) with (0%nat) by word.
       setoid_rewrite <- plus_n_O. iFrame. }
  {
    clear Φ.
    iIntros (???Φ) "!# ([HI Hl] & % & %) HΦ".
    assert ((drop (uint.nat i) l) !! 0%nat = Some x) as ?.
    {
      rewrite lookup_drop. rewrite <- H0.
      f_equal. word.
    }
    iDestruct (big_sepL_take_drop _ _ 1 with "Hl") as "[Hϕ Hl]".
    wp_apply ("Hwp" with "[HI Hϕ]").
    {
      iFrame "∗%".
      iSplit. 1: word.
      iDestruct (big_sepL_lookup_acc with "Hϕ") as "[H _]".
      {
        rewrite lookup_take.
        { done. }
        lia.
      }
      iExactEq "H". repeat f_equal.
    }
    iIntros "HI".
    iApply "HΦ".
    iFrame.
    rewrite drop_drop.
    replace (uint.nat (word.add i 1%Z))%nat with (uint.nat i + 1)%nat by word.
    iApply (big_sepL_impl with "Hl").
    iModIntro.
    iIntros.
    replace (k + (uint.nat i + 1))%nat with (1 + k + uint.nat i)%nat by word.
    done.
  }
  iIntros "[[HI _] _]".
  iApply "HΦ".
  rewrite Hsz.
  iExactEq "HI". f_equal. word.
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
  iApply (wp_forSlice (λ i, P (take (uint.nat i) vs) (drop (uint.nat i) vs))
    with "[] [$Hs $Hi0]").
  {
    iIntros (i x). iModIntro.
    iIntros (Φ0) "(HP & % & %) HΦ0".
    assert (drop (uint.nat i) vs = x::drop (S (uint.nat i)) vs) as Hdrop_S.
    { eapply drop_S in H0; eauto. }
    wp_apply ("Hind" with "[%] [HP]").
    { rewrite -[vs in _ = vs](take_drop (uint.nat i)).
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

Theorem wp_forSliceEach (I: iProp Σ) (P Q: V -> iProp Σ) stk E s t q vs (body: val) :
  (∀ (i: u64) (x: V),
      {{{ I ∗ P x }}}
        body #i (to_val x) @ stk; E
      {{{ (v : val), RET v; I ∗ Q x }}}) -∗
    {{{ own_slice_small s t q vs ∗ I ∗ [∗ list] x ∈ vs, P x }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); own_slice_small s t q vs ∗ I ∗ [∗ list] x ∈ vs, Q x }}}.
Proof.
  iIntros "#Hind".
  iIntros (Φ) "!> [Hs [Hi Hp]] HΦ".
  iApply (wp_forSliceEach I (λ vv, ∃ v, ⌜vv=to_val v⌝ ∗ P v)%I (λ vv, ∃ v, ⌜vv=to_val v⌝ ∗ Q v)%I with "[] [$Hs $Hi Hp]").
  {
    iIntros (i x Ψ) "!> [Hi Hp] HΨ".
    iDestruct "Hp" as (v) "[% Hp]". subst.
    iApply ("Hind" with "[$Hi $Hp] [-]").
    iNext. iIntros (v0) "[Hi Hq]".
    iApply "HΨ". iFrame. done.
  }
  {
    iApply big_sepL_fmap.
    iApply (big_sepL_impl with "Hp").
    iModIntro. iIntros (??) "% Hp". iFrame. done.
  }
  iNext.
  iIntros "(Hs & Hi & Hq)".
  iApply "HΦ".
  iFrame.
  rewrite big_sepL_fmap.
  iApply (big_sepL_impl with "Hq"). iModIntro.
  iIntros (??) "% Hq".
  iDestruct "Hq" as (v) "[%Heq Hq]".
  apply IntoVal_inj in Heq. subst. done.
Qed.

End heap.
