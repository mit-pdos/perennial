From RecordUpdate Require Import RecordSet.
From Perennial.Helpers Require Import List Fractional.
From Perennial.goose_lang Require Import proofmode array.
From Perennial.goose_lang.lib Require Import persistent_readonly typed_mem.
From Perennial.goose_lang.lib Require Export slice.impl.
From Perennial.goose_lang.lib Require Import control.control.

Set Default Proof Using "Type".

Module Slice.
  Record t :=
    mk { ptr: loc;
         sz: u64;
         cap: u64; }.
  Global Instance _eta: Settable _ := settable! mk <ptr; sz; cap>.
  Global Instance _witness: Inhabited _ := populate (mk inhabitant inhabitant inhabitant).
  Notation extra s := (uint.Z (cap s) - uint.Z (sz s)).
  Definition nil := mk null (W64 0) (W64 0).
End Slice.
Add Printing Constructor Slice.t.

Section goose_lang.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.

Implicit Types (stk:stuckness) (E:coPset).
Implicit Types (v:val) (vs:list val).

Coercion slice_val (s: Slice.t) : val := (#s.(Slice.ptr), #s.(Slice.sz), #s.(Slice.cap)).
Definition val_slice v : option Slice.t :=
  match v with
  | (#(LitLoc ptr), #(LitInt sz), #(LitInt cap))%V => Some (Slice.mk ptr sz cap)
  | _ => None
  end.

Transparent slice.T.
Theorem slice_val_ty s t : val_ty (slice_val s) (slice.T t).
Proof.
  val_ty.
Qed.
Opaque slice.T.

(* own_slice_small is a smaller footprint version of own_slice that imprecisely
ignores the extra capacity; it allows for weaker preconditions for code which
doesn't make use of capacity *)
Definition own_slice_small (s: Slice.t) (t:ty) (dq:dfrac) (vs: list val): iProp Σ :=
  s.(Slice.ptr) ↦∗[t]{dq} vs ∗
  ⌜length vs = uint.nat s.(Slice.sz) ∧ uint.Z s.(Slice.sz) ≤ uint.Z s.(Slice.cap)⌝.

Definition own_slice_cap (s: Slice.t) (t:ty): iProp Σ :=
  (∃ extra, ⌜Z.of_nat (length extra) = Slice.extra s⌝ ∗
            (s.(Slice.ptr) +ₗ[t] uint.Z s.(Slice.sz)) ↦∗[t] extra).

Definition own_slice (s: Slice.t) (t:ty) (dq:dfrac) (vs: list val): iProp Σ :=
  own_slice_small s t dq vs ∗ own_slice_cap s t.

Lemma own_slice_to_small s t q vs :
  own_slice s t q vs -∗ own_slice_small s t q vs.
Proof.
  iDestruct 1 as "[$ _]".
Qed.

Lemma own_slice_split s t q vs :
  own_slice s t q vs ⊣⊢ own_slice_small s t q vs ∗ own_slice_cap s t.
Proof.
  rewrite /own_slice //.
Qed.

Lemma own_slice_small_acc s t q vs :
  own_slice s t q vs -∗ own_slice_small s t q vs ∗ (∀ vs', own_slice_small s t q vs' -∗ own_slice s t q vs').
Proof.
  iDestruct 1 as "[$ Hextra]".
  iDestruct "Hextra" as (extra Hlen) "Hextra".
  iIntros (vs') "Hs".
  iFrame "Hs".
  iExists _; by iFrame.
Qed.

Lemma own_slice_small_read s t q vs :
  own_slice s t q vs -∗ own_slice_small s t q vs ∗ (own_slice_small s t q vs -∗ own_slice s t q vs).
Proof.
  iIntros "Hs".
  iDestruct (own_slice_small_acc with "Hs") as "[$ Hupd]".
  iApply ("Hupd" $! vs).
Qed.

Lemma own_slice_of_small s t q vs :
  s.(Slice.sz) = s.(Slice.cap) ->
  own_slice_small s t q vs -∗ own_slice s t q vs.
Proof.
  destruct s; simpl; intros ->.
  rewrite /own_slice /=.
  iIntros "$".
  iExists nil.
  rewrite array_nil right_id.
  rewrite Z.sub_diag; auto.
Qed.

Lemma own_slice_small_sz s t q vs :
  own_slice_small s t q vs -∗ ⌜length vs = uint.nat s.(Slice.sz)⌝.
Proof.
  iIntros "(_&[%%]) !% //".
Qed.

Lemma own_slice_sz s t q vs :
  own_slice s t q vs -∗ ⌜length vs = uint.nat s.(Slice.sz)⌝.
Proof.
  iIntros "((_&[%%])&_) !% //".
Qed.

Lemma own_slice_small_frac_valid s t q vs :
  0 < ty_size t →
  0 < length vs →
  own_slice_small s t (DfracOwn q) vs -∗ ⌜(q ≤ 1)%Qp⌝.
Proof.
  iIntros (??) "[Ha _]".
  by iApply (array_frac_valid with "Ha").
Qed.

Lemma own_slice_frac_valid s t q vs :
  0 < ty_size t →
  0 < length vs →
  own_slice s t (DfracOwn q) vs -∗ ⌜(q ≤ 1)%Qp⌝.
Proof.
  iIntros (??) "Hs".
  iDestruct (own_slice_to_small with "Hs") as "Hs".
  by iApply (own_slice_small_frac_valid with "Hs").
Qed.

Lemma replicate_0 A (x:A) : replicate 0 x = [].
Proof. reflexivity. Qed.

Lemma own_slice_intro l t q (sz: u64) vs :
  l ↦∗[t]{q} vs -∗ ⌜length vs = uint.nat sz⌝ -∗
  own_slice (Slice.mk l sz sz) t q vs.
Proof.
  iIntros "H1 H2".
  iApply own_slice_of_small; first by auto.
  iFrame. iSplit; done.
Qed.

Theorem own_slice_elim s t q vs :
  own_slice s t q vs -∗ s.(Slice.ptr) ↦∗[t]{q} vs ∗ ⌜length vs = uint.nat s.(Slice.sz)⌝.
Proof.
  rewrite /own_slice.
  iIntros "[[Hs [%%]] _]".
  iFrame. done.
Qed.

Theorem own_slice_small_fractional s t vs :
  fractional.Fractional (λ q, own_slice_small s t (DfracOwn q) vs).
Proof. apply _. Qed.

Theorem own_slice_small_as_fractional s q t vs :
  fractional.AsFractional (own_slice_small s t (DfracOwn q) vs) (λ q, own_slice_small s t (DfracOwn q) vs) q.
Proof. split; auto; apply _. Qed.

Global Instance own_slice_small_as_pointsto s t vs :
  AsMapsTo (own_slice_small s t (DfracOwn 1) vs) (λ q, own_slice_small s t (DfracOwn q) vs).
Proof. constructor; auto; apply _. Qed.

Theorem own_slice_small_agree s t q1 q2 vs1 vs2 :
  own_slice_small s t q1 vs1 -∗
  own_slice_small s t q2 vs2 -∗
  ⌜vs1 = vs2⌝.
Proof.
  iIntros "[Hs1 [%%]] [Hs2 [%%]]".
  assert (length vs1 = length vs2) by congruence.
  iDestruct (array_agree with "Hs1 Hs2") as %->; auto.
Qed.

Global Instance own_slice_small_persistent s t vs : Persistent (own_slice_small s t DfracDiscarded vs).
Proof. apply _. Qed.

Lemma own_slice_small_persist s t dq vs:
  own_slice_small s t dq vs ==∗ own_slice_small s t DfracDiscarded vs.
Proof.
  rewrite /own_slice_small.
  iIntros "[Hs %Hl]".
  iMod (array_persist with "Hs") as "Hs".
  iModIntro.
  iFrame. done.
Qed.

Global Instance own_slice_small_timeless s t q vs :
  Timeless (own_slice_small s t q vs) := _.

Definition slice_val_fold (ptr: loc) (sz: u64) (cap: u64) :
  (#ptr, #sz, #cap)%V = slice_val (Slice.mk ptr sz cap) := eq_refl.

Theorem own_slice_small_not_null s bt q vs :
  bt ≠ unitBT ->
  length vs > 0 ->
  own_slice_small s (baseT bt) q vs -∗
  ⌜ s.(Slice.ptr) ≠ null ⌝.
Proof.
  iIntros (Hbt Hvs) "[Hs %]".
  destruct s; destruct vs; simpl in *; try lia.
  rewrite array_cons.
  iDestruct "Hs" as "[Hptr _]".
  rewrite base_pointsto_untype.
  2: { destruct bt; eauto. }
  iApply heap_pointsto_non_null.
  iDestruct "Hptr" as "[Hptr %]".
  iFrame.
Qed.

Theorem own_slice_not_null s bt q vs :
  bt ≠ unitBT ->
  length vs > 0 ->
  own_slice s (baseT bt) q vs -∗
  ⌜ s.(Slice.ptr) ≠ null ⌝.
Proof.
  iIntros (Hbt Hvs) "[Hs _]".
  iApply own_slice_small_not_null; last by iFrame.
  all: eauto.
Qed.

Theorem own_slice_cap_wf s t :
  own_slice_cap s t -∗ ⌜uint.Z s.(Slice.sz) ≤ uint.Z s.(Slice.cap)⌝.
Proof.
  iIntros "Hcap".
  iDestruct "Hcap" as (extra) "[% Hcap]".
  iPureIntro.
  word.
Qed.

Theorem own_slice_wf s t q vs :
  own_slice s t q vs -∗ ⌜uint.Z s.(Slice.sz) ≤ uint.Z s.(Slice.cap)⌝.
Proof.
  rewrite own_slice_split.
  iIntros "[Hs Hcap]".
  iDestruct (own_slice_cap_wf with "Hcap") as "$".
Qed.

Theorem own_slice_small_wf s t q vs :
  own_slice_small s t q vs -∗ ⌜uint.Z s.(Slice.sz) ≤ uint.Z s.(Slice.cap)⌝.
Proof.
  iIntros "[_ [%%]]". done.
Qed.

(* TODO: order commands so primitives are opaque only after proofs *)
Transparent raw_slice.

Lemma wp_make_cap stk E (sz: u64) :
  {{{ True }}}
    make_cap #sz @ stk; E
  {{{ (cap:u64), RET #cap; ⌜uint.Z cap >= uint.Z sz⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply wp_ArbitraryInt.
  iIntros (extra) "_".
  wp_pures.
  wp_if_destruct; try wp_pures; iApply "HΦ"; iPureIntro.
  - rewrite word.unsigned_add /word.wrap in Heqb.
    rewrite word.unsigned_add /word.wrap.
    word.
  - word.
Qed.

Lemma wp_raw_slice stk E l vs (sz: u64) t :
  {{{ l ↦∗[t] vs ∗ ⌜length vs = uint.nat sz⌝ }}}
    raw_slice t #l #sz @ stk; E
  {{{ sl, RET slice_val sl; own_slice sl t (DfracOwn 1) vs }}}.
Proof.
  iIntros (Φ) "(Hslice&%) HΦ".
  wp_call.
  rewrite slice_val_fold. iApply "HΦ".
  iApply (own_slice_intro with "Hslice").
  iPureIntro; auto.
Qed.

Lemma wp_slice_len stk E (s: Slice.t) (Φ: val -> iProp Σ) :
    Φ #(s.(Slice.sz)) -∗ WP slice.len (slice_val s) @ stk; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ".
  wp_call.
  iApply "HΦ".
Qed.

Lemma wp_slice_cap stk E (s: Slice.t) (Φ: val -> iProp Σ) :
    Φ #(s.(Slice.cap)) -∗ WP slice.cap (slice_val s) @ stk; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ".
  wp_call.
  iApply "HΦ".
Qed.

Lemma wp_slice_ptr stk E (s: Slice.t) (Φ: val -> iProp Σ) :
    Φ #(s.(Slice.ptr)) -∗ WP slice.ptr (slice_val s) @ stk; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ".
  wp_call.
  iApply "HΦ".
Qed.

Theorem own_slice_zero t q :
  ⊢ own_slice Slice.nil t q [].
Proof.
  iApply own_slice_of_small; first by auto.
  rewrite /own_slice_small /=.
  rewrite array_nil.
  rewrite left_id; auto.
Qed.

Theorem own_slice_small_nil t q s :
  uint.Z s.(Slice.sz) = 0 ->
  ⊢ own_slice_small s t q [].
Proof.
  intros Hsz.
  iSplit.
  - iApply array_nil; auto.
  - rewrite Hsz /=; auto. iPureIntro. split; word.
Qed.

Lemma own_slice_nil s t q :
  uint.Z s.(Slice.sz) = 0 ->
  uint.Z s.(Slice.cap) = 0 ->
  ⊢ own_slice s t q [].
Proof.
  destruct s as [ptr len cap]; simpl; intros.
  iSplitL.
  - iApply own_slice_small_nil; simpl; auto.
  - iExists []; simpl.
    iSplitL.
    + iPureIntro; lia.
    + iApply array_nil; auto.
Qed.

Lemma own_slice_cap_nil t :
  ⊢ own_slice_cap Slice.nil t.
Proof.
  iExists []; simpl.
  rewrite array_nil right_id.
  iPureIntro.
  word.
Qed.

Theorem zero_slice_val t :
  zero_val (slice.T t) = slice_val Slice.nil.
Proof.
  reflexivity.
Qed.

Lemma u64_val_ne (x1 x2:u64) :
  #x1 ≠ #x2 -> uint.Z x1 ≠ uint.Z x2.
Proof.
  intros Hne.
  intros Heq%word.unsigned_inj.
  congruence.
Qed.

Lemma array_replicate_split (n1 n2 n: nat) l t v :
  (n1 + n2 = n)%nat ->
  l ↦∗[t] replicate n v -∗
    l ↦∗[t] replicate n1 v ∗
    (l +ₗ[t] n1) ↦∗[t] replicate n2 v.
Proof.
  iIntros (<-) "Ha".
  iDestruct (array_split n1 with "Ha") as "[Ha1 Ha2]".
  { word. }
  { rewrite replicate_length.
    word. }
  rewrite take_replicate drop_replicate.
  rewrite -> Nat.min_l by word.
  iFrame.
  iSplitL "Ha1".
  - iExactEq "Ha1"; repeat (f_equal; try word).
  - iExactEq "Ha2"; repeat (f_equal; try word).
Qed.

Ltac word_eq :=
  repeat (f_equal; try word).

Lemma wp_new_slice s E t (sz: u64) :
  has_zero t ->
  {{{ True }}}
    NewSlice t #sz @ s; E
  {{{ sl, RET slice_val sl; own_slice sl t (DfracOwn 1) (replicate (uint.nat sz) (zero_val t)) }}}.
Proof.
  iIntros (Hzero Φ) "_ HΦ".
  wp_call.
  wp_if_destruct.
  - rewrite /slice.nil slice_val_fold.
    iApply "HΦ".
    rewrite replicate_0.
    iApply own_slice_zero.
  - wp_apply wp_make_cap.
    iIntros (cap Hcapge).
    wp_pures.
    wp_apply (wp_allocN t); eauto.
    { apply u64_val_ne in Heqb.
      change (uint.Z 0) with 0 in Heqb.
      word. }
  iIntros (l) "Hl".
  wp_pures.
  rewrite slice_val_fold. iApply "HΦ". rewrite /own_slice /own_slice_small /=.
  iDestruct (array_replicate_split (uint.nat sz) (uint.nat cap - uint.nat sz) with "Hl") as "[Hsz Hextra]";
    first by word.
  rewrite replicate_length.
  iFrame.
  iSplitR.
  { iPureIntro. split; word. }
  iExists (replicate (uint.nat cap - uint.nat sz) (zero_val t)); iFrame.
  iSplitR.
  { iPureIntro.
    rewrite replicate_length.
    simpl.
    word. }
  simpl. iModIntro.
  iExactEq "Hextra"; word_eq.
Qed.

Lemma wp_new_slice_cap s E t (sz cap: u64) :
  has_zero t →
  uint.Z sz ≤ uint.Z cap →
  {{{ True }}}
    NewSliceWithCap t #sz #cap @ s; E
  {{{ ptr, RET slice_val (Slice.mk ptr sz cap) ; own_slice (Slice.mk ptr sz cap) t (DfracOwn 1) (replicate (uint.nat sz) (zero_val t)) }}}.
Proof.
  iIntros (Hzero Hsz Φ) "_ HΦ".
  wp_call.
  rewrite ->bool_decide_false by lia.
  wp_if_destruct.
  - rewrite /slice.nil slice_val_fold.
    (* FIXME: why can [word] not prove [sz = 0] without this help? *)
    rewrite unsigned_U64_0 in Hsz.
    assert (sz = 0) as -> by word.
    iApply "HΦ".
    rewrite replicate_0.
    iApply own_slice_zero.
  - wp_apply (wp_allocN t); eauto.
    { apply u64_val_ne in Heqb.
      change (uint.Z 0) with 0 in Heqb.
      word. }
  iIntros (l) "Hl".
  wp_pures.
  rewrite slice_val_fold. iApply "HΦ". rewrite /own_slice /own_slice_small /=.
  iDestruct (array_replicate_split (uint.nat sz) (uint.nat cap - uint.nat sz) with "Hl") as "[Hsz Hextra]";
    first by word.
  rewrite replicate_length.
  iFrame.
  iSplitR.
  { iPureIntro. split; word. }
  iExists (replicate (uint.nat cap - uint.nat sz) (zero_val t)); iFrame.
  iSplitR.
  { iPureIntro.
    rewrite replicate_length.
    simpl.
    word. }
  simpl. iModIntro.
  iExactEq "Hextra"; word_eq.
Qed.

Theorem wp_SliceSingleton Φ stk E t x :
  val_ty x t ->
  (∀ s, own_slice s t (DfracOwn 1) [x] -∗ Φ (slice_val s)) -∗
  WP SliceSingleton x @ stk; E {{ Φ }}.
Proof.
  iIntros (Hty) "HΦ".
  wp_call.
  wp_apply (wp_allocN t); eauto.
  { word. }
  change (replicate (uint.nat 1) x) with [x].
  iIntros (l) "Hl".
  wp_steps.
  rewrite slice_val_fold. iApply "HΦ".
  iApply own_slice_of_small; first by auto.
  rewrite /own_slice_small /=.
  iFrame.
  auto.
Qed.

Definition slice_take (sl: Slice.t) (n: u64) : Slice.t :=
  {| Slice.ptr := sl.(Slice.ptr);
     Slice.sz := n;
     Slice.cap := sl.(Slice.cap);
  |}.

Definition slice_skip (sl: Slice.t) (t:ty) (n: u64) : Slice.t :=
  {| Slice.ptr := sl.(Slice.ptr) +ₗ[t] uint.Z n;
     Slice.sz := word.sub sl.(Slice.sz) n;
     Slice.cap := word.sub sl.(Slice.cap) n;
  |}.

Definition slice_subslice (sl: Slice.t) (t:ty) (n1 n2: u64) : Slice.t :=
  Slice.mk (sl.(Slice.ptr) +ₗ[t] uint.Z n1) (word.sub n2 n1) (word.sub sl.(Slice.cap) n1).

(* TODO: this theorem isn't true as-is for a correct model of splitting (the
above gets the capacities wrong) *)
(*
Lemma slice_split s (n: u64) t q vs :
  0 <= uint.Z n ->
  uint.nat n <= length vs ->
  own_slice s t q vs -∗ own_slice (slice_take s t n) t q (take (uint.nat n) vs) ∗
           own_slice (slice_skip s t n) t q (drop (uint.nat n) vs).
 *)

Theorem own_slice_take_cap s t vs n :
  uint.Z n <= length vs ->
  own_slice s t (DfracOwn 1) vs -∗
  own_slice (slice_take s n) t (DfracOwn 1) (take (uint.nat n) vs).
Proof.
  intros.
  rewrite /own_slice /own_slice_small /own_slice_cap /slice_take /=.
  rewrite -> firstn_length_le by lia.
  iIntros "[[Hsmall %] Hcap]".
  iDestruct "Hcap" as (extra) "[% Hcap]".
  iDestruct (array_split (uint.nat n) with "Hsmall") as "[Hsmall0 Hsmall1]"; try lia.
  word_cleanup.
  iSplitL "Hsmall0".
  - iFrame. iPureIntro. split; word.
  - iExists _. iSplitR.
    2: {
      iApply array_app. iFrame "Hsmall1".
      replace (uint.Z (Slice.sz s)) with (uint.Z n + length (drop (uint.nat n) vs)).
      2: { rewrite drop_length. lia. }
      rewrite Z.mul_add_distr_l -loc_add_assoc //.
    }
    iPureIntro.
    rewrite app_length drop_length. lia.
Qed.

Lemma slice_small_split s (n: u64) t q vs :
  uint.Z n <= length vs →
  own_slice_small s t q vs -∗ own_slice_small (slice_take s n) t q (take (uint.nat n) vs) ∗
           own_slice_small (slice_skip s t n) t q (drop (uint.nat n) vs).
Proof.
  iIntros (Hbounds) "Hs".
  iDestruct "Hs" as "[Ha %]".
  iDestruct (array_split (uint.nat n) with "Ha") as "[Ha1 Ha2]"; try lia.
  iSplitL "Ha1".
  - iSplit; simpl.
    + iExactEq "Ha1".
      repeat (f_equal; try word).
    + iPureIntro.
      rewrite take_length.
      word.
  - iSplit; simpl.
    + iExactEq "Ha2".
      repeat (f_equal; try word).
    + iPureIntro.
      rewrite drop_length.
      word.
Qed.

Theorem own_slice_small_take_drop s t q n vs :
  (uint.nat n <= uint.nat s.(Slice.sz))%nat ->
   own_slice_small (slice_skip s t n) t q (drop (uint.nat n) vs) ∗
   own_slice_small (slice_take s n) t q (take (uint.nat n) vs) ⊣⊢
  own_slice_small s t q vs.
Proof.
  intros Hbound.
  iSplit.
  - iIntros "(Hs1 & Hs2)".
    iDestruct "Hs1" as "[Ha1 %Hlen1]".
    iDestruct "Hs2" as "[Ha2 %Hlen2]".
    rewrite drop_length /= in Hlen1.
    rewrite take_length /= in Hlen2.
    iDestruct (array_split with "[$Ha1 $Ha2]") as "Ha"; try word.
    iFrame.
    iPureIntro.
    revert Hlen1; word.
  - iIntros "Hs".
    iDestruct "Hs" as "[Ha %Hlen]".
    iDestruct (array_split (uint.nat n) with "Ha") as "[Ha1 Ha2]"; try word.
    rewrite Z2Nat.id; try word.
    iFrame.
    iPureIntro; simpl.
    rewrite drop_length take_length; word.
Qed.

Theorem own_slice_small_take_drop_1 s t q n vs :
  (uint.nat n <= uint.nat s.(Slice.sz))%nat ->
  own_slice_small (slice_skip s t n) t q (drop (uint.nat n) vs) ∗
                  own_slice_small (slice_take s n) t q (take (uint.nat n) vs) -∗
  own_slice_small s t q vs.
Proof.
  intros Hbound.
  rewrite own_slice_small_take_drop; auto.
Qed.

Theorem own_slice_combine s t q n vs1 vs2 :
  (uint.nat n ≤ uint.nat s.(Slice.sz))%nat →
  own_slice_small (slice_take s n) t q vs1 ⊢@{_}
  own_slice_small (slice_skip s t n) t q vs2 -∗
  own_slice_small s t q (vs1 ++ vs2).
Proof.
  iIntros (Hbound) "Hs1 Hs2".
  assert (vs1 = take (length vs1) (vs1 ++ vs2)) as Hvs1.
  { rewrite take_app_le //.
    rewrite take_ge //. }
  assert (vs2 = drop (length vs1) (vs1 ++ vs2)) as Hvs2.
  { rewrite drop_app_ge //.
    rewrite Nat.sub_diag //. }
  iDestruct (own_slice_small_sz with "Hs1") as %Hsz1.
  iDestruct (own_slice_small_sz with "Hs2") as %Hsz2.
  simpl in Hsz1, Hsz2.
  iApply (own_slice_small_take_drop _ _ _ (W64 (length vs1))).
  { word. }
  replace (uint.nat (W64 (length vs1))) with (length vs1) by word.
  rewrite -> take_app_le by word.
  rewrite -> drop_app_ge, Nat.sub_diag by word.
  rewrite Hsz1.
  rewrite drop_0.
  rewrite -> take_ge by word.
  replace (W64 (uint.nat n)) with n; first by iFrame.
  apply (inj uint.Z).
  word.
Qed.

Lemma own_slice_split_acc n s t vs q :
  uint.Z n <= length vs →
  own_slice s t q vs -∗
  own_slice_small (slice_skip s t n) t q (drop (uint.nat n) vs) ∗
    (∀ vs', own_slice_small (slice_skip s t n) t q vs' -∗
            own_slice s t q (take (uint.nat n) vs ++ vs')).
Proof.
  iIntros (Hlen) "Hs".
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  iDestruct (own_slice_small_acc with "Hs") as "[Hs Hclose]".
  iDestruct (slice_small_split _ n with "Hs") as "[Hhead $]".
  { done. }
  iIntros (vs') "Htail". iApply "Hclose".
  iApply (own_slice_combine with "Hhead Htail").
  word.
Qed.

Theorem slice_skip_skip (n m: u64) s t :
  uint.Z m ≤ uint.Z n ≤ uint.Z s.(Slice.sz) ->
  uint.Z s.(Slice.sz) ≤ uint.Z s.(Slice.cap) ->
  slice_skip s t n =
  slice_skip (slice_skip s t m) t (word.sub n m).
Proof.
  intros Hbound Hwf.
  rewrite /slice_skip /=.
  f_equal.
  - rewrite !loc_add_assoc.
    f_equal.
    word_cleanup.
  - repeat word_cleanup.
  - repeat word_cleanup.
Qed.

Theorem own_slice_cap_skip s t n :
  uint.Z n ≤ uint.Z s.(Slice.sz) →
  own_slice_cap s t -∗
  own_slice_cap (slice_skip s t n) t.
Proof.
  iDestruct 1 as (extra) "[% Hextra]".
  rewrite /slice_skip.
  iExists extra; simpl.
  iSplit.
  { iPureIntro.
    word. }
  iExactEq "Hextra".
  rewrite loc_add_assoc.
  rewrite -Z.mul_add_distr_l.
  repeat (f_equal; try word).
Qed.

Theorem own_slice_cap_skip_more s n1 n2 t :
  uint.Z n1 ≤ uint.Z n2 ≤ uint.Z s.(Slice.sz) ->
  uint.Z s.(Slice.sz) ≤ uint.Z s.(Slice.cap) ->
  own_slice_cap (slice_skip s t n1) t -∗ own_slice_cap (slice_skip s t n2) t.
Proof.
  iIntros (Hbound Hwf) "Hcap".
  rewrite (slice_skip_skip n2 n1); try (repeat word_cleanup).
  iApply (own_slice_cap_skip with "Hcap"); simpl; try word.
Qed.

Theorem slice_skip_take_commute s t n1 n2 :
  slice_skip (slice_take s n1) t n2 =
  slice_take (slice_skip s t n2) (word.sub n1 n2).
Proof.
  intros.
  destruct s as [ptr len cap]; simpl.
  rewrite /slice_take /slice_skip; simpl.
  f_equal.
Qed.

(** * Hoare triples *)

Lemma wp_SliceSkip Φ stk E s t (n: u64):
  uint.Z n ≤ uint.Z s.(Slice.sz) →
  ▷ Φ (slice_val (slice_skip s t n)) -∗
  WP (SliceSkip t (slice_val s) #n) @ stk; E {{ Φ }}.
Proof.
  iIntros "% HΦ".
  wp_call.
  wp_call.
  wp_call.
  wp_call.
  iApply "HΦ".
Qed.

Lemma wp_SliceSkip_small s t q vs (n : u64) :
  uint.Z n ≤ length vs →
  {{{ own_slice_small s t q vs }}}
    SliceSkip t (slice_val s) #n
  {{{ s', RET (slice_val s'); own_slice_small s' t q (drop (uint.nat n) vs) }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  iApply wp_SliceSkip.
  { word. }
  iApply "HΦ". iNext.
  iDestruct (own_slice_small_take_drop _ _ _ n with "Hs") as "[$ _]".
  word.
Qed.

Lemma wp_SliceTake {Φ stk E s} (n: u64):
  uint.Z n ≤ uint.Z s.(Slice.cap) →
  ▷ Φ (slice_val (slice_take s n)) -∗
  WP (SliceTake (slice_val s) #n) @ stk; E {{ Φ }}.
Proof.
  iIntros (?) "HΦ".
  wp_call.
  wp_call.
  wp_if_destruct.
  - wp_apply wp_panic.
    word.
  - wp_call.
    wp_call.
    iApply "HΦ".
Qed.

Lemma wp_SliceTake_small {stk E s} t q vs (n: u64):
  uint.Z n ≤ length vs →
  {{{ own_slice_small s t q vs }}}
    SliceTake (slice_val s) #n @ stk; E
  {{{ RET (slice_val (slice_take s n)); own_slice_small (slice_take s n) t q (take (uint.nat n) vs) }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  iDestruct (own_slice_small_wf with "Hs") as %Hwf.
  wp_apply (wp_SliceTake).
  { word. }
  iApply "HΦ".
  iDestruct (own_slice_small_take_drop _ _ _ n with "Hs") as "[_ $]".
  word.
Qed.

(** We have full ownership, and take into the capacity.
Cannot be typed, since [extra] might not be valid at this type. *)
Lemma wp_SliceTake_full_cap {stk E s} t vs (n: u64):
  uint.Z s.(Slice.sz) ≤ uint.Z n ≤ uint.Z s.(Slice.cap) →
  {{{ own_slice s t (DfracOwn 1) vs }}}
    SliceTake (slice_val s) #n @ stk; E
  {{{ extra, RET (slice_val (slice_take s n));
    ⌜length extra = uint.nat n - uint.nat (s.(Slice.sz))⌝%nat ∗
    own_slice (slice_take s n) t (DfracOwn 1) (vs ++ extra)
  }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  wp_apply (wp_SliceTake).
  { word. }
  iDestruct "Hs" as "[Hs [%extra [%Hextra Hextra]]]".
  set elen := (uint.nat n - uint.nat (s.(Slice.sz)))%nat.
  iApply ("HΦ" $! (take elen extra)).
  iSplit.
  { iPureIntro. rewrite take_length. word. }
  rewrite -{1}(take_drop elen extra) array_app.
  iDestruct "Hextra" as "[He1 He2]".
  iSplitL "Hs He1".
  - rewrite /own_slice_small /= array_app. iDestruct "Hs" as "[$ _]".
    iSplit. { iExactEq "He1". word_eq. }
    iPureIntro. split; last word.
    rewrite app_length take_length. word.
  - iExists _. iSplit; last first.
    + iExactEq "He2". f_equal.
      rewrite loc_add_assoc. f_equal.
      rewrite take_length /slice_take /=.
      rewrite ->Nat.min_l by word.
      rewrite -Z.mul_add_distr_l. f_equal. word.
    + iPureIntro. rewrite drop_length /slice_take /=. word.
Qed.

Lemma wp_SliceSubslice Φ stk E s t (n1 n2: u64):
  uint.Z n1 ≤ uint.Z n2 ∧ uint.Z n2 ≤ uint.Z s.(Slice.cap) →
  ▷ Φ (slice_val (slice_subslice s t n1 n2)) -∗
  WP (SliceSubslice t (slice_val s) #n1 #n2) @ stk; E {{ Φ }}.
Proof.
  iIntros "% HΦ".
  wp_call.
  wp_if_destruct.
  - word.
  - wp_call.
    wp_if_destruct.
    + exfalso.
      word.
    + wp_call. wp_call.
      iApply "HΦ".
Qed.

Lemma own_slice_small_skipn s t q vs n:
  ⌜uint.Z n ≤ uint.Z s.(Slice.sz)⌝ -∗
  own_slice_small s t q vs -∗
  own_slice_small (Slice.mk (s.(Slice.ptr) +ₗ[t] uint.Z n)
                           (word.sub s.(Slice.sz) n)
                           (word.sub s.(Slice.cap) n)) t q (skipn (uint.nat n) vs).
Proof.
  iIntros "% [Hs %]".
  iSplitL; simpl.
  2: {
    iPureIntro.
    rewrite skipn_length.
    word.
  }

  replace vs with (firstn (uint.nat n) vs ++ skipn (uint.nat n) vs) at 1 by apply firstn_skipn.

  rewrite array_app.
  iDestruct "Hs" as "[Hs0 Hs1]".
  rewrite -> firstn_length_le by lia.
  replace (Z.of_nat (uint.nat n)) with (uint.Z n) by word.
  iFrame.
Qed.

Lemma own_slice_small_firstn s t q vs n:
  ⌜uint.Z n ≤ uint.Z s.(Slice.sz)⌝ -∗
  own_slice_small s t q vs -∗
  own_slice_small (Slice.mk s.(Slice.ptr) n s.(Slice.cap)) t q (firstn (uint.nat n) vs).
Proof.
  iIntros "% [Hs %]".
  iSplitL; simpl.
  2: {
    iPureIntro.
    rewrite firstn_length.
    word.
  }

  replace vs with (firstn (uint.nat n) vs ++ skipn (uint.nat n) vs) at 1 by apply firstn_skipn.

  rewrite array_app.
  iDestruct "Hs" as "[Hs0 Hs1]".
  iFrame.
Qed.

Lemma own_slice_small_subslice s t q vs n1 n2:
  uint.Z n1 ≤ uint.Z n2 ∧ uint.Z n2 ≤ uint.Z s.(Slice.sz) →
  own_slice_small s t q vs -∗
  own_slice_small (Slice.mk (s.(Slice.ptr) +ₗ[t] uint.Z n1)
                           (word.sub n2 n1) (word.sub s.(Slice.cap) n1)) t q
                 (skipn (uint.nat n1) (firstn (uint.nat n2) vs)).
Proof.
  iIntros "% Hs".
  iDestruct (own_slice_small_firstn _ _ _ _ n2 with "[] Hs") as "Hs".
  { iPureIntro; lia. }
  iDestruct (own_slice_small_skipn _ _ _ _ n1 with "[] Hs") as "Hs".
  { iPureIntro; simpl; lia. }
  simpl. iFrame.
Qed.

Lemma wp_SliceSubslice_small stk E s t (n1 n2: u64) q vs:
  {{{
    own_slice_small s t q vs ∗
    ⌜uint.Z n1 ≤ uint.Z n2 ∧ uint.Z n2 ≤ uint.Z s.(Slice.sz)⌝
  }}}
    SliceSubslice t (slice_val s) #n1 #n2 @ stk; E
  {{{
    (s': Slice.t), RET (slice_val s');
    own_slice_small s' t q (skipn (uint.nat n1) (firstn (uint.nat n2) vs))
  }}}.
Proof.
  iIntros (Φ) "[Hs [%%]] HΦ".
  iDestruct (own_slice_small_wf with "Hs") as %Hwf.
  iApply wp_SliceSubslice.
  { word. }
  iApply "HΦ".
  iModIntro.
  iApply own_slice_small_subslice.
  { word. }
  iFrame.
Qed.

Lemma wp_SliceGet_body stk E sl t q vs (i: u64) v0 :
  {{{ own_slice_small sl t q vs ∗ ⌜ vs !! uint.nat i = Some v0 ⌝ }}}
    ![t] (slice.ptr (sl) +ₗ[t] #i) @ stk; E
  {{{ RET v0; own_slice_small sl t q vs ∗ ⌜val_ty v0 t⌝ }}}.
Proof.
  iIntros (Φ) "[Hsl %] HΦ".
  destruct sl as [ptr sz].
  repeat wp_step.
  rewrite /own_slice_small /=.
  iDestruct "Hsl" as "(Hsl&%)"; simpl.
  repeat wp_call.
  iDestruct (array_elem_acc H with "Hsl") as "[Hi Hsl']".
  pose proof (word.unsigned_range i).
  word_cleanup.
  iDestruct (struct_pointsto_ty with "Hi") as %Hty.
  wp_load.
  iSpecialize ("Hsl'" with "Hi").
  iApply "HΦ"; iFrame.
  iPureIntro; auto.
Qed.


Lemma wp_SliceGet stk E sl t q vs (i: u64) v0 :
  {{{ own_slice_small sl t q vs ∗ ⌜ vs !! uint.nat i = Some v0 ⌝ }}}
    SliceGet t sl #i @ stk; E
  {{{ RET v0; own_slice_small sl t q vs ∗ ⌜val_ty v0 t⌝ }}}.
Proof.
  iIntros (Φ) "[Hsl %] HΦ".
  destruct sl as [ptr sz].
  rewrite /SliceGet.
  repeat wp_step.
  wp_apply (wp_SliceGet_body with "[Hsl]"); last done.
  { iFrame. eauto. }
Qed.

Lemma list_lookup_Z_lt {A} (l: list A) (i: Z) :
  (0 <= i < Z.of_nat (length l)) ->
  exists x, l !! Z.to_nat i = Some x.
Proof.
  intros.
  apply list_lookup_lt.
  apply Nat2Z.inj_le; lia.
Qed.

Theorem wp_forSlice_mut (I: u64 -> iProp Σ) stk E s t q vs (body: val) :
  □ (∀ (i: u64),
        I i -∗ ∃ vs', ⌜ length vs' = length vs ⌝ ∗
                      ⌜ vs' !! uint.nat i = vs !! uint.nat i ⌝ ∗
                      own_slice_small s t q vs' ∗
                      (own_slice_small s t q vs' -∗ I i)) -∗
  (∀ (i: u64) (x: val),
      {{{ I i ∗ ⌜uint.Z i < uint.Z s.(Slice.sz)⌝ ∗
                ⌜vs !! uint.nat i = Some x⌝ }}}
        body #i x @ stk; E
      {{{ (v : val), RET v; I (word.add i (W64 1)) }}}) -∗
    {{{ I (W64 0) }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); I s.(Slice.sz) }}}.
Proof.
  iIntros "#Hslice_acc #Hind".
  iIntros (Φ) "!> Hi0 HΦ".
  wp_call.
  wp_apply wp_slice_len.
  wp_steps.
  remember 0 as z.
  assert (0 <= z <= uint.Z s.(Slice.sz)) by word.
  iDestruct ("Hslice_acc" with "[$]") as (vs' Hlen' Hlookup') "(Hs&Hclo)".
  iDestruct (own_slice_small_sz with "Hs") as %Hslen.
  clear Heqz; generalize dependent z.
  intros z Hzrange Hlookup'.
  pose proof (word.unsigned_range s.(Slice.sz)).
  assert (uint.Z (W64 z) = z) by (rewrite /W64; word).
  iDestruct ("Hclo" with "[$]") as "Hi0".
  iRename "Hi0" into "Hiz".
  rewrite Hlen' in Hslen.
  clear vs' Hlen' Hlookup'.
  (iLöb as "IH" forall (z Hzrange H0) "Hiz").
  wp_if_destruct.
  - destruct (list_lookup_Z_lt vs z) as [xz Hlookup]; first word.
    iDestruct ("Hslice_acc" with "[$]") as (vs' Hlen' Hlookup') "(Hs&Hclo)".
    wp_apply (wp_SliceGet with "[$Hs]").
    { rewrite Hlookup'. replace (uint.Z z); eauto. }
    iIntros "[Hs Hty]".
    iDestruct "Hty" as %Hty.
    wp_steps.
    iDestruct ("Hclo" with "[$]") as "Hiz".
    wp_apply ("Hind" with "[$Hiz]").
    { iPureIntro; split; eauto.
      replace (uint.Z z); eauto. }
    iIntros (v) "Hiz1".
    wp_steps.
    assert (uint.Z (z + 1) = uint.Z z + 1).
    { rewrite word.unsigned_of_Z.
      rewrite wrap_small; try lia. }
    replace (word.add z 1) with (W64 (z + 1)) by word.
    iSpecialize ("IH" $! (z+1) with "[] []").
    { iPureIntro; lia. }
    { iPureIntro; lia. }
    wp_apply ("IH" with "HΦ Hiz1").
  - assert (z = uint.Z s.(Slice.sz)) by lia; subst z.
    iApply "HΦ"; iFrame.
    replace (W64 (uint.Z s.(Slice.sz))) with s.(Slice.sz); auto.
    unfold W64.
    rewrite word.of_Z_unsigned; auto.
Qed.

Theorem wp_forSlice (I: u64 -> iProp Σ) stk E s t q vs (body: val) :
  (∀ (i: u64) (x: val),
      {{{ I i ∗ ⌜uint.Z i < uint.Z s.(Slice.sz)⌝ ∗
                ⌜vs !! uint.nat i = Some x⌝ }}}
        body #i x @ stk; E
      {{{ (v : val), RET v; I (word.add i (W64 1)) }}}) -∗
    {{{ I (W64 0) ∗ own_slice_small s t q vs }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); I s.(Slice.sz) ∗ own_slice_small s t q vs }}}.
Proof.
  iIntros "#Hind".
  iApply (wp_forSlice_mut (λ i, I i ∗ own_slice_small s t q vs)%I).
  { iModIntro. iIntros (?) "(Hi&Hs)".
    iExists vs. iFrame. eauto. }
  iIntros.
  iIntros (Φ) "!> [[Hi0 Hs] %] HΦ".
  wp_apply ("Hind" with "[$Hi0 //] [HΦ Hs]").
  { iNext. iIntros. iApply "HΦ". iFrame. }
Qed.

Theorem wp_forSlicePrefix (P: list val -> list val -> iProp Σ) stk E s t q vs (body: val) :
  (∀ (i: u64) (x: val) (vs: list val) (vs': list val),
      {{{ P vs (x :: vs') }}}
        body #i x @ stk; E
      {{{ (v : val), RET v; P (vs ++ [x]) vs' }}}) -∗
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
    wp_apply ("Hind" with "[HP]").
    { eapply drop_S in H0. rewrite H0. iFrame. }
    iIntros (v) "HP".
    iApply "HΦ0".
    iExactEq "HP". f_equal.
    { apply take_S_r in H0. rewrite -H0. f_equal. word. }
    f_equal. word.
  }

  iModIntro. iIntros "[HP Hs]".
  iDestruct (own_slice_small_sz with "Hs") as %<-.
  iApply "HΦ". iFrame.
  rewrite firstn_all.
  rewrite drop_all. done.
Qed.

Theorem wp_forSliceEach (I: iProp Σ) (P Q: val -> iProp Σ) stk E s t q vs (body: val) :
  (∀ (i: u64) (x: val),
      {{{ I ∗ P x }}}
        body #i x @ stk; E
      {{{ (v : val), RET v; I ∗ Q x }}}) -∗
    {{{ own_slice_small s t q vs ∗ I ∗ [∗ list] x ∈ vs, P x }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); own_slice_small s t q vs ∗ I ∗ [∗ list] x ∈ vs, Q x }}}.
Proof.
  iIntros "#Hind".
  iIntros (Φ) "!> [Hs [Hi Hp]] HΦ".
  iDestruct (own_slice_small_sz with "Hs") as %Hlen.
  wp_apply (wp_forSlice
    (λ i, ([∗ list] x ∈ firstn (uint.nat i) vs, Q x) ∗
          ([∗ list] x ∈ skipn (uint.nat i) vs, P x) ∗
          I)%I with "[] [$Hs Hi Hp]").
  {
    iIntros (i x).
    iModIntro.
    iIntros (Φ0) "[(Hq & Hp & Hi) [% %]] HΦ0".
    apply take_drop_middle in H0.
    replace (uint.nat (word.add i 1)) with (S (uint.nat i)) by word.
    assert (length (take (uint.nat i) vs) = uint.nat i) as Hivs.
    { rewrite take_length. lia. }
    replace (drop (uint.nat i) vs) with (x :: drop (S (uint.nat i)) vs).
    2: {
      rewrite <- H0 at 2.
      rewrite drop_app_length'; eauto.
    }
    iDestruct "Hp" as "[Hpx Hp]".
    iApply ("Hind" with "[$Hi $Hpx]").
    iModIntro.
    iIntros (v) "[Hi Hqx]".
    iApply "HΦ0".
    replace (take (S (uint.nat i)) vs) with ((take (uint.nat i) vs) ++ [x]).
    2: {
      rewrite <- H0 at 2.
      rewrite firstn_app Hivs.
      rewrite (firstn_all2 (take _ _)); last lia.
      f_equal.
      replace (S (uint.nat i) - uint.nat i)%nat with 1%nat by lia.
      rewrite /= firstn_O.
      reflexivity.
    }
    rewrite big_sepL_app /=.
    iFrame.
  }
  {
    repeat replace (uint.nat 0) with 0%nat by reflexivity.
    rewrite drop_0 /=.
    iFrame.
  }
  rewrite -Hlen skipn_all firstn_all /=.
  iIntros "[(Hq & _ & Hi) Hs]".
  iApply "HΦ"; iFrame.
Qed.

Lemma u64_nat_0 (n: u64) : 0%nat = uint.nat n -> n = W64 0.
Proof.
  intros.
  apply (f_equal Z.of_nat) in H.
  rewrite u64_Z_through_nat in H.
  apply word.unsigned_inj.
  rewrite <- H.
  reflexivity.
Qed.

Lemma wp_MemCpy_rec s E t q dst vs1 src vs2 (n: u64) :
  {{{ dst ↦∗[t] vs1 ∗ src ↦∗[t]{q} vs2 ∗
            ⌜ length vs1 = uint.nat n /\ length vs2 >= length vs1 ⌝ }}}
    MemCpy_rec t #dst #src #n @ s; E
  {{{ RET #(); dst ↦∗[t] (take (uint.nat n) vs2) ∗ src ↦∗[t]{q} vs2 }}}.
Proof.
  iIntros (Φ) "(Hdst&Hsrc&Hbounds) HΦ".
  iDestruct "Hbounds" as %(Hvs1&Hvs2).
  (iLöb as "IH" forall (vs1 vs2 n dst src Hvs1 Hvs2) "Hdst Hsrc HΦ").
  wp_call.
  wp_if_destruct.
  - change (uint.nat 0) with 0%nat.
    iEval (rewrite firstn_O array_nil) in "HΦ" .
    iApply "HΦ"; by iFrame.
  - apply u64_val_ne in Heqb.
    change (uint.Z 0) with 0 in *.
    destruct vs1, vs2; simpl in Hvs1, Hvs2; try word.
    iDestruct (array_cons with "Hdst") as "[Hdst Hvs1]".
    iDestruct (array_cons with "Hsrc") as "[Hsrc Hvs2]".
    wp_load.
    wp_bind (store_ty _ _).
    iDestruct (struct_pointsto_ty with "Hsrc") as %Hv0ty.
    wp_store.
    wp_pures.
    rewrite Z.mul_1_r.
    wp_apply ("IH" $! vs1 vs2 with "[] [] [Hvs1] [Hvs2]");
      iFrame;
      try iPureIntro.
    + word.
    + word.
    + iIntros "(Hdst'&Hsrc')".
      iApply "HΦ".
      rewrite array_cons; iFrame.
      replace (take (uint.nat n) (v0 :: vs2)) with
          (v0 :: take (uint.nat n - 1) vs2).
      { replace (uint.nat n - 1)%nat with (uint.nat (word.sub n 1)) by word.
        rewrite array_cons; iFrame. }
      replace (uint.nat n) with (1 + (uint.nat n - 1))%nat at 2 by lia.
      auto.
Qed.

Lemma wp_SliceCopy_full stk E sl t q vs dst vs' :
  {{{ own_slice_small sl t q vs ∗ own_slice_small dst t (DfracOwn 1) vs' ∗ ⌜length vs = length vs'⌝ }}}
    SliceCopy t (slice_val dst) (slice_val sl) @ stk; E
  {{{ RET #(W64 (length vs)); own_slice_small sl t q vs ∗ own_slice_small dst t (DfracOwn 1) vs }}}.
Proof.
  iIntros (Φ) "(Hsrc&Hdst&%) HΦ".
  wp_call.
  iDestruct "Hsrc" as "[Hsrc %]".
  iDestruct "Hdst" as "[Hdst %]".
  assert (sl.(Slice.sz) = dst.(Slice.sz)) by word.
  wp_apply wp_slice_len.
  wp_apply wp_slice_len.
  wp_bind (If _ _ _).
  wp_pures.
  wp_if_destruct; first by word.
  wp_apply wp_slice_len.
  wp_pures.
  rewrite /slice.ptr; wp_pures.
  wp_apply (wp_MemCpy_rec with "[$Hsrc $Hdst]").
  { iPureIntro.
    word. }
  iIntros "(Hdst & Hsrc)".
  wp_pures.
  replace (Slice.sz sl) with (W64 (length vs)) by word.
  iApply "HΦ".
  rewrite -> take_ge by word.
  iFrame.
  iPureIntro; word.
Qed.

Global Opaque SliceCopy.

Transparent SliceAppend.
Transparent SliceAppendSlice.

Lemma replicate_singleton {A} (x:A) :
  replicate 1 x = [x].
Proof. reflexivity. Qed.

Lemma array_split_1n l q t vs :
  (1 ≤ length vs)%nat ->
  l ↦∗[t]{q} vs -∗ ∃ v vs', l ↦[t]{q} v ∗ (l +ₗ ty_size t) ↦∗[t]{q} vs' ∗ ⌜vs = v::vs'⌝.
Proof.
  iIntros (Hlen).
  destruct vs.
  { simpl in Hlen; lia. }
  rewrite array_cons.
  iIntros "[Hl Hrest]".
  iExists v, vs; iFrame.
  auto.
Qed.

Lemma wp_SliceAppend'' stk E s t vs1 vs2 x (q : Qp) (n : u64) :
  has_zero t ->
  val_ty x t ->
  0 ≤ uint.Z n ≤ uint.Z (Slice.sz s) ≤ uint.Z (Slice.cap s) ->
  (q < 1)%Qp ->
  {{{ own_slice_small (slice_take s n) t (DfracOwn q) vs1 ∗
      own_slice (slice_skip s t n) t (DfracOwn 1) vs2 }}}
    SliceAppend t s x @ stk; E
  {{{ s', RET slice_val s';
      own_slice_small (slice_take s' n) t (DfracOwn q) vs1 ∗
      own_slice (slice_skip s' t n) t (DfracOwn 1) (vs2 ++ [x]) ∗
      ⌜uint.Z (Slice.sz s') ≤ uint.Z (Slice.cap s') ∧
       uint.Z (Slice.sz s') = (uint.Z (Slice.sz s) + 1)%Z ⌝}}}.
Proof.
  iIntros (Hzero Hty Hn Hq Φ) "[Hprefix Hs] HΦ".
  wp_call.
  wp_apply wp_slice_len.
  wp_apply wp_Assume.
  iIntros (Hbound).
  apply bool_decide_eq_true in Hbound.
  assert (uint.Z s.(Slice.sz) + 1 < 2^64) by word.
  wp_pures.
  wp_apply wp_slice_len.
  wp_pures.
  wp_lam; wp_pures.
  wp_apply wp_slice_len; wp_pures.
  iDestruct "Hs" as "((Hptr&[%Hlen %Hcap])&Hfree)".
  iDestruct "Hprefix" as "(Hprefix&[%Hlen' %Hcap'])".
  iDestruct (own_slice_cap_wf with "Hfree") as "%Hfreelen".
  iDestruct "Hfree" as (extra Hextralen) "Hfree".
  wp_if_destruct.
  - wp_call.
    rewrite word.unsigned_sub in Heqb.
    unfold slice_skip, slice_take in *; simpl in *.
    rewrite -> wrap_small in Heqb.
    2: { word. }
    iDestruct (array_split_1n with "Hfree") as (x0 extra') "(Hnew&Hfree&->)".
    { revert Hextralen. word. }
    simpl in Hextralen.
    wp_call.
    wp_pures.
    rewrite loc_add_assoc.
    rewrite -Z.mul_add_distr_l.
    replace (uint.Z n + uint.Z (word.sub (Slice.sz s) n))
      with (uint.Z (Slice.sz s)) by word.
    wp_apply (wp_StoreAt with "Hnew"); [ auto | iIntros "Hnew" ].
    wp_pures.
    wp_call.
    rewrite slice_val_fold. iApply "HΦ". rewrite /own_slice /=.
    iDestruct (array_app _ _ _ vs2 [x] with "[$Hptr Hnew]") as "Hptr".
    { rewrite array_singleton.
      rewrite Hlen.
      rewrite loc_add_assoc.
      rewrite -Z.mul_add_distr_l.
      replace (uint.Z n + uint.nat (word.sub (Slice.sz s) n))
        with (uint.Z (Slice.sz s)) by word.
      iExactEq "Hnew"; f_equal.
    }
    iFrame.
    iSplitR.
    { rewrite Hlen' /=. done. }
    iSplitL.
    2: { iPureIntro. word. }
    iSplitR.
    { rewrite app_length Hlen /=.
      iPureIntro.
      (* XXX why twice? *)
      repeat word_cleanup.
    }
    iExists extra'.
    simpl.
    iSplitR.
    { iPureIntro.
      revert Hextralen. repeat word_cleanup.
    }
    rewrite ?loc_add_assoc. iModIntro.
    iExactEq "Hfree". f_equal. f_equal.
    repeat word_cleanup.

  - wp_apply wp_make_cap.
    iIntros (cap Hcapgt).
    rewrite word.unsigned_add in Hcapgt.
    rewrite -> wrap_small in Hcapgt by word.
    wp_apply (wp_allocN t); auto.
    { word. }
    iIntros (l) "Halloc".
    iDestruct (array_replicate_split (uint.nat s.(Slice.sz) + 1) (uint.nat cap - uint.nat s.(Slice.sz) - 1) with "Halloc") as "[Halloc HnewFree]";
      first by word.
    iDestruct (array_replicate_split (uint.nat s.(Slice.sz)) 1%nat with "Halloc") as "[Halloc_sz Halloc1]";
      first by word.
    rewrite array_singleton.
    wp_pures.
    wp_call.
    wp_call.

    iDestruct (as_fractional_weaken q with "Hptr") as "Hptr".
    { apply Qp.lt_le_incl. eauto. }

    iDestruct (array_app with "[Hprefix Hptr]") as "Hptr".
    { rewrite /slice_take /slice_skip /=.
      iFrame "Hprefix".
      rewrite Hlen' /=.
      iExactEq "Hptr". f_equal. f_equal. f_equal. word.
    }

    wp_apply (wp_MemCpy_rec with "[$Halloc_sz $Hptr]").
    { iPureIntro.
      rewrite replicate_length.
      intuition try word.
      rewrite app_length Hlen Hlen'.
      rewrite /slice_take /slice_skip /=. word.
    }
    iIntros "[Hvs Hsrc]".
    rewrite firstn_all2.
    2: {
      rewrite app_length Hlen Hlen'.
      rewrite /slice_take /slice_skip /=. word.
    }

    wp_pures.
    wp_call.
    wp_apply (wp_StoreAt with "[Halloc1]"); [ val_ty | | iIntros "Hlast" ].
    { iModIntro. iExactEq "Halloc1"; word_eq. }
    wp_pures.

    rewrite slice_val_fold. iApply "HΦ". rewrite /own_slice /own_slice_small /=.
    rewrite array_app.
    iDestruct "Hvs" as "[Hprefix Hvs]".
    iDestruct (as_fractional_weaken q with "Hprefix") as "Hprefix".
    { eapply Qp.lt_le_incl. eauto. }

    iFrame "Hprefix".
    iSplitR.
    { iPureIntro. split; first done. word. }

    iSplitL.
    2: { iPureIntro. word. }

    iSplitL "Hvs Hlast".
    { iSplitL.
      * rewrite array_app array_singleton.
        replace (length vs1) with (uint.nat n) by done.
        replace (uint.nat n : Z) with (uint.Z n) by word.
        iFrame. iModIntro.
        rewrite loc_add_assoc.
        iExactEq "Hlast"; word_eq.
        replace (uint.Z n) with (uint.nat n : Z) by word.
        replace (uint.nat n) with (length vs1) by done.
        rewrite Hlen Hlen'.
        rewrite /slice_take /slice_skip /=. word.
      * iPureIntro.
        rewrite app_length /=.
        rewrite Hlen /slice_skip /=.
        word_cleanup. word_cleanup.
    }

    iExists (replicate (uint.nat cap - uint.nat s.(Slice.sz) - 1) (zero_val t)).
    iSplitR.
    { rewrite replicate_length.
      iPureIntro.
      simpl.
      word_cleanup. word_cleanup. }
    simpl. iModIntro.
    iExactEq "HnewFree".
    rewrite loc_add_assoc.
    word_eq.
    replace (uint.Z n) with (uint.nat n : Z) by word.
    replace (uint.nat n) with (length vs1) by done.
    rewrite Hlen'.
    rewrite /slice_take /=.
    word_cleanup. word_cleanup.
    replace (ty_size t * uint.Z n + ty_size t * (uint.Z (Slice.sz s) + 1 - uint.Z n))
       with (ty_size t * ( uint.Z n + ( (uint.Z (Slice.sz s) + 1 - uint.Z n) ) ) ) by lia.
    word_eq.
Qed.

Lemma wp_SliceAppend' stk E s t vs x :
   has_zero t ->
   val_ty x t ->
  {{{ own_slice s t (DfracOwn 1) vs }}}
     SliceAppend t s x @ stk; E
  {{{ s', RET slice_val s'; own_slice s' t (DfracOwn 1) (vs ++ [x]) }}}.
Proof.
  iIntros (Hzero Hty Φ) "Hs HΦ".
  iDestruct (own_slice_cap_wf with "[Hs]") as "%Hcap".
  { rewrite /own_slice. iDestruct "Hs" as "[_ $]". }
  wp_apply (wp_SliceAppend'' _ _ _ _ nil _ _ (1/2)%Qp 0 with "[Hs]"); try eassumption.
  3: {
    rewrite /slice_take /slice_skip.
    replace (word.sub (Slice.sz s) 0) with (Slice.sz s) by word.
    replace (word.sub (Slice.cap s) 0) with (Slice.cap s) by word.
    iSplitR "Hs".
    2: { iExactEq "Hs". f_equal. destruct s; simpl; f_equal. replace (ty_size t * uint.Z 0) with 0 by word.
      rewrite loc_add_0. done. }
    rewrite /own_slice_small /=.
    rewrite array_nil. iPureIntro. word.
  }
  { word. }
  { eapply (Qextra.Qp_div_2_lt 1). }
  iIntros (s') "(_ & Hs & _)".
  rewrite /slice_skip.
  replace (word.sub (Slice.sz s') 0) with (Slice.sz s') by word.
  replace (word.sub (Slice.cap s') 0) with (Slice.cap s') by word.
  iApply "HΦ".
  iExactEq "Hs". f_equal. destruct s'; simpl; f_equal.
  replace (ty_size t * uint.Z 0) with 0 by word.
  rewrite loc_add_0. done.
Qed.

Lemma wp_SliceAppend stk E s t vs x :
  has_zero t ->
  {{{ own_slice s t (DfracOwn 1) vs ∗ ⌜val_ty x t⌝ }}}
    SliceAppend t s x @ stk; E
  {{{ s', RET slice_val s'; own_slice s' t (DfracOwn 1) (vs ++ [x]) }}}.
Proof.
  iIntros (Hzero Φ) "(Hs&%) HΦ".
  wp_apply (wp_SliceAppend' with "[$Hs]"); auto.
Qed.

Lemma wp_SliceAppend_to_zero stk E t x :
  val_ty x t ->
  has_zero t ->
  {{{ True }}}
    SliceAppend t (zero_val (slice.T t)) x @ stk; E
  {{{ s', RET slice_val s'; own_slice s' t (DfracOwn 1) ([x]) }}}.
Proof.
  iIntros (Hty Hzero Φ) "_ HΦ".
  iDestruct (own_slice_zero t (DfracOwn 1)) as "Hs".
  wp_apply (wp_SliceAppend' with "Hs"); auto.
Qed.

Lemma own_slice_val_ty s t q vs :
  own_slice_small s t q vs -∗
  ⌜∀ i x, vs !! i = Some x → val_ty x t⌝.
Proof.
  iIntros "Hs %i %x %Hlook".
  iDestruct "Hs" as "[Hs _]".
  iDestruct (array_elem_acc Hlook with "Hs") as "[Hi _]".
  iDestruct (struct_pointsto_ty with "Hi") as %Hty.
  iFrame "%".
Qed.

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
  iIntros (Hzero Φ) "[Hs1 Hs2] HΦ".
  wp_call.
  wp_apply wp_ref_to; [apply slice_val_ty|].
  iIntros (s_ptr) "Hs_ptr".
  iDestruct (own_slice_val_ty with "Hs2") as "%Hty".

  set for_inv :=
    (λ (loopIdx : u64), ∃ s,
      s_ptr ↦[slice.T t] (slice_val s) ∗
      own_slice s t (DfracOwn 1) (vs1 ++ (take (uint.nat loopIdx) vs2)))%I.
  wp_apply (wp_forSlice for_inv with "[] [Hs_ptr Hs1 Hs2]");
    rewrite /for_inv;
    clear for_inv.
  2: {
    replace (uint.nat 0) with (0%nat) by word.
    rewrite take_0.
    rewrite app_nil_r.
    iFrame.
  }
  {
    iIntros (?? Φ2) "!> ([%s [Hs_ptr Hs]] & %Hlt & %Hlook) HΦ2".
    wp_load.
    specialize (Hty (uint.nat i) x Hlook).
    wp_apply (wp_SliceAppend with "[$Hs]"); [done..|].
    iIntros (?) "Hs'".
    (* TODO: why doesn't wp_store work here? *)
    wp_apply (wp_StoreAt with "Hs_ptr"); [apply slice_val_ty|].
    iIntros "Hs'_ptr".
    iApply "HΦ2".
    apply take_S_r in Hlook.
    replace (uint.nat (word.add i 1)) with (S (uint.nat i)) by word.
    rewrite Hlook.
    list_simplifier.
    iFrame.
  }

  iIntros "[(%s & Hs_ptr & Hs) Hs2]".
  wp_load.
  iDestruct (own_slice_small_sz with "Hs2") as "<-".
  rewrite firstn_all.
  iApply "HΦ".
  by iFrame.
Qed.

Lemma wp_SliceSet stk E s t vs (i: u64) (x: val) :
  {{{ own_slice_small s t (DfracOwn 1) vs ∗ ⌜ is_Some (vs !! uint.nat i) ⌝ ∗ ⌜val_ty x t⌝ }}}
    SliceSet t s #i x @ stk; E
  {{{ RET #(); own_slice_small s t (DfracOwn 1) (<[uint.nat i:=x]> vs) }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  destruct H as [Hlookup Hty].
  destruct s as [ptr sz].
  wp_call.
  wp_call.
  iDestruct "Hs" as "(Hptr&%)".
  simpl in H |- *.
  replace (uint.Z i) with (Z.of_nat (uint.nat i)) by word.
  wp_apply (wp_store_offset with "Hptr"); [ | done | iIntros "Hptr" ]; auto.
  iApply "HΦ".
  iSplitL.
  { iExactEq "Hptr"; word_eq. }
  iPureIntro.
  rewrite insert_length; auto.
Qed.

(* using full ownership of the slice *)
Lemma wp_SliceSet_full stk E s t vs (i: u64) (x: val) :
  {{{ own_slice s t (DfracOwn 1) vs ∗ ⌜ is_Some (vs !! uint.nat i) ⌝ ∗ ⌜val_ty x t⌝ }}}
    SliceSet t s #i x @ stk; E
  {{{ RET #(); own_slice s t (DfracOwn 1) (<[uint.nat i:=x]> vs) }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  iDestruct (own_slice_small_acc with "Hs") as "[Hs Hs_upd]".
  wp_apply (wp_SliceSet with "[$Hs //]").
  iIntros "Hs".
  iApply "HΦ".
  iApply ("Hs_upd" with "[$]").
Qed.

End goose_lang.

#[global]
Hint Resolve slice_val_ty : core.

Arguments wp_forSlice {_ _ _ _ _ _ _}
          _%bi_scope _ _ _ _%heap_type _%Qp_scope _%list_scope _%val_scope.
Arguments wp_forSliceEach {_ _ _ _ _ _ _}
          (_ _ _)%bi_scope _ _ _ _%heap_type _%Qp_scope _%list_scope _%val_scope.

Typeclasses Opaque own_slice_small own_slice_cap.
