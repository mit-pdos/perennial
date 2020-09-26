From RecordUpdate Require Import RecordSet.
From Perennial.Helpers Require Import List Fractional.
From Perennial.goose_lang Require Import proofmode array.
From Perennial.goose_lang.lib Require Import persistent_readonly.
From Perennial.goose_lang.lib Require Export slice.impl typed_mem.
From Perennial.goose_lang.lib Require Import control.control.

From iris_string_ident Require Import ltac2_string_ident.
Set Default Proof Using "Type".

Module Slice.
  Record t :=
    mk { ptr: loc;
         sz: u64;
         cap: u64; }.
  Global Instance _eta: Settable _ := settable! mk <ptr; sz; cap>.
  Global Instance _witness: Inhabited _ := populate (mk inhabitant inhabitant inhabitant).
  Notation extra s := (int.val (cap s) - int.val (sz s)).
  Definition nil := mk null (U64 0) (U64 0).
End Slice.
Local Notation slice_extra s := (Slice.extra s).

Section goose_lang.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
Context {ext_ty: ext_types ext}.

Implicit Types (stk:stuckness) (E:coPset).
Implicit Types (v:val) (vs:list val).
Implicit Types (q:Qp).

Coercion slice_val (s: Slice.t) : val := (#s.(Slice.ptr), #s.(Slice.sz), #s.(Slice.cap)).

Transparent slice.T.
Theorem slice_val_ty s t : val_ty (slice_val s) (slice.T t).
Proof.
  val_ty.
Qed.
Opaque slice.T.

(* is_slice_small is a smaller footprint version of is_slice that imprecisely
ignores the extra capacity; it allows for weaker preconditions for code which
doesn't make use of capacity *)
Definition is_slice_small (s: Slice.t) (t:ty) (q:Qp) (vs: list val): iProp Σ :=
  s.(Slice.ptr) ↦∗[t]{q} vs ∗ ⌜length vs = int.nat s.(Slice.sz)⌝.

Definition is_slice_cap (s: Slice.t) (t:ty): iProp Σ :=
  (∃ extra, ⌜Z.of_nat (length extra) = Slice.extra s⌝ ∗
            (s.(Slice.ptr) +ₗ[t] int.val s.(Slice.sz)) ↦∗[t] extra).

Definition is_slice (s: Slice.t) (t:ty) (q:Qp) (vs: list val): iProp Σ :=
  is_slice_small s t q vs ∗ is_slice_cap s t.

Lemma is_slice_to_small s t q vs :
  is_slice s t q vs -∗ is_slice_small s t q vs.
Proof.
  iDestruct 1 as "[$ _]".
Qed.

Lemma is_slice_split s t q vs :
  is_slice s t q vs ⊣⊢ is_slice_small s t q vs ∗ is_slice_cap s t.
Proof.
  rewrite /is_slice //.
Qed.

Lemma is_slice_small_acc s t q vs :
  is_slice s t q vs -∗ is_slice_small s t q vs ∗ (∀ vs', is_slice_small s t q vs' -∗ is_slice s t q vs').
Proof.
  iDestruct 1 as "[$ Hextra]".
  iDestruct "Hextra" as (extra Hlen) "Hextra".
  iIntros (vs') "Hs".
  iFrame "Hs".
  iExists _; by iFrame.
Qed.

Lemma is_slice_small_read s t q vs :
  is_slice s t q vs -∗ is_slice_small s t q vs ∗ (is_slice_small s t q vs -∗ is_slice s t q vs).
Proof.
  iIntros "Hs".
  iDestruct (is_slice_small_acc with "Hs") as "[$ Hupd]".
  iApply ("Hupd" $! vs).
Qed.

Lemma is_slice_of_small s t q vs :
  s.(Slice.sz) = s.(Slice.cap) ->
  is_slice_small s t q vs -∗ is_slice s t q vs.
Proof.
  destruct s; simpl; intros ->.
  rewrite /is_slice /=.
  iIntros "$".
  iExists nil.
  rewrite array_nil right_id.
  rewrite Z.sub_diag; auto.
Qed.

Lemma is_slice_small_sz s t q vs :
  is_slice_small s t q vs -∗ ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof.
  iIntros "(_&%) !% //".
Qed.

Lemma is_slice_sz s t q vs :
  is_slice s t q vs -∗ ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof.
  iIntros "((_&%)&_) !% //".
Qed.

Lemma replicate_0 A (x:A) : replicate 0 x = [].
Proof. reflexivity. Qed.

Lemma is_slice_intro l t q (sz: u64) vs :
  l ↦∗[t]{q} vs -∗ ⌜length vs = int.nat sz⌝ -∗
  is_slice (Slice.mk l sz sz) t q vs.
Proof.
  iIntros "H1 H2".
  iApply is_slice_of_small; first by auto.
  iFrame.
Qed.

Theorem is_slice_elim s t q vs :
  is_slice s t q vs -∗ s.(Slice.ptr) ↦∗[t]{q} vs ∗ ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof.
  rewrite /is_slice.
  iIntros "[Hs _]".
  by iFrame.
Qed.

Theorem is_slice_small_fractional s t vs :
  fractional.Fractional (λ q, is_slice_small s t q vs).
Proof. rewrite /is_slice_small. apply _. Unshelve. exact 1%Qp. Qed.

Theorem is_slice_small_as_fractional s q t vs :
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

Theorem is_slice_small_agree s t q1 q2 vs1 vs2 :
  is_slice_small s t q1 vs1 -∗
  is_slice_small s t q2 vs2 -∗
  ⌜vs1 = vs2⌝.
Proof.
  iIntros "[Hs1 %] [Hs2 %]".
  assert (length vs1 = length vs2) by congruence.
  iDestruct (array_agree with "Hs1 Hs2") as %->; auto.
Qed.

Global Instance is_slice_small_timeless s t q vs :
  Timeless (is_slice_small s t q vs) := _.

Definition slice_val_fold (ptr: loc) (sz: u64) (cap: u64) :
  (#ptr, #sz, #cap)%V = slice_val (Slice.mk ptr sz cap) := eq_refl.

Theorem is_slice_small_not_null s bt q vs :
  bt ≠ unitBT ->
  length vs > 0 ->
  is_slice_small s (baseT bt) q vs -∗
  ⌜ s.(Slice.ptr) ≠ null ⌝.
Proof.
  iIntros (Hbt Hvs) "[Hs %]".
  destruct s; destruct vs; simpl in *; try lia.
  rewrite array_cons.
  iDestruct "Hs" as "[Hptr _]".
  rewrite base_mapsto_untype.
  2: { destruct bt; eauto. }
  iApply heap_mapsto_non_null.
  iDestruct "Hptr" as "[Hptr %]".
  iFrame.
Qed.

Theorem is_slice_not_null s bt q vs :
  bt ≠ unitBT ->
  length vs > 0 ->
  is_slice s (baseT bt) q vs -∗
  ⌜ s.(Slice.ptr) ≠ null ⌝.
Proof.
  iIntros (Hbt Hvs) "[Hs _]".
  iApply is_slice_small_not_null; last by iFrame.
  all: eauto.
Qed.

Theorem is_slice_cap_wf s t :
  is_slice_cap s t -∗ ⌜int.val s.(Slice.sz) ≤ int.val s.(Slice.cap)⌝.
Proof.
  iIntros "Hcap".
  iDestruct "Hcap" as (extra) "[% Hcap]".
  iPureIntro.
  word.
Qed.

Theorem is_slice_wf s t q vs :
  is_slice s t q vs -∗ ⌜int.val s.(Slice.sz) ≤ int.val s.(Slice.cap)⌝.
Proof.
  rewrite is_slice_split.
  iIntros "[Hs Hcap]".
  iDestruct (is_slice_cap_wf with "Hcap") as "$".
Qed.

(* TODO: order commands so primitives are opaque only after proofs *)
Transparent raw_slice.

Lemma wp_make_cap stk E (sz: u64) :
  {{{ True }}}
    make_cap #sz @ stk; E
  {{{ (cap:u64), RET #cap; ⌜int.val cap >= int.val sz⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply wp_ArbitraryInt.
  iIntros (extra) "_".
  wp_pures.
  wp_if_destruct; wp_pures; iApply "HΦ"; iPureIntro.
  - rewrite word.unsigned_add /word.wrap in Heqb.
    rewrite word.unsigned_add /word.wrap.
    word.
  - word.
Qed.

Lemma wp_raw_slice stk E l vs (sz: u64) t :
  {{{ l ↦∗[t] vs ∗ ⌜length vs = int.nat sz⌝ }}}
    raw_slice t #l #sz @ stk; E
  {{{ sl, RET slice_val sl; is_slice sl t 1 vs }}}.
Proof.
  iIntros (Φ) "(Hslice&%) HΦ".
  wp_call.
  rewrite slice_val_fold. iApply "HΦ".
  iApply (is_slice_intro with "Hslice").
  iPureIntro; auto.
Qed.

Lemma wp_slice_len stk E (s: Slice.t) (Φ: val -> iProp Σ) :
    Φ #(s.(Slice.sz)) -∗ WP slice.len (slice_val s) @ stk; E {{ v, Φ v }}.
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

Theorem is_slice_zero t q :
  ⊢ is_slice Slice.nil t q [].
Proof.
  iApply is_slice_of_small; first by auto.
  rewrite /is_slice_small /=.
  rewrite array_nil.
  rewrite left_id; auto.
Qed.

Theorem is_slice_small_nil t q s :
  int.val s.(Slice.sz) = 0 ->
  ⊢ is_slice_small s t q [].
Proof.
  intros Hsz.
  iSplit.
  - iApply array_nil; auto.
  - rewrite Hsz /=; auto.
Qed.

Lemma is_slice_nil s t q :
  int.val s.(Slice.sz) = 0 ->
  int.val s.(Slice.cap) = 0 ->
  ⊢ is_slice s t q [].
Proof.
  destruct s as [ptr len cap]; simpl; intros.
  iSplitL.
  - iApply is_slice_small_nil; simpl; auto.
  - iExists []; simpl.
    iSplitL.
    + iPureIntro; lia.
    + iApply array_nil; auto.
Qed.

Lemma is_slice_cap_nil t :
  ⊢ is_slice_cap Slice.nil t.
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
  #x1 ≠ #x2 -> int.val x1 ≠ int.val x2.
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
  {{{ sl, RET slice_val sl; is_slice sl t 1 (replicate (int.nat sz) (zero_val t)) }}}.
Proof.
  iIntros (Hzero Φ) "_ HΦ".
  wp_call.
  wp_if_destruct.
  - wp_pures.
    rewrite /slice.nil slice_val_fold.
    iApply "HΦ".
    rewrite replicate_0.
    iApply is_slice_zero.
  - wp_apply wp_make_cap.
    iIntros (cap Hcapge).
    wp_pures.
    wp_apply (wp_allocN t); eauto.
    { apply u64_val_ne in Heqb.
      change (int.val 0) with 0 in Heqb.
      word. }
  iIntros (l) "Hl".
  wp_pures.
  rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice /is_slice_small /=.
  iDestruct (array_replicate_split (int.nat sz) (int.nat cap - int.nat sz) with "Hl") as "[Hsz Hextra]";
    first by word.
  rewrite replicate_length.
  iFrame.
  iSplitR; first by auto.
  iExists (replicate (int.nat cap - int.nat sz) (zero_val t)); iFrame.
  iSplitR.
  { iPureIntro.
    rewrite replicate_length.
    simpl.
    word. }
  simpl.
  iExactEq "Hextra"; word_eq.
Qed.

Theorem wp_SliceSingleton Φ stk E t x :
  val_ty x t ->
  (∀ s, is_slice s t 1 [x] -∗ Φ (slice_val s)) -∗
  WP SliceSingleton x @ stk; E {{ Φ }}.
Proof.
  iIntros (Hty) "HΦ".
  wp_call.
  wp_apply (wp_allocN t); eauto.
  { word. }
  change (replicate (int.nat 1) x) with [x].
  iIntros (l) "Hl".
  wp_steps.
  rewrite slice_val_fold. iApply "HΦ".
  iApply is_slice_of_small; first by auto.
  rewrite /is_slice_small /=.
  iFrame.
  auto.
Qed.

Definition slice_take (sl: Slice.t) (t:ty) (n: u64) : Slice.t :=
  {| Slice.ptr := sl.(Slice.ptr);
     Slice.sz := n;
     Slice.cap := sl.(Slice.cap);
  |}.

Definition slice_skip (sl: Slice.t) (t:ty) (n: u64) : Slice.t :=
  {| Slice.ptr := sl.(Slice.ptr) +ₗ[t] int.val n;
     Slice.sz := word.sub sl.(Slice.sz) n;
     Slice.cap := word.sub sl.(Slice.cap) n;
  |}.

(* TODO: this theorem isn't true as-is for a correct model of splitting (the
above gets the capacities wrong) *)
(*
Lemma slice_split s (n: u64) t q vs :
  0 <= int.val n ->
  int.nat n <= length vs ->
  is_slice s t q vs -∗ is_slice (slice_take s t n) t q (take (int.nat n) vs) ∗
           is_slice (slice_skip s t n) t q (drop (int.nat n) vs).
 *)

Theorem is_slice_take_cap s t vs n :
  int.val n <= length vs ->
  is_slice s t 1 vs -∗
  is_slice (slice_take s t n) t 1 (take (int.nat n) vs).
Proof.
  intros.
  rewrite /is_slice /is_slice_small /is_slice_cap /slice_take /=.
  rewrite -> firstn_length_le by lia.
  iIntros "[[Hsmall %] Hcap]".
  iDestruct "Hcap" as (extra) "[% Hcap]".
  iDestruct (array_split (int.nat n) with "Hsmall") as "[Hsmall0 Hsmall1]"; try lia.
  word_cleanup.
  iSplitL "Hsmall0".
  - iFrame. done.
  - iExists _. iSplitR.
    2: {
      iApply array_app. iFrame "Hsmall1".
      replace (int.val (Slice.sz s)) with (int.val n + length (drop (int.nat n) vs)).
      2: { rewrite drop_length. lia. }
      rewrite Z.mul_add_distr_l -loc_add_assoc //.
    }
    iPureIntro.
    rewrite app_length drop_length. lia.
Qed.

Lemma slice_small_split s (n: u64) t q vs :
  int.val n <= length vs →
  is_slice_small s t q vs -∗ is_slice_small (slice_take s t n) t q (take (int.nat n) vs) ∗
           is_slice_small (slice_skip s t n) t q (drop (int.nat n) vs).
Proof.
  iIntros (Hbounds) "Hs".
  iDestruct "Hs" as "[Ha %]".
  iDestruct (array_split (int.nat n) with "Ha") as "[Ha1 Ha2]"; try lia.
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

Theorem is_slice_small_take_drop s t q n vs :
  (int.nat n <= int.nat s.(Slice.sz))%nat ->
   is_slice_small (slice_skip s t n) t q (drop (int.nat n) vs) ∗
   is_slice_small (slice_take s t n) t q (take (int.nat n) vs) ⊣⊢
  is_slice_small s t q vs.
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
    iDestruct (array_split (int.nat n) with "Ha") as "[Ha1 Ha2]"; try word.
    rewrite Z2Nat.id; try word.
    iFrame.
    iPureIntro; simpl.
    rewrite drop_length take_length; word.
Qed.

Theorem is_slice_small_take_drop_1 s t q n vs :
  (int.nat n <= int.nat s.(Slice.sz))%nat ->
  is_slice_small (slice_skip s t n) t q (drop (int.nat n) vs) ∗
                  is_slice_small (slice_take s t n) t q (take (int.nat n) vs) -∗
  is_slice_small s t q vs.
Proof.
  intros Hbound.
  rewrite is_slice_small_take_drop; auto.
Qed.

Theorem is_slice_combine s t q n vs1 vs2 :
  (int.nat n ≤ int.nat s.(Slice.sz))%nat →
  is_slice_small (slice_take s t n) t q vs1 -∗
  is_slice_small (slice_skip s t n) t q vs2 -∗
  is_slice_small s t q (vs1 ++ vs2).
Proof.
  iIntros (Hbound) "Hs1 Hs2".
  assert (vs1 = take (length vs1) (vs1 ++ vs2)) as Hvs1.
  { rewrite take_app_le //.
    rewrite take_ge //. }
  assert (vs2 = drop (length vs1) (vs1 ++ vs2)) as Hvs2.
  { rewrite drop_app_ge //.
    rewrite Nat.sub_diag //. }
  iDestruct (is_slice_small_sz with "Hs1") as %Hsz1.
  iDestruct (is_slice_small_sz with "Hs2") as %Hsz2.
  simpl in Hsz1, Hsz2.
  iApply (is_slice_small_take_drop _ _ _ (U64 (length vs1))).
  { word. }
  replace (int.nat (U64 (length vs1))) with (length vs1) by word.
  rewrite -> take_app_le by word.
  rewrite -> drop_app_ge, Nat.sub_diag by word.
  rewrite Hsz1.
  rewrite drop_0.
  rewrite -> take_ge by word.
  replace (U64 (int.nat n)) with n; first by iFrame.
  apply (inj int.val).
  word.
Qed.

Theorem slice_skip_skip (n m: u64) s t :
  int.val m ≤ int.val n ≤ int.val s.(Slice.sz) ->
  int.val s.(Slice.sz) ≤ int.val s.(Slice.cap) ->
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

Theorem is_slice_cap_skip s t n :
  int.val n ≤ int.val s.(Slice.sz) →
  is_slice_cap s t -∗
  is_slice_cap (slice_skip s t n) t.
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

Theorem is_slice_cap_skip_more s n1 n2 t :
  int.val n1 ≤ int.val n2 ≤ int.val s.(Slice.sz) ->
  int.val s.(Slice.sz) ≤ int.val s.(Slice.cap) ->
  is_slice_cap (slice_skip s t n1) t -∗ is_slice_cap (slice_skip s t n2) t.
Proof.
  iIntros (Hbound Hwf) "Hcap".
  rewrite (slice_skip_skip n2 n1); try (repeat word_cleanup).
  iApply (is_slice_cap_skip with "Hcap"); simpl; try word.
Qed.

Theorem slice_skip_take_commute s t n1 n2 :
  slice_skip (slice_take s t n1) t n2 =
  slice_take (slice_skip s t n2) t (word.sub n1 n2).
Proof.
  intros.
  destruct s as [ptr len cap]; simpl.
  rewrite /slice_take /slice_skip; simpl.
  f_equal.
Qed.

(** * Hoare triples *)

Lemma wp_SliceSkip' Φ stk E s t (n: u64):
  ⌜int.val n ≤ int.val s.(Slice.sz)⌝ -∗
  Φ (slice_val (slice_skip s t n)) -∗
  WP (SliceSkip t (slice_val s) #n) @ stk; E {{ Φ }}.
Proof.
  iIntros "% HΦ".
  wp_call.
  wp_call.
  wp_call.
  wp_call.
  iApply "HΦ".
Qed.

Lemma wp_SliceTake {Φ stk E s} t (n: u64):
  int.val n ≤ int.val s.(Slice.sz) →
  ▷ Φ (slice_val (slice_take s t n)) -∗
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

Lemma wp_SliceTake' {stk E s} t q vs (n: u64):
  int.val n ≤ length vs →
  {{{ is_slice_small s t q vs }}}
    SliceTake (slice_val s) #n @ stk; E
  {{{ RET (slice_val (slice_take s t n)); is_slice_small (slice_take s t n) t q (take (int.nat n) vs) }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  iDestruct (is_slice_small_sz with "Hs") as %Hsz.
  wp_apply (wp_SliceTake t).
  { word. }
  iApply "HΦ".
  iDestruct (is_slice_small_take_drop _ _ _ n with "Hs") as "[_ $]".
  word.
Qed.

Lemma wp_SliceSubslice Φ stk E s t (n1 n2: u64):
  ⌜int.val n1 ≤ int.val n2 ∧ int.val n2 ≤ int.val s.(Slice.sz)⌝ -∗
  ▷ Φ (slice_val (Slice.mk (s.(Slice.ptr) +ₗ[t] int.val n1) (word.sub n2 n1) (word.sub n2 n1))) -∗
  WP (SliceSubslice t (slice_val s) #n1 #n2) @ stk; E {{ Φ }}.
Proof.
  iIntros "% HΦ".
  wp_call.
  wp_if_destruct.
  - word.
  - wp_call.
    wp_if_destruct.
    + exfalso.
      rewrite word.unsigned_sub in Heqb0.
      rewrite -> wrap_small in Heqb0 by word.
      word.
    + wp_call.
      iApply "HΦ".
Qed.

Lemma is_slice_small_skipn s t q vs n:
  ⌜int.val n ≤ int.val s.(Slice.sz)⌝ -∗
  is_slice_small s t q vs -∗
  is_slice_small (Slice.mk (s.(Slice.ptr) +ₗ[t] int.val n)
                           (word.sub s.(Slice.sz) n)
                           (word.sub s.(Slice.sz) n)) t q (skipn (int.nat n) vs).
Proof.
  iIntros "% [Hs %]".
  iSplitL; simpl.
  2: {
    iPureIntro.
    rewrite skipn_length.
    word.
  }

  replace vs with (firstn (int.nat n) vs ++ skipn (int.nat n) vs) at 1 by apply firstn_skipn.

  rewrite array_app.
  iDestruct "Hs" as "[Hs0 Hs1]".
  rewrite -> firstn_length_le by lia.
  replace (Z.of_nat (int.nat n)) with (int.val n) by word.
  iFrame.
Qed.

Lemma is_slice_small_firstn s t q vs n:
  ⌜int.val n ≤ int.val s.(Slice.sz)⌝ -∗
  is_slice_small s t q vs -∗
  is_slice_small (Slice.mk s.(Slice.ptr) n n) t q (firstn (int.nat n) vs).
Proof.
  iIntros "% [Hs %]".
  iSplitL; simpl.
  2: {
    iPureIntro.
    rewrite firstn_length.
    word.
  }

  replace vs with (firstn (int.nat n) vs ++ skipn (int.nat n) vs) at 1 by apply firstn_skipn.

  rewrite array_app.
  iDestruct "Hs" as "[Hs0 Hs1]".
  iFrame.
Qed.

Lemma is_slice_small_subslice s t q vs n1 n2:
  ⌜int.val n1 ≤ int.val n2 ∧ int.val n2 ≤ int.val s.(Slice.sz)⌝ -∗
  is_slice_small s t q vs -∗
  is_slice_small (Slice.mk (s.(Slice.ptr) +ₗ[t] int.val n1)
                           (word.sub n2 n1) (word.sub n2 n1)) t q
                 (skipn (int.nat n1) (firstn (int.nat n2) vs)).
Proof.
  iIntros "% Hs".
  iDestruct (is_slice_small_firstn _ _ _ _ n2 with "[] Hs") as "Hs".
  { iPureIntro; lia. }
  iDestruct (is_slice_small_skipn _ _ _ _ n1 with "[] Hs") as "Hs".
  { iPureIntro; simpl; lia. }
  iFrame.
Qed.

Lemma wp_SliceSubslice_small stk E s t (n1 n2: u64) q vs:
  {{{
    is_slice_small s t q vs ∗
    ⌜int.val n1 ≤ int.val n2 ∧ int.val n2 ≤ int.val s.(Slice.sz)⌝
  }}}
    SliceSubslice t (slice_val s) #n1 #n2 @ stk; E
  {{{
    (s': Slice.t), RET (slice_val s');
    is_slice_small s' t q (skipn (int.nat n1) (firstn (int.nat n2) vs))
  }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  iApply wp_SliceSubslice; first done.
  iApply "HΦ".
  iModIntro.
  iApply is_slice_small_subslice; first done.
  iFrame.
Qed.

Lemma wp_SliceGet_body stk E sl t q vs (i: u64) v0 :
  {{{ is_slice_small sl t q vs ∗ ⌜ vs !! int.nat i = Some v0 ⌝ }}}
    ![t] (slice.ptr (sl) +ₗ[t] #i) @ stk; E
  {{{ RET v0; is_slice_small sl t q vs ∗ ⌜val_ty v0 t⌝ }}}.
Proof.
  iIntros (Φ) "[Hsl %] HΦ".
  destruct sl as [ptr sz].
  repeat wp_step.
  rewrite /is_slice_small /=.
  iDestruct "Hsl" as "(Hsl&%)"; simpl.
  repeat wp_call.
  iDestruct (array_elem_acc H with "Hsl") as "[Hi Hsl']".
  pose proof (word.unsigned_range i).
  word_cleanup.
  iDestruct (struct_mapsto_ty with "Hi") as %Hty.
  wp_load.
  iSpecialize ("Hsl'" with "Hi").
  iApply "HΦ"; iFrame.
  iPureIntro; auto.
Qed.


Lemma wp_SliceGet stk E sl t q vs (i: u64) v0 :
  {{{ is_slice_small sl t q vs ∗ ⌜ vs !! int.nat i = Some v0 ⌝ }}}
    SliceGet t sl #i @ stk; E
  {{{ RET v0; is_slice_small sl t q vs ∗ ⌜val_ty v0 t⌝ }}}.
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

Theorem wp_forSlice (I: u64 -> iProp Σ) stk E s t q vs (body: val) :
  (∀ (i: u64) (x: val),
      {{{ I i ∗ ⌜int.val i < int.val s.(Slice.sz)⌝ ∗
                ⌜vs !! int.nat i = Some x⌝ }}}
        body #i x @ stk; E
      {{{ RET #(); I (word.add i (U64 1)) }}}) -∗
    {{{ I (U64 0) ∗ is_slice_small s t q vs }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); I s.(Slice.sz) ∗ is_slice_small s t q vs }}}.
Proof.
  iIntros "#Hind".
  iIntros (Φ) "!> [Hi0 Hs] HΦ".
  wp_call.
  wp_apply wp_slice_len.
  wp_steps.
  remember 0 as z.
  assert (0 <= z <= int.val s.(Slice.sz)) by word.
  iDestruct (is_slice_small_sz with "Hs") as %Hslen.
  clear Heqz; generalize dependent z.
  intros z Hzrange.
  pose proof (word.unsigned_range s.(Slice.sz)).
  assert (int.val (U64 z) = z) by (rewrite /U64; word).
  iRename "Hi0" into "Hiz".
  (iLöb as "IH" forall (z Hzrange H0) "Hiz").
  wp_if_destruct.
  - destruct (list_lookup_Z_lt vs z) as [xz Hlookup]; first word.
    wp_apply (wp_SliceGet with "[$Hs]").
    { replace (int.val z); eauto. }
    iIntros "[Hs Hty]".
    iDestruct "Hty" as %Hty.
    wp_steps.
    wp_apply ("Hind" with "[$Hiz]").
    { iPureIntro; split; eauto.
      replace (int.val z); eauto. }
    iIntros "Hiz1".
    wp_steps.
    assert (int.val (z + 1) = int.val z + 1).
    { rewrite word.unsigned_of_Z.
      rewrite wrap_small; try lia. }
    replace (word.add z 1) with (U64 (z + 1)) by word.
    iSpecialize ("IH" $! (z+1) with "[] []").
    { iPureIntro; lia. }
    { iPureIntro; lia. }
    wp_apply ("IH" with "Hs HΦ Hiz1").
  - assert (z = int.val s.(Slice.sz)) by lia; subst z.
    iApply "HΦ"; iFrame.
    replace (U64 (int.val s.(Slice.sz))) with s.(Slice.sz); auto.
    unfold U64.
    rewrite word.of_Z_unsigned; auto.
Qed.

Theorem wp_forSlicePrefix (P: list val -> list val -> iProp Σ) stk E s t q vs (body: val) :
  (∀ (i: u64) (x: val) (vs: list val) (vs': list val),
      {{{ P vs (x :: vs') }}}
        body #i x @ stk; E
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
  rewrite firstn_all.
  rewrite drop_all. done.
Qed.

Theorem wp_forSliceEach (I: iProp Σ) (P Q: val -> iProp Σ) stk E s t q vs (body: val) :
  (∀ (i: u64) (x: val),
      {{{ I ∗ P x }}}
        body #i x @ stk; E
      {{{ RET #(); I ∗ Q x }}}) -∗
    {{{ is_slice_small s t q vs ∗ I ∗ [∗ list] x ∈ vs, P x }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); is_slice_small s t q vs ∗ I ∗ [∗ list] x ∈ vs, Q x }}}.
Proof.
  iIntros "#Hind".
  iIntros (Φ) "!> [Hs [Hi Hp]] HΦ".
  iDestruct (is_slice_small_sz with "Hs") as %Hlen.
  wp_apply (wp_forSlice
    (λ i, ([∗ list] x ∈ firstn (int.nat i) vs, Q x) ∗
          ([∗ list] x ∈ skipn (int.nat i) vs, P x) ∗
          I)%I with "[] [$Hs Hi Hp]").
  {
    iIntros (i x).
    iModIntro.
    iIntros (Φ0) "[(Hq & Hp & Hi) [% %]] HΦ0".
    apply take_drop_middle in H0.
    replace (int.nat (word.add i 1)) with (S (int.nat i)) by word.
    assert (length (take (int.nat i) vs) = int.nat i) as Hivs.
    { rewrite take_length. lia. }
    replace (drop (int.nat i) vs) with (x :: drop (S (int.nat i)) vs).
    2: {
      rewrite <- H0 at 2.
      rewrite drop_app_alt; eauto.
    }
    iDestruct "Hp" as "[Hpx Hp]".
    iApply ("Hind" with "[$Hi $Hpx]").
    iModIntro.
    iIntros "[Hi Hqx]".
    iApply "HΦ0".
    replace (take (S (int.nat i)) vs) with ((take (int.nat i) vs) ++ [x]).
    2: {
      rewrite <- H0 at 2.
      rewrite firstn_app Hivs.
      rewrite (firstn_all2 (take _ _)); last lia.
      f_equal.
      replace (S (int.nat i) - int.nat i)%nat with 1%nat by lia.
      rewrite /= firstn_O.
      reflexivity.
    }
    rewrite big_sepL_app /=.
    iFrame.
  }
  {
    repeat replace (int.nat 0) with 0%nat by reflexivity.
    rewrite drop_0 /=.
    iFrame.
  }
  rewrite -Hlen skipn_all firstn_all /=.
  iIntros "[(Hq & _ & Hi) Hs]".
  iApply "HΦ"; iFrame.
Qed.

Lemma u64_nat_0 (n: u64) : 0%nat = int.nat n -> n = U64 0.
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
            ⌜ length vs1 = int.nat n /\ length vs2 >= length vs1 ⌝ }}}
    MemCpy_rec t #dst #src #n @ s; E
  {{{ RET #(); dst ↦∗[t] (take (int.nat n) vs2) ∗ src ↦∗[t]{q} vs2 }}}.
Proof.
  iIntros (Φ) "(Hdst&Hsrc&Hbounds) HΦ".
  iDestruct "Hbounds" as %(Hvs1&Hvs2).
  (iLöb as "IH" forall (vs1 vs2 n dst src Hvs1 Hvs2) "Hdst Hsrc HΦ").
  wp_call.
  wp_if_destruct.
  - change (int.nat 0) with 0%nat.
    iEval (rewrite firstn_O array_nil) in "HΦ" .
    iApply "HΦ"; iFrame.
  - apply u64_val_ne in Heqb.
    change (int.val 0) with 0 in *.
    destruct vs1, vs2; simpl in Hvs1, Hvs2; try word.
    iDestruct (array_cons with "Hdst") as "[Hdst Hvs1]".
    iDestruct (array_cons with "Hsrc") as "[Hsrc Hvs2]".
    wp_load.
    wp_bind (store_ty _ _).
    iDestruct (struct_mapsto_ty with "Hsrc") as %Hv0ty.
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
      replace (take (int.nat n) (v0 :: vs2)) with
          (v0 :: take (int.nat n - 1) vs2).
      { replace (int.nat n - 1)%nat with (int.nat (word.sub n 1)) by word.
        rewrite array_cons; iFrame. }
      replace (int.nat n) with (1 + (int.nat n - 1))%nat at 2 by lia.
      auto.
Qed.

Lemma wp_SliceCopy_full stk E sl t q vs dst vs' :
  {{{ is_slice_small sl t q vs ∗ is_slice_small dst t 1 vs' ∗ ⌜length vs = length vs'⌝ }}}
    SliceCopy t (slice_val dst) (slice_val sl) @ stk; E
  {{{ RET #(U64 (length vs)); is_slice_small sl t q vs ∗ is_slice_small dst t 1 vs }}}.
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
  replace (Slice.sz sl) with (U64 (length vs)) by word.
  iApply "HΦ".
  rewrite -> take_ge by word.
  iFrame.
  iPureIntro; word.
Qed.

Global Opaque SliceCopy.

Transparent SliceAppend.

Lemma replicate_singleton {A} (x:A) :
  replicate 1 x = [x].
Proof. reflexivity. Qed.

Lemma array_split_1n l q t vs :
  (1 <= length vs)%nat ->
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

Lemma wp_SliceAppend' stk E s t vs x q :
  has_zero t ->
  val_ty x t ->
  {{{ is_slice s t q vs }}}
    SliceAppend t s x @ stk; E
  {{{ s', RET slice_val s'; is_slice s' t q (vs ++ [x]) }}}.
Proof.
  iIntros (Hzero Hty Φ) "Hs HΦ".
  wp_call.
  wp_apply wp_slice_len.
  wp_apply wp_Assume.
  iIntros (Hbound).
  apply bool_decide_eq_true in Hbound.
  assert (int.val s.(Slice.sz) + 1 < 2^64) by word.
  wp_pures.
  wp_apply wp_slice_len.
  wp_pures.
  wp_lam; wp_pures.
  wp_apply wp_slice_len; wp_pures.
  iDestruct "Hs" as "((Hptr&%)&Hfree)".
  iDestruct "Hfree" as (extra Hextralen) "Hfree".
  wp_if_destruct.
  - wp_call.
    rewrite word.unsigned_sub in Heqb.
    rewrite -> wrap_small in Heqb by word.
    iDestruct (array_split_1n with "Hfree") as (x0 extra') "(Hnew&Hfree&->)"; [ word | ].
    simpl in Hextralen.
    wp_call.
    wp_pures.
    wp_apply (wp_StoreAt with "Hnew"); [ auto | iIntros "Hnew" ].
    wp_pures.
    wp_call.
    rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice /=.
    iDestruct (array_app _ _ _ vs [x] with "[$Hptr Hnew]") as "Hptr".
    { rewrite array_singleton.
      (* XXX why does struct_mapsto_fractional need to be so explicit? *)
      iDestruct (@fractional_weaken q _ _ (struct_mapsto_fractional _ _ _) with "Hnew") as "Hnew".
      iExactEq "Hnew"; f_equal.
      f_equal.
      f_equal.
      word. }
    iFrame.
    iSplitR.
    { rewrite app_length /=.
      iPureIntro.
      word. }
    iExists extra'.
    simpl.
    iSplitR; first by iPureIntro; word.
    rewrite loc_add_assoc.
    iExactEq "Hfree"; word_eq.

  - wp_apply wp_make_cap.
    iIntros (cap Hcapgt).
    rewrite word.unsigned_add in Hcapgt.
    rewrite -> wrap_small in Hcapgt by word.
    wp_apply (wp_allocN t); auto.
    { word. }
    iIntros (l) "Halloc".
    iDestruct (array_replicate_split (int.nat s.(Slice.sz) + 1) (int.nat cap - int.nat s.(Slice.sz) - 1) with "Halloc") as "[Halloc HnewFree]";
      first by word.
    iDestruct (array_replicate_split (int.nat s.(Slice.sz)) 1%nat with "Halloc") as "[Halloc_sz Halloc1]";
      first by word.
    rewrite array_singleton.
    wp_pures.
    wp_call.
    wp_call.
    wp_apply (wp_MemCpy_rec with "[$Halloc_sz $Hptr]").
    { iPureIntro.
      rewrite replicate_length.
      word. }
    iIntros "[Hvs Hsrc]".
    rewrite firstn_all2; last lia.

    wp_pures.
    wp_call.
    wp_apply (wp_StoreAt with "[Halloc1]"); [ val_ty | | iIntros "Hlast" ].
    { iModIntro. iExactEq "Halloc1"; word_eq. }
    wp_pures.

    rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice /is_slice_small /=.
    iSplitL "Hvs Hlast".
    + iSplitL.
      * rewrite array_app array_singleton.
        iDestruct (@fractional_weaken q _ _ (@fractional.as_fractional_fractional _ _ _ q (array_fractional _ _ _ _)) with "Hvs") as "Hvs".
        iDestruct (@fractional_weaken q _ _ (struct_mapsto_fractional _ _ _) with "Hlast") as "Hlast".
        iFrame.
        iExactEq "Hlast"; word_eq.
      * iPureIntro.
        rewrite app_length /=.
        word.
    + iExists (replicate (int.nat cap - int.nat s.(Slice.sz) - 1) (zero_val t)).
      iSplitR.
      { rewrite replicate_length.
        iPureIntro.
        simpl.
        word. }
      simpl.
      iExactEq "HnewFree"; word_eq.
Qed.

Lemma wp_SliceAppend stk E s t vs x q :
  has_zero t ->
  {{{ is_slice s t q vs ∗ ⌜val_ty x t⌝ }}}
    SliceAppend t s x @ stk; E
  {{{ s', RET slice_val s'; is_slice s' t q (vs ++ [x]) }}}.
Proof.
  iIntros (Hzero Φ) "(Hs&%) HΦ".
  wp_apply (wp_SliceAppend' with "[$Hs]"); auto.
Qed.

Lemma wp_SliceAppend_to_zero stk E t x :
  val_ty x t ->
  has_zero t ->
  {{{ True }}}
    SliceAppend t (zero_val (slice.T t)) x @ stk; E
  {{{ s', RET slice_val s'; is_slice s' t 1 ([x]) }}}.
Proof.
  iIntros (Hty Hzero Φ) "_ HΦ".
  iDestruct (is_slice_zero t 1) as "Hs".
  wp_apply (wp_SliceAppend' with "Hs"); auto.
Qed.

Lemma wp_SliceSet stk E s t vs (i: u64) (x: val) :
  {{{ is_slice_small s t 1 vs ∗ ⌜ is_Some (vs !! int.nat i) ⌝ ∗ ⌜val_ty x t⌝ }}}
    SliceSet t s #i x @ stk; E
  {{{ RET #(); is_slice_small s t 1 (<[int.nat i:=x]> vs) }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  destruct H as [Hlookup Hty].
  destruct s as [ptr sz].
  wp_call.
  wp_call.
  iDestruct "Hs" as "(Hptr&%)".
  simpl in H |- *.
  replace (int.val i) with (Z.of_nat (int.nat i)) by word.
  wp_apply (wp_store_offset with "Hptr"); [ | done | iIntros "Hptr" ]; auto.
  iApply "HΦ".
  iSplitL.
  { iExactEq "Hptr"; word_eq. }
  iPureIntro.
  rewrite insert_length; auto.
Qed.

(* using full ownership of the slice *)
Lemma wp_SliceSet_full stk E s t vs (i: u64) (x: val) :
  {{{ is_slice s t 1 vs ∗ ⌜ is_Some (vs !! int.nat i) ⌝ ∗ ⌜val_ty x t⌝ }}}
    SliceSet t s #i x @ stk; E
  {{{ RET #(); is_slice s t 1 (<[int.nat i:=x]> vs) }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  iDestruct (is_slice_small_acc with "Hs") as "[Hs Hs_upd]".
  wp_apply (wp_SliceSet with "[$Hs //]").
  iIntros "Hs".
  iApply "HΦ".
  iApply ("Hs_upd" with "[$]").
Qed.

End goose_lang.

Hint Resolve slice_val_ty : val_ty.

Arguments wp_forSlice {_ _ _ _ _ _ _}
          _%bi_scope _ _ _ _%heap_type _%Qp_scope _%list_scope _%val_scope.
Arguments wp_forSliceEach {_ _ _ _ _ _ _}
          (_ _ _)%bi_scope _ _ _ _%heap_type _%Qp_scope _%list_scope _%val_scope.
