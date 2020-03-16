From Perennial.goose_lang Require Import proofmode array.
From Perennial.goose_lang.lib Require Export typed_mem slice.impl.
Set Default Proof Using "Type".

Module Slice.
  Record t :=
    mk { ptr: loc;
         sz: u64;
         cap: u64; }.
  Notation extra s := (int.val (cap s) - int.val (sz s)).
End Slice.
Notation slice_extra s := (Slice.extra s).

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

(* is_slice_small is a smaller footprint version if is_slice that imprecisely
ignores the extra capacity; it allows for weaker preconditions for code which
doesn't make use of capacity *)
Definition is_slice_small (s: Slice.t) (t:ty) (q:Qp) (vs: list val): iProp Σ :=
  s.(Slice.ptr) ↦∗[t]{q} vs ∗ ⌜length vs = int.nat s.(Slice.sz)⌝.

Definition is_slice (s: Slice.t) (t:ty) (q:Qp) (vs: list val): iProp Σ :=
  is_slice_small s t q vs ∗
  (∃ extra, ⌜Z.of_nat (length extra) = Slice.extra s⌝ ∗
            (s.(Slice.ptr) +ₗ[t] int.val s.(Slice.sz)) ↦∗[t] extra).

Lemma is_slice_to_small s t q vs :
  is_slice s t q vs -∗ is_slice_small s t q vs.
Proof.
  iDestruct 1 as "[$ _]".
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

Definition slice_val_fold (ptr: loc) (sz: u64) (cap: u64) :
  (#ptr, #sz, #cap)%V = slice_val (Slice.mk ptr sz cap) := eq_refl.


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
  ⊢ is_slice (Slice.mk null (U64 0) (U64 0)) t q [].
Proof.
  iApply is_slice_of_small; first by auto.
  rewrite /is_slice_small /=.
  rewrite array_nil.
  rewrite left_id; auto.
Qed.

Theorem zero_slice_val t :
  zero_val (slice.T t) = slice_val (Slice.mk null (U64 0) (U64 0)).
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
    word. }
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
     Slice.cap := n;
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

Lemma wp_SliceTake Φ stk E s t vs (n: u64):
  ⌜int.val n ≤ int.val s.(Slice.sz)⌝ -∗
  Φ (slice_val (slice_take s t n)) -∗
  WP (SliceTake (slice_val s) #n) @ stk; E {{ Φ }}.
Proof.
  iIntros "% HΦ".
  wp_call.
  wp_call.
  wp_if_destruct.
  - wp_apply wp_panic.
    word.
  - wp_call.
    iApply "HΦ".
Qed.

Lemma wp_SliceSubslice Φ stk E s t (n1 n2: u64):
  ⌜int.val n1 ≤ int.val n2 ∧ int.val n2 ≤ int.val s.(Slice.sz)⌝ -∗
  Φ (slice_val (Slice.mk (s.(Slice.ptr) +ₗ[t] int.val n1) (word.sub n2 n1) (word.sub n2 n1))) -∗
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

Lemma wp_SliceGet stk E sl t q vs (i: u64) v0 :
  {{{ is_slice_small sl t q vs ∗ ⌜ vs !! int.nat i = Some v0 ⌝ }}}
    SliceGet t sl #i @ stk; E
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

Lemma list_lookup_lt A (l: list A) (i: nat) :
  (i < length l)%nat ->
  exists x, l !! i = Some x.
Proof.
  intros.
  destruct_with_eqn (l !! i); eauto.
  exfalso.
  apply lookup_ge_None in Heqo.
  lia.
Qed.

Lemma list_lookup_Z_lt {A} (l: list A) (i: Z) :
  (0 <= i < Z.of_nat (length l)) ->
  exists x, l !! Z.to_nat i = Some x.
Proof.
  intros.
  apply list_lookup_lt.
  apply Nat2Z.inj_le; lia.
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

Lemma wp_SliceAppend stk E s t vs x :
  has_zero t ->
  {{{ is_slice s t 1 vs ∗ ⌜int.val s.(Slice.sz) + 1 < 2^64⌝ ∗ ⌜val_ty x t⌝ }}}
    SliceAppend t s x @ stk; E
  {{{ s', RET slice_val s'; is_slice s' t 1 (vs ++ [x]) }}}.
Proof.
  iIntros (Hzero Φ) "(Hs&%) HΦ".
  destruct H as [Hbound Hty].
  wp_lam; repeat wp_step.
  repeat wp_step.
  iDestruct "Hs" as "((Hptr&%)&Hfree)".
  iDestruct "Hfree" as (extra Hextralen) "Hfree".
  wp_call.
  wp_call.
  wp_call.
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
        iFrame.
        iExactEq "Hlast"; word_eq.
      * iPureIntro.
        rewrite app_length /=.
        word.
    + iExists (replicate (int.nat cap - int.nat s.(Slice.sz) - 1) (zero_val t)).
      iSplitR.
      { rewrite replicate_length.
        iPureIntro.
        word. }
      iExactEq "HnewFree"; word_eq.
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
