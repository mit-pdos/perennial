From Perennial.Helpers Require Import List.
From Perennial.goose_lang Require Import proofmode array typing.
From Perennial.goose_lang.lib Require Import slice typed_slice into_val.

Set Default Proof Using "Type".

Theorem big_sepL2_lookup_2 {PROP:bi} {A B:Type} {Φ: nat → A → B → PROP} {l1: list A} {l2: list B} i (v2: B) :
  l2 !! i = Some v2 →
  big_sepL2 Φ l1 l2 -∗
  ∃ v1, ⌜l1 !! i = Some v1⌝.
Proof.
  iIntros (Hlookup) "HL2".
  iDestruct (big_sepL2_length with "HL2") as %Hlen.
  destruct (list_lookup_lt l1 i) as [v1 Hlookup1]; eauto.
  rewrite Hlen.
  apply lookup_lt_is_Some_1; eauto.
Qed.

Theorem big_sepL2_lookup_1 {PROP:bi} {A B:Type} {Φ: nat → A → B → PROP} {l1: list A} {l2: list B} i (v1: A) :
  l1 !! i = Some v1 →
  big_sepL2 Φ l1 l2 -∗
  ∃ v2, ⌜l2 !! i = Some v2⌝.
Proof.
  iIntros (Hlookup) "HL2".
  iDestruct (big_sepL2_length with "HL2") as %Hlen.
  destruct (list_lookup_lt l2 i) as [v2 Hlookup2]; eauto.
  rewrite -Hlen.
  apply lookup_lt_is_Some_1; eauto.
Qed.

#[local]
Instance val_IntoVal `{ffi_syn: ffi_syntax} : IntoVal val.
Proof.
  refine {|
      to_val := λ v, v;
      from_val := λ v, Some v;
      IntoVal_def := #();
    |}.
  intros v; auto.
Defined.

Lemma list_untype_val `{ffi_syn: ffi_syntax} (l: list val) :
  list.untype l = l.
Proof.
  unfold list.untype.
  induction l.
  + done.
  + rewrite fmap_cons. rewrite IHl. done.
Qed.

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Context {A: Type}.
Context (Ψ: val → A → dfrac -> iProp Σ).

Definition own_val {X:Type} {I:IntoVal X} (v: val) (x: X) (dq: dfrac) : iProp Σ :=
  ⌜v = to_val x⌝.

Lemma own_val_to_val {X:Type} {I:IntoVal X} (v: val) (x: X) (dq: dfrac) :
  own_val v x dq ⊢@{_} ⌜v = to_val x⌝.
Proof.
  iIntros "Hown".
  iUnfold own_val in "Hown".
  iFrame.
Qed.

Lemma big_sepL2_own_val {X:Type} {I:IntoVal X} (dq: dfrac) :
  ∀ (xs:list X) (vs:list val),
  big_sepL2 (λ k v x, own_val v x dq) vs xs -∗ ⌜vs = list.untype xs⌝.
Proof.
  iIntros (xs).
  iInduction xs as [|x].
  + iIntros (vs) "Hsep". unfold list.untype, own_val.
    iDestruct (big_sepL2_nil_inv_r with "Hsep") as "%Hvs".
    rewrite Hvs. done.
  + iIntros (vs).
    destruct (vs) as [|v].
  - iIntros "Hsep".
    iDestruct (big_sepL2_nil_inv_l with "Hsep") as "%Hnil".
    discriminate Hnil.
  - iIntros "Hsep".
    iDestruct (big_sepL2_cons with "Hsep") as "[Hhead Hsep]".
    iPoseProof ("IHxs" with "Hsep") as "IH".
    unfold list.untype, own_val.
    iDestruct "Hhead" as "%Hhead".
    iDestruct "IH" as "%IH".
    iPureIntro.
    rewrite fmap_cons.
    rewrite Hhead.
    rewrite IH.
    reflexivity.
Qed.    
    
Definition is_pred_slice s t q l: iProp Σ :=
  ∃ (vs: list val), typed_slice.own_slice_small s t q vs ∗
                  [∗ list] v;x ∈ vs;l, Ψ v x q.

Lemma pred_slice_sz s t q xs :
  is_pred_slice s t q xs ⊢@{_} ⌜length xs = uint.nat s.(Slice.sz)⌝.
Proof.
  iIntros "Hsl".
  iUnfold is_pred_slice in "Hsl".
  iDestruct "Hsl" as "[%vs [Hsl HΨ]]".
  iDestruct (own_slice_small_sz with "Hsl") as "%Hslsz".
  iDestruct (big_sepL2_length with "HΨ") as "%HΨsz".
  rewrite HΨsz in Hslsz.
  done.
Qed.

Theorem wp_SliceGet {stk E} s t q l (i: u64) (x: A) :
  l !! uint.nat i = Some x →
  {{{ is_pred_slice s t q l }}}
    SliceGet t (slice_val s) #i @ stk; E
  {{{ (v:val), RET v; Ψ v x q ∗ (Ψ v x q -∗ is_pred_slice s t q l) }}}.
Proof.
  iIntros (Hlookup Φ) "Hs HΦ".
  iDestruct "Hs" as (vs) "[Hs Hxs]".
  iDestruct (big_sepL2_lookup_2 (uint.nat i) with "Hxs") as (v) "%Hlookup1"; eauto.
  iDestruct (big_sepL2_lookup_acc with "Hxs") as "[Hx Hxs]"; eauto.
  wp_apply (slice.wp_SliceGet with "[$Hs]").
  { iPureIntro. rewrite list_untype_val. done. }
  iIntros "[Hs %Hty]".
  iApply "HΦ"; iFrame.
  iIntros "HΨ". iFrame. iApply ("Hxs" with "HΨ").
Qed.

Theorem wp_SliceAppend {stk E} s t l v x :
  impl.val_ty v t -> has_zero t ->
  {{{ is_pred_slice s t (DfracOwn 1) l ∗ own_slice_cap s t ∗ Ψ v x (DfracOwn 1) }}}
    SliceAppend t (slice_val s) v @ stk; E
  {{{ s', RET slice_val s'; is_pred_slice s' t (DfracOwn 1) (l ++ [x]) ∗ own_slice_cap s' t }}}.
Proof.
  iIntros (Hval Hzero Φ) "(Hs&Hcap&Hx) HΦ".
  iDestruct "Hs" as (vs) "[Hs Hxs]".
  wp_apply (wp_SliceAppend' with "[Hs Hcap]").
  { done. }
  { done. }
  { iFrame. }
  iIntros (s') "Hs".
  iApply "HΦ".
  iDestruct "Hs" as "[Hs $]".
  iExists (vs ++ [v]).
  unfold own_slice_small.
  rewrite ?list_untype_val.
  iFrame "Hs".
  iApply (big_sepL2_app with "Hxs").
  simpl; iFrame.
Qed.

Theorem wp_SliceSet {stk E} s t l (i: u64) (x : A) v :
  impl.val_ty v t -> l !! uint.nat i = Some x ->
  {{{
        is_pred_slice s t (DfracOwn 1) l ∗
        Ψ v x (DfracOwn 1)
  }}}
    SliceSet t (slice_val s) #i v @ stk; E
  {{{
        RET #(); Ψ v x (DfracOwn 1) ∗
                 (Ψ v x (DfracOwn 1) -∗
                  is_pred_slice s t (DfracOwn 1) (<[uint.nat i:=x]> l))
  }}}.
Proof.
  iIntros (Hto_val Hlookup Φ) "[Hs HΨ] HΦ".
  iDestruct "Hs" as (vs) "[Hs Hxs]".
  iDestruct (big_sepL2_lookup_2 (uint.nat i) with "Hxs") as (v') "%Hlookup1"; eauto.
  iDestruct (big_sepL2_lookup_acc with "Hxs") as "[Hx Hxs]"; eauto.
  wp_apply (slice.wp_SliceSet with "[$Hs]").
  { iPureIntro. rewrite list_untype_val. split; first done. done. }
  iIntros "Hs".
  iApply "HΦ"; iFrame.
  iIntros "Hv".
  iExists (<[uint.nat i:=v]> vs).
  unfold own_slice_small.
  rewrite ?list_untype_val.
  iFrame "Hs".
  iApply "Hxs" in "Hx".
  iDestruct (big_sepL2_insert_acc with "Hx") as "[_ Hxs]".
  { done. } { done. }
  iApply "Hxs". iFrame.
Qed.

Theorem wp_NewSlice {stk E} t x (sz: u64) :
  has_zero t ->
  {{{ [∗ list] _ ∈ replicate (uint.nat sz) x, Ψ (zero_val t) x (DfracOwn 1) }}}
    NewSlice t #sz @ stk; E
  {{{ s, RET slice_val s; is_pred_slice s t (DfracOwn 1) (replicate (uint.nat sz) x) ∗
                          own_slice_cap s t }}}.
Proof.
  iIntros (Hzero Φ) "HΨ HΦ".
  wp_apply (slice.wp_new_slice).
  { done. }
  iIntros (sl) "Hs".
  iApply "HΦ".
  iDestruct (slice.own_slice_split with "Hs") as "[Hs Hscap]".
  iSplitR "Hscap".
  + iExists (replicate (uint.nat sz) (zero_val t)).
    unfold own_slice_small.
    rewrite ?list_untype_val.
    iFrame "Hs".
    iApply (big_sepL2_replicate_l).
    { apply length_replicate. }
    iApply (big_sepL_impl with "HΨ").
    iModIntro.
    iIntros (k x0) "%Hrep".
    apply lookup_replicate in Hrep.
    destruct Hrep as [Hrep_eq Hk].
    rewrite Hrep_eq.
    iIntros "H". done.
  + iFrame.
Qed.

Theorem wp_NewSlice_0 {stk E} t :
  has_zero t ->
  {{{ True }}}
    NewSlice t #(W64 0) @ stk; E
  {{{ s, RET slice_val s; is_pred_slice s t (DfracOwn 1) [] ∗
                          own_slice_cap s t }}}.
Proof.
  iIntros (Hzero Φ) "_ HΦ".
  wp_apply (slice.wp_new_slice); first done.
  iIntros (sl) "Hs".
  iApply "HΦ".
  iDestruct (slice.own_slice_split with "Hs") as "[Hs Hscap]".
  iSplitR "Hscap".
  + iExists [].
    unfold own_slice_small.
    rewrite ?list_untype_val.
    iFrame "Hs".
    rewrite big_sepL2_nil.
    done.
  + iFrame.
Qed.

Theorem wp_forSlice {stk E} (I: u64 → iProp Σ) s t q xs (body: val) :
  (∀ (i: u64) v x,
      {{{ I i ∗ Ψ v x q ∗ ⌜uint.Z i < uint.Z s.(Slice.sz)⌝ ∗ ⌜xs !! uint.nat i = Some x⌝ }}}
        body #i v @ stk; E
      {{{ RET #(); I (word.add i (W64 1)) ∗ Ψ v x q }}}) -∗
    {{{ I (W64 0) ∗ is_pred_slice s t q xs }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); I s.(Slice.sz) ∗ is_pred_slice s t q xs }}}.
Proof.
  iIntros "#Hwp".
  iIntros "!>" (Φ) "(HI0 & Hs) HΦ".
  iDestruct "Hs" as (vs) "[Hs Hxs]".
  wp_apply (slice.wp_forSlice (λ i, I i ∗ [∗ list] v;x ∈ vs;xs, Ψ v x q)%I with
                "[] [$HI0 $Hs $Hxs]").
  { clear Φ.
    iIntros (i x) "!>".
    iIntros (Φ) "((Hi&Hxs)&%Hbound&%Hlookup) HΦ".
    rewrite list_untype_val in Hlookup.
    iDestruct (big_sepL2_lookup_1 with "Hxs") as (y) "%Hlookup2"; eauto.
    iDestruct (big_sepL2_lookup_acc with "Hxs") as "[Hx Hxs]"; eauto.
    wp_apply ("Hwp" with "[$Hi $Hx]"); first done.
    iIntros "[HI Hx]".
    iSpecialize ("Hxs" with "Hx").
    iApply "HΦ"; iFrame. }
  iIntros "((HI&Hxs)&Hs)".
  iApply "HΦ"; iFrame.
Qed.

End goose_lang.
