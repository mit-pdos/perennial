From Perennial.Helpers Require Import List.
From Perennial.goose_lang Require Import proofmode array typing.
From Perennial.goose_lang.lib Require Import slice into_val.

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

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Context {A: Type}.
Context `{!IntoVal val}.
Context `{!IntoValForType val t}.
Context (Ψ: val → A → dfrac -> iProp Σ).

Implicit Types (s: Slice.t) (t: ty) (l: list A).
(* V is the type that represents the values in the slice (through IntoVal),
while A is the type that represents the larger predicates at each address *)
Implicit Types (v: val) (x: A).

Definition is_pred_slice s q l: iProp Σ :=
  ∃ (vs: list val), own_slice_small s t q vs ∗
                  [∗ list] v;x ∈ vs;l, Ψ v x q.

Theorem wp_SliceGet {stk E} s q l (i: u64) (x: A) :
  l !! uint.nat i = Some x →
  {{{ is_pred_slice s q l }}}
    SliceGet t (slice_val s) #i @ stk; E
  {{{ (v:val), RET v; Ψ v x q ∗ (Ψ v x q -∗ is_pred_slice s q l) }}}.
Proof.
  iIntros (Hlookup Φ) "Hs HΦ".
  iDestruct "Hs" as (vs) "[Hs Hxs]".
  iDestruct (big_sepL2_lookup_2 (uint.nat i) with "Hxs") as (v) "%Hlookup1"; eauto.
  iDestruct (big_sepL2_lookup_acc with "Hxs") as "[Hx Hxs]"; eauto.
  wp_apply (slice.wp_SliceGet with "[$Hs]").
  { iPureIntro. done. }
  iIntros "[Hs %Hty]".
  iApply "HΦ"; iFrame.
  iIntros "HΨ". iFrame. iApply ("Hxs" with "HΨ").
Qed.

(* FIXME: Remove the to_val in the precondition and call to SliceAppend.
   I don't know how to do this, since that causes `apply to_val_ty` 12 lines
   below to not work since the goal is `impl.val_ty v t`, not
   `impl.val_ty (to_val v) t` *)
Theorem wp_SliceAppend {stk E} s l v x :
  {{{ is_pred_slice s (DfracOwn 1) l ∗ own_slice_cap s t ∗ Ψ (to_val v) x (DfracOwn 1) }}}
    SliceAppend t (slice_val s) (to_val v) @ stk; E
  {{{ s', RET slice_val s'; is_pred_slice s' (DfracOwn 1) (l ++ [x]) ∗ own_slice_cap s' t }}}.
Proof using IntoValForType0.
  iIntros (Φ) "(Hs&Hcap&Hx) HΦ".
  iDestruct "Hs" as (vs) "[Hs Hxs]".
  wp_apply (slice.wp_SliceAppend' with "[Hs Hcap]").
  { apply to_val_has_zero. }
  { apply to_val_ty. }
  { iFrame. }
  iIntros (s') "Hs".
  iApply "HΦ".
  iDestruct "Hs" as "[Hs $]".
  iExists (vs ++ [to_val v]).
  iFrame "Hs".
  iApply (big_sepL2_app with "Hxs").
  simpl; iFrame.
Qed.

Theorem wp_forSlice {stk E} (I: u64 → iProp Σ) s q xs (body: val) :
  (∀ (i: u64) v x,
      {{{ I i ∗ Ψ v x q }}}
        body #i v @ stk; E
      {{{ RET #(); I (word.add i (W64 1)) ∗ Ψ v x q }}}) -∗
    {{{ I (W64 0) ∗ is_pred_slice s q xs }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); I s.(Slice.sz) ∗ is_pred_slice s q xs }}}.
Proof.
  iIntros "#Hwp".
  iIntros "!>" (Φ) "(HI0 & Hs) HΦ".
  iDestruct "Hs" as (vs) "[Hs Hxs]".
  wp_apply (slice.wp_forSlice (λ i, I i ∗ [∗ list] v;x ∈ vs;xs, Ψ v x q)%I with
                "[] [$HI0 $Hs $Hxs]").
  { clear Φ.
    iIntros (i x) "!>".
    iIntros (Φ) "((Hi&Hxs)&%Hbound&%Hlookup) HΦ".
    iDestruct (big_sepL2_lookup_1 with "Hxs") as (y) "%Hlookup2"; eauto.
    iDestruct (big_sepL2_lookup_acc with "Hxs") as "[Hx Hxs]"; eauto.
    wp_apply ("Hwp" with "[$Hi $Hx]").
    iIntros "[HI Hx]".
    iSpecialize ("Hxs" with "Hx").
    iApply "HΦ"; iFrame. }
  iIntros "((HI&Hxs)&Hs)".
  iApply "HΦ"; iFrame.
Qed.

End goose_lang.
