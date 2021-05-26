From Perennial.goose_lang Require Import notation proofmode typing.
From Perennial.goose_lang Require Import wpc_proofmode.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Import
     slice.slice slice.typed_slice into_val.


Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Context `{!IntoVal V}.

Implicit Types (v:V) (vs: list V).

Lemma wpc_slice_len k stk E1 s Φ Φc :
  Φc ∧ Φ #(Slice.sz s) -∗
  WPC slice.len (slice_val s) @ stk; k; E1 {{ v, Φ v }} {{ Φc }}.
Proof.
  iIntros "HΦ".
  rewrite /slice.len.
  wpc_pures.
  { by iDestruct "HΦ" as "[$ _]". }
  { by iDestruct "HΦ" as "[_ $]". }
Qed.

Lemma wpc_SliceGet stk k E1 s t q vs (i: u64) v0 :
  {{{ is_slice_small s t q vs ∗ ⌜ vs !! int.nat i = Some v0 ⌝ }}}
    SliceGet t (slice_val s) #i @ stk; k; E1
  {{{ RET (to_val v0); is_slice_small s t q vs }}}
  {{{ True }}}.
Proof.
  iIntros (Φ Φc) "[Hs %] HΦ".
  rewrite /SliceGet.
  wpc_pures; first auto.
  { by crash_case. }
  wpc_pures.
  { by crash_case. }
  wpc_frame "HΦ".
  { by crash_case. }
  iApply (wp_SliceGet_body with "[$Hs]").
  { rewrite /list.untype list_lookup_fmap.
    rewrite H //. }
  iIntros "!> [Hs %] HΦ". iNamed "HΦ".
  iRight in "HΦ".
  iApply "HΦ".
  auto.
Qed.

Theorem wpc_forSlice (I: u64 -> iProp Σ) Φc' stk k E1 s t q (vs: list V) (body: val) :
  □ (∀ x, I x -∗ Φc') -∗
  (∀ (i: u64) (x: V),
      {{{ I i ∗ ⌜(int.nat i < length vs)%nat⌝ ∗
                ⌜vs !! int.nat i = Some x⌝ }}}
        body #i (to_val x) @ stk; k; E1
      {{{ RET #(); I (word.add i (U64 1)) }}}
      {{{ Φc' }}}) -∗
    {{{ I (U64 0) ∗ is_slice_small s t q vs }}}
      forSlice t body (slice_val s) @ stk; k; E1
    {{{ RET #(); I s.(Slice.sz) ∗ is_slice_small s t q vs }}}
    {{{ Φc' }}}.
Proof.
  iIntros "#HΦcI #Hind".
  iIntros (Φ Φc) "!> [Hi0 Hs] HΦ".
  rewrite /forSlice.
  wpc_pures.
  { iSpecialize ("HΦcI" with "[$]"). iLeft in "HΦ". iApply "HΦ". eauto. }
  wpc_pures.
  { iSpecialize ("HΦcI" with "[$]"). iLeft in "HΦ". iApply "HΦ". eauto. }
  wpc_apply wpc_slice_len.
  iSplit.
  { iSpecialize ("HΦcI" with "[$]"). iLeft in "HΦ". iApply "HΦ". eauto. }
  wpc_pures.
  { iSpecialize ("HΦcI" with "[$]"). iLeft in "HΦ". iApply "HΦ". eauto. }
  remember 0 as z.
  iRename "Hi0" into "Hiz".
  assert (0 <= z <= int.Z s.(Slice.sz)) by word.
  iDestruct (is_slice_small_sz with "Hs") as %Hslen.
  autorewrite with len in Hslen.
  clear Heqz; generalize dependent z.
  intros z Hzrange.
  assert (int.Z (U64 z) = z) by (rewrite /U64; word).
  (iLöb as "IH" forall (z Hzrange H)).
  wpc_if_destruct.
  - wpc_pures.
    { iSpecialize ("HΦcI" with "[$]"). iLeft in "HΦ". iApply "HΦ". eauto. }
    destruct (list_lookup_Z_lt vs z) as [xz Hlookup]; first word.
    wpc_apply (wpc_SliceGet with "[$Hs] [HΦ Hiz]").
    { replace (int.Z z); eauto. }
    { iSplit.
      - iSpecialize ("HΦcI" with "[$]"). iLeft in "HΦ".
        iIntros "_".
        iApply ("HΦ" with "[$]").
      - iIntros "!> Hs".
        wpc_pures.
        { iSpecialize ("HΦcI" with "[$]"). iLeft in "HΦ". iApply "HΦ". eauto. }
        wpc_apply ("Hind" with "[Hiz]").
        + iFrame.
          iPureIntro.
          split; try lia.
          replace (int.nat z) with (Z.to_nat z) by lia; auto.
        + iSplit; crash_case.
          { iLeft in "HΦ"; iFrame. }
          iIntros "!> Hiz1".
          wpc_pures.
          { iSpecialize ("HΦcI" with "[$]"). iLeft in "HΦ". iApply "HΦ". eauto. }
          assert (int.Z (z + 1) = int.Z z + 1) by word.
          replace (word.add z 1) with (U64 (z + 1)) by word.
          iSpecialize ("IH" $! (z+1) with "[] []").
          { iPureIntro; word. }
          { iPureIntro; word. }
          wpc_apply ("IH" with "[$] [$] [$]"). }
  - assert (z = int.Z s.(Slice.sz)) by lia; subst z.
    wpc_pures; swap 2 3.
    { iSpecialize ("HΦcI" with "[$]"). iLeft in "HΦ". iApply "HΦ". eauto. }
    { iSpecialize ("HΦcI" with "[$]"). iLeft in "HΦ". iApply "HΦ". eauto. }
    iRight in "HΦ".
    replace (U64 (int.Z s.(Slice.sz))) with s.(Slice.sz); last first.
    { rewrite /U64 word.of_Z_unsigned //. }
    iApply ("HΦ" with "[$]").
Qed.

End goose_lang.
