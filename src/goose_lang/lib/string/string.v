From Perennial.goose_lang Require Import notation proofmode typing slice typed_slice.
From Perennial.goose_lang.lib Require Import string.impl.
From Perennial.goose_lang.lib Require Import control.
Import uPred.

Global Delimit Scope byte_string_scope with go.
Set Default Proof Using "Type".

Section heap.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Lemma wp_stringToBytes (i:u64) (s:byte_string) :
  {{{
        ⌜uint.nat i <= length s⌝
  }}}
    stringToBytes #i #(str s)
  {{{
        (sl:Slice.t), RET (slice_val sl); own_slice sl byteT (DfracOwn 1)
                                                    (take (uint.nat i) s)
  }}}
.
Proof.
  iLöb as "Hwp" forall (i).
  iIntros (Φ) "%Hineq HΦ".
  wp_rec.
  wp_pures.
  wp_if_destruct.
  {
    change (slice.nil) with (slice_val Slice.nil).
    iApply "HΦ". iModIntro.
    rewrite take_0.
    by iApply (own_slice_nil).
  }
  wp_pures.
  destruct (decide (i = 0)).
  { subst. by exfalso. }
  assert (uint.nat (word.sub i 1%Z) < length s)%nat as Hlookup.
  { enough (uint.nat i ≠ 0%nat) by word.
    intros ?. apply n. word. }
  pose proof Hlookup as Hineq2.
  apply List.list_lookup_lt in Hlookup as [? Hlookup].
  wp_pure.
  { by rewrite /bin_op_eval /= Hlookup. }
  wp_pures.
  wp_apply ("Hwp" with "[]").
  { iPureIntro.
    rewrite -Nat2Z.inj_le.
    lia. }
  iIntros (?) "Hsl'".
  wp_apply (wp_SliceAppend with "[$]").
  iIntros (?) "Hsl".
  iApply "HΦ".
  rewrite -take_S_r.
  2:{ done. }
  replace (uint.nat i) with (S $ uint.nat (word.sub i 1%Z))%nat.
  2:{ enough (uint.nat i ≠ 0%nat) by word.
      intros ?. apply n. word. }
  iFrame.
Qed.

Lemma wp_StringToBytes (s:byte_string) :
  {{{
        True
  }}}
    StringToBytes #(str s)
  {{{
        (sl:Slice.t), RET (slice_val sl); own_slice sl byteT (DfracOwn 1) s
  }}}
.
Proof.
  iIntros (Φ) "Hsl HΦ".
  wp_rec. wp_pures.
  wp_apply wp_Assume. iIntros (Hover).
  rewrite bool_decide_eq_true in Hover.
  wp_apply wp_stringToBytes.
  { word. }
  iIntros. iApply "HΦ".
  iDestruct (own_slice_sz with "[$]") as %Hsz.
  rewrite take_ge.
  { iFrame. }
  word.
Qed.

Lemma wp_StringFromBytes sl q (l:list u8) :
  {{{
        own_slice_small sl byteT q l
  }}}
    StringFromBytes (slice_val sl)
  {{{
        RET #(str l); own_slice_small sl byteT q l
  }}}
.
Proof.
  iLöb as "Hwp" forall (sl q l).
  iIntros (Φ) "Hsl HΦ".
  wp_rec. wp_rec. wp_pures.
  destruct sl; simpl in *.
  iDestruct (own_slice_small_sz with "Hsl") as %Hsz.
  iDestruct (own_slice_small_wf with "Hsl") as %Hwf.
  wp_if_destruct.
  { (* case: empty slice *)
    apply nil_length_inv in Hsz. subst.
    iApply "HΦ". iModIntro. iFrame.
  }
  (* case: non-empty slice *)
  destruct l.
  { simpl in *. exfalso.
    apply Heqb. repeat f_equal.
    word. }

  wp_apply (wp_SliceGet with "[$Hsl]").
  { done. }
  iIntros "Hsl".
  wp_pures.
  wp_apply wp_slice_len.
  wp_apply wp_SliceSubslice.
  { simpl in *; split; word. }
  iDestruct (slice_small_split _ 1 with "Hsl") as "[H0 Hsl]".
  { simpl. word. }
  rewrite /slice_take /slice_subslice.
  replace (w :: l) with ([w] ++ l) by done.
  rewrite drop_app_length'; last done.
  wp_apply ("Hwp" with "[$]").
  iIntros "Hsl".
  wp_pures.
  iModIntro.
  iSpecialize ("HΦ" with "[H0 Hsl]").
  { iApply (own_slice_combine with "[$] [$]").
    simpl in *. word. }
  iFrame.
Qed.

End heap.
