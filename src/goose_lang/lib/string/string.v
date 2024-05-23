From Perennial.goose_lang Require Import notation proofmode slice typed_slice.
From Perennial.goose_lang.lib Require Import string.impl.
From Perennial.goose_lang.lib Require Import control.
Import uPred.

Section heap.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Definition bytes_to_string (l:list u8) : string :=
  string_of_list_ascii (u8_to_ascii <$> l).

Lemma bytes_to_string_inj l :
  string_to_bytes $ bytes_to_string l = l.
Proof.
  rewrite /string_to_bytes /bytes_to_string /=.
  rewrite -{2}(list_fmap_id l).
  rewrite list_ascii_of_string_of_list_ascii.
  rewrite -list_fmap_compose.
  apply list_fmap_ext.
  intros.
  simpl.
  rewrite /string_to_bytes /bytes_to_string /= /u8_to_ascii.
  pose proof (word.unsigned_range x).
  assert (uint.nat x < 256)%nat.
  { lia. (* word_cleanup. *) } (* FIXME: word_cleanup doesn't have good support for u8  *)
  rewrite Ascii.nat_ascii_embedding.
  {
    apply word.unsigned_inj.
    rewrite (Z2Nat.id _); last lia.
    rewrite word.unsigned_of_Z.
    by rewrite (@wrap_small _ _ _ _).
  }
  done.
Qed.

Lemma String_append s1 s2 a :
  String a s1 +:+ s2 = String a (s1 +:+ s2).
Proof.
  reflexivity.
Qed.

Lemma string_to_bytes_app s1 s2 :
  string_to_bytes (s1 ++ s2) = string_to_bytes s1 ++ string_to_bytes s2.
Proof.
  rewrite /string_to_bytes.
  induction s1; first done.
  cbn. rewrite String_append -IHs1.
  done.
Qed.

Lemma bytes_to_string_app l1 l2 :
  bytes_to_string (l1 ++ l2) = bytes_to_string l1 +:+ bytes_to_string l2.
Proof.
  rewrite /bytes_to_string.
  induction l1; first done.
  cbn. rewrite String_append -IHl1.
  done.
Qed.

Lemma string_to_bytes_inj s :
   bytes_to_string $ string_to_bytes s = s.
Proof.
  rewrite /string_to_bytes /bytes_to_string /=.
  induction s as [|].
  { done. }
  {
    simpl.
    rewrite IHs.
    f_equal.
    rewrite /u8_to_string /u8_to_ascii.
    f_equal.
    replace (uint.nat (_)) with (Ascii.nat_of_ascii a).
    2:{ pose proof (Ascii.nat_ascii_bounded a) as H.
        revert H. generalize (Ascii.nat_of_ascii a).
        intros.
        rewrite word.unsigned_of_Z.
        word.
    }
    by rewrite Ascii.ascii_nat_embedding.
  }
Qed.

Lemma string_bytes_length s :
  String.length s = length $ string_to_bytes s.
Proof.
  rewrite /string_to_bytes fmap_length.
  induction s as [|? ? IHs].
  { done. }
  { cbn. apply f_equal. done. }
Qed.

(*
Global Instance pure_StringGet s i c :
  PureExec (bin_op_eval op v1 v2 = Some c) 1 (BinOp StringGetOp (Val $ LitString $ s)
                                                     (Val $ LitInt $ i)) (c) | 10.
Proof. solve_pure_exec. Qed. *)

Lemma wp_stringToBytes (i:u64) (s:string) :
  {{{
        ⌜uint.nat i <= String.length s⌝
  }}}
    stringToBytes #i #(str s)
  {{{
        (sl:Slice.t), RET (slice_val sl); own_slice sl byteT (DfracOwn 1)
                                                    (take (uint.nat i) (string_to_bytes s))
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
  assert (uint.nat (word.sub i 1%Z) < String.length s)%nat as Hlookup.
  { enough (uint.nat i ≠ 0%nat) by word.
    intros ?. apply n. word. }
  pose proof Hlookup as Hineq2.
  rewrite string_bytes_length in Hlookup.
  apply List.list_lookup_lt in Hlookup as [? Hlookup].
  wp_pure1.
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

Lemma wp_StringToBytes (s:string) :
  {{{
        True
  }}}
    StringToBytes #(str s)
  {{{
        (sl:Slice.t), RET (slice_val sl); own_slice sl byteT (DfracOwn 1) (string_to_bytes s)
  }}}
.
Proof.
  iIntros (Φ) "Hsl HΦ".
  wp_lam. wp_pure1. wp_pures.
  wp_apply wp_Assume. iIntros (Hover).
  rewrite bool_decide_eq_true in Hover.
  wp_apply wp_stringToBytes.
  { iPureIntro. word. }
  iIntros. iApply "HΦ".
  iDestruct (own_slice_sz with "[$]") as %Hsz.
  rewrite take_ge.
  { iFrame. }
  rewrite -string_bytes_length.
  word.
Qed.

Lemma wp_StringFromBytes sl q (l:list u8) :
  {{{
        own_slice_small sl byteT q l
  }}}
    StringFromBytes (slice_val sl)
  {{{
        RET #(str bytes_to_string l); own_slice_small sl byteT q l
  }}}
.
Proof.
  iLöb as "Hwp" forall (sl q l).
  iIntros (Φ) "Hsl HΦ".
  wp_rec.
  wp_lam.
  wp_pures.
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
