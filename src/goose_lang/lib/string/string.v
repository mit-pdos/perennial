From Perennial.goose_lang Require Import notation proofmode slice typed_slice.
From Perennial.goose_lang.lib Require Import string.impl.
Import uPred.

Section heap.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Fixpoint string_to_bytes (s:string): list u8 :=
  match s with
  | EmptyString => []
  | String x srest => [U8 (Ascii.nat_of_ascii x)] ++ (string_to_bytes srest)
  end
.

Definition bytes_to_string (l:list u8) : string :=
  fold_right (λ b s, (u8_to_string b) +:+ s) EmptyString l
.

Lemma byte_to_string_inj l :
  string_to_bytes $ bytes_to_string l = l.
Proof.
  induction l as [|].
  { done. }
  {
    rewrite /string_to_bytes /bytes_to_string /= /u8_to_ascii.
    assert (int.nat a < 256)%nat.
    { clear -a. admit. } (* FIXME: word (same as above) *)
    rewrite Ascii.nat_ascii_embedding.
    {
      f_equal.
      { clear -a. admit. } (* FIXME: word *)
      done.
    }
    { done. }
  }
Admitted.

Lemma string_to_bytes_app s1 s2 :
  string_to_bytes (s1 ++ s2) = string_to_bytes s1 ++ string_to_bytes s2.
Proof.
Admitted.

Lemma string_to_bytes_inj s :
   bytes_to_string $ string_to_bytes s = s.
Proof.
  induction s as [|].
  { done. }
  {
    replace (String a s) with ((String a EmptyString) +:+ s) by done.
    rewrite string_to_bytes_app.
    simpl.
    rewrite IHs.
    f_equal.
    rewrite /u8_to_string /u8_to_ascii.
    f_equal.
    replace (int.nat (_)) with (Ascii.nat_of_ascii a).
    2:{ Search Ascii.nat_of_ascii.
        pose proof (Ascii.nat_ascii_bounded a) as H.
        revert H. generalize (Ascii.nat_of_ascii a).
        intros. admit. (* FIXME: word. *)
    }
    by rewrite Ascii.ascii_nat_embedding.
  }
Admitted.

Lemma wp_StringToBytes (s:string) :
  {{{
        True
  }}}
    StringToBytes #(str s)
  {{{
        (sl:Slice.t), RET (slice_val sl); own_slice sl byteT 1 (string_to_bytes s)
  }}}
.
Proof.
Admitted.

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
  replace (u :: l) with ([u] ++ l) by done.
  rewrite drop_app_alt; last done.
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
