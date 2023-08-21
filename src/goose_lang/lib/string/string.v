From Perennial.goose_lang Require Import notation proofmode slice typed_slice.
From Perennial.goose_lang.lib Require Import string.impl.
Import uPred.

Section heap.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Definition string_to_bytes (s:string): list u8 :=
  (λ x, U8 $ Ascii.nat_of_ascii x) <$> list_ascii_of_string s.

Definition bytes_to_string (l:list u8) : string :=
  string_of_list_ascii (u8_to_ascii <$> l).

(*
Ltac word_cleanup :=
  repeat autounfold with word in *;
  try match goal with
      | |- @eq u64 _ _ => apply word.unsigned_inj
      | |- @eq u32 _ _ => apply word.unsigned_inj
      | |- @eq u8 _ _ => apply word.unsigned_inj
      end;
  (* can't replace this with [autorewrite], probably because typeclass inference
  isn't the same *)
  rewrite ?word.unsigned_add, ?word.unsigned_sub,
  ?word.unsigned_divu_nowrap, ?word.unsigned_modu_nowrap,
  ?unsigned_U64_0, ?unsigned_U32_0,
  ?word.unsigned_of_Z, ?word.of_Z_unsigned, ?unsigned_U64, ?unsigned_U32;
  try autorewrite with word;
  repeat match goal with
         | [ H: context[word.unsigned (U64 (Zpos ?x))] |- _ ] => change (int.Z (Zpos x)) with (Zpos x) in *
         | [ |- context[word.unsigned (U64 (Zpos ?x))] ] => change (int.Z (Zpos x)) with (Zpos x)
         | [ H: context[word.unsigned (U32 (Zpos ?x))] |- _ ] => change (int.Z (U32 (Zpos x))) with (Zpos x) in *
         | [ |- context[word.unsigned (U32 (Zpos ?x))] ] => change (int.Z (U32 (Zpos x))) with (Zpos x)
         end;
  repeat match goal with
         | [ |- context[int.Z ?x] ] =>
           lazymatch goal with
           | [ H': 0 <= int.Z x < 2^64 |- _ ] => fail
           | [ H': 0 <= int.Z x <= 2^64 |- _ ] => fail (* TODO: should be unnecessary *)
           | _ => pose proof (word.unsigned_range x)
           end
         | [ H: context[int.Z ?x] |- _ ] =>
           lazymatch goal with
           | [ H': 0 <= int.Z x < 2^64 |- _ ] => fail
           | [ H': 0 <= int.Z x <= 2^64 |- _ ] => fail (* TODO: should be unnecessary *)
           | _ => pose proof (word.unsigned_range x)
           end
         end;
  repeat match goal with
         | |- context[@word.wrap _ ?word ?ok ?z] =>
           rewrite (@wrap_small _ word ok z) by lia
         | |- context[Z.of_nat (Z.to_nat ?z)] =>
           rewrite (Z2Nat.id z) by lia
         end;
  try lia. *)

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
  assert (int.nat x < 256)%nat.
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

Lemma string_to_bytes_app s1 s2 :
  string_to_bytes (s1 ++ s2) = string_to_bytes s1 ++ string_to_bytes s2.
Proof.
  rewrite /string_to_bytes.
Admitted.

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
    replace (int.nat (_)) with (Ascii.nat_of_ascii a).
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
        ⌜int.nat i <= String.length s⌝
  }}}
    stringToBytes #i #(str s)
  {{{
        (sl:Slice.t), RET (slice_val sl); own_slice sl byteT 1
                                                    (take (int.nat i) (string_to_bytes s))
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
  wp_pure1.
  { (* FIXME: StringGet wp_pures *)
    rewrite /bin_op_eval /=.
    instantiate (1:=(LitV $ LitByte $ (U8 37))).
    admit.
  }
  wp_pures.
  wp_apply ("Hwp" with "[]").
  {
    iPureIntro. admit. (* TODO: overflow reasoning *)
  }
  iIntros (?) "Hsl'".
  change (#(U8 37)) with (into_val.to_val (U8 37)).
  wp_apply (wp_SliceAppend with "[$]").
  iIntros (?) "Hsl".
  iApply "HΦ".
  (* FIXME: appending in wrong order *)
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
  iIntros (Φ) "Hsl HΦ".
  wp_lam. wp_pures.
  wp_apply wp_stringToBytes.
  { admit. (* TODO: overflow *) }
  iIntros. iApply "HΦ".
  rewrite take_ge.
  { iFrame. }
  admit. (* TODO: overflow and length of string_to_bytes vs String.length *)
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
