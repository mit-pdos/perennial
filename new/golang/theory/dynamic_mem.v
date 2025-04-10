From Coq Require Import Program.Equality.
From New.golang.theory Require Import proofmode.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From New.golang.theory Require Import typing assume list mem dynamic_typing.
From New.golang.defn Require Export dynamic_mem.

Set Default Proof Using "Type".

Section goose_lang.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!IntoVal V}.

Context `{!IntoValTyped V t}.

Lemma wp_load_ty l (v: V) q :
  {{{ ▷ l ↦{q} v }}}
    load_ty #t #l
  {{{ RET #v; l ↦{q} v }}}.
Proof.
  (*
  iIntros (Φ) ">Hl HΦ".
  rewrite type.load_ty_unseal /=.
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  pose proof (to_val_has_go_type v) as Hty.
  generalize dependent (# v). clear dependent V.
  intros v Hty.
  rename l into l'.
  iInduction Hty as [] "IH" forall (l' Φ) "HΦ".
  all: try destruct i.
  all: rewrite ?[in flatten_struct _]to_val_unseal /= /= ?loc_add_0 ?right_id; wp_pures.
  all:
    try solve [ wp_call; rewrite !to_val_unseal /=;
                           iApply (wp_load with "[$]");
                iIntros "!> H"; rewrite ?to_val_unseal /=; iApply "HΦ"; done
      ].

  {
    wp_call.
    replace n with (W64 (uint.nat n)) in * by word.
    assert (Z.of_nat (uint.nat n) < 2^64) by word.
    generalize dependent (uint.nat n); clear n; intros n Hty Hbound.
    clear Hty.
    iInduction n as [|n] "IHn" forall (l' a Φ).
    - admit.
    - rewrite (bool_decide_eq_false_2 (W64 (S n) = W64 0)); [ wp_pures | word ].
      destruct a as [|t' a']; simpl in *; [ word | ].
      iDestruct (big_sepL_app with "Hl") as "[Hl1 Hl2]".
      wp_apply ("IH" with "[] [$Hl1]").
      { naive_solver. }
      iIntros "Hl1".
      wp_pures.
      replace (word.sub (W64 (S n)) (W64 1)) with (W64 n) by word.
      wp_bind (If _ _ _).
      rewrite Z.mul_1_l.
      iApply "IHn".
      iApply ("IH" $! _ _ (foldr PairV (#()) a') with "[] [] [Hl2]").
      { iPureIntro. apply has_go_type_array.
        - word.
        - naive_solver. }
      {
        iPureIntro. rewrite app_length in Hlen.
        apply has_go_type_len in H.
  }
   *)

  rewrite load_ty_unseal /=.
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  pose proof (to_val_has_go_type v) as Hty.
  generalize dependent (# v). clear dependent V.
  generalize dependent l.
  induction t using go_type_ind;
    iIntros (l v Hty Φ) ">Hl HΦ";
    try solve [
        wp_call;
        inv Hty;
        rewrite to_val_unseal /= ?loc_add_0 ?right_id;
        iApply (wp_load with "[$Hl]");
        iFrame
      ].
  - wp_call.
    replace n with (W64 (uint.nat n)) in * by word.
    assert (Z.of_nat (uint.nat n) < 2^64) by word.
    generalize dependent (uint.nat n); clear n; intros n Hty Hbound.
    wp_apply wp_type_size. iIntros "[_ %Hsz]". wp_pures.
    iInduction n as [|n] "IH" forall (l v Hty Φ).
    + rewrite bool_decide_eq_true_2; [ wp_pures | word ].
      inv Hty.
      assert (a = []) by (destruct a; naive_solver); subst; simpl.
      rewrite to_val_unseal /=.
      iApply "HΦ". iFrame.
    + rewrite (bool_decide_eq_false_2 (W64 (S n) = W64 0)); [ wp_pures | word ].
      assert (length (flatten_struct v) = (S n * go_type_size g)%nat) as Hlen.
      {
        apply has_go_type_len in Hty.
        rewrite Hty.
        rewrite go_type_size_unseal /=.
        rewrite -go_type_size_unseal.
        replace (uint.nat (W64 (S n))) with (S n) by word.
        reflexivity.
      }
      pose proof Hty as Hty'.
      inv Hty.
      destruct a as [|t' a']; simpl in *; [ word | ].
      rewrite length_app in Hlen.
      assert (has_go_type t' g) as Ht' by naive_solver.
      pose proof Ht' as Hlen'. apply has_go_type_len in Hlen'.
      rewrite Hlen' in Hlen.
      iDestruct (big_sepL_app with "Hl") as "[Hl1 Hl2]".
      wp_apply (IHg with "[$Hl1]").
      { auto. }
      iIntros "Hl1".
      wp_pures.
      replace (word.sub (W64 (S n)) (W64 1)) with (W64 n) by word.
      wp_bind (If _ _ _).
      rewrite Z.mul_1_l.
      iApply ("IH" $! _ _ (foldr PairV (#()) a') with "[] [Hl2]").
      { iPureIntro. apply has_go_type_array.
        - word.
        - naive_solver. }
      { rewrite Hlen'.
        iApply (big_sepL_impl with "Hl2").
        iIntros "!>" (???) "H".
        iExactEq "H".
        rewrite loc_add_assoc.
        repeat (f_equal; try word). }
      iIntros "Hl2".
      wp_pures.
      iApply "HΦ".
      rewrite big_sepL_app.
      rewrite Hlen'.
      iFrame "Hl1".
      iApply (big_sepL_impl with "Hl2").
      iIntros "!>" (???) "H".
      iExactEq "H".
      rewrite loc_add_assoc.
      repeat (f_equal; try word).
  - inv Hty.
    wp_call.
    destruct i;
      rewrite to_val_unseal /= ?loc_add_0 ?right_id;
      iApply (wp_load with "[$Hl]");
      iFrame.
  - (* structT *)
    wp_call.
    admit.
Admitted.

Lemma wp_store_ty l (v0 v: V) :
  {{{ ▷l ↦ v0 }}}
    store_ty #t #l #v
  {{{ RET #(); l ↦ v }}}.
Proof.
Admitted.

End goose_lang.
