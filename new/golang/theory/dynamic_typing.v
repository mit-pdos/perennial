From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Program.Equality.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From New.golang.defn Require Export dynamic_typing.
From New.golang.theory Require Import typing list mem.
From New.golang.theory Require Import proofmode.

Set Default Proof Using "Type".

Section goose_lang.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!IntoVal V}.

#[global] Instance to_val_w64_inj : Inj eq eq (λ (n: w64), #n).
Proof.
  rewrite to_val_unseal /to_val_def /=.
  intros n1 n2. inv 1. auto.
Qed.

#[global] Instance to_val_string_inj : Inj eq eq (λ (s: byte_string), #s).
Proof.
  rewrite to_val_unseal /to_val_def /=.
  intros s1 s2. inv 1. auto.
Qed.

#[global] Instance type_to_val_inj : Inj eq eq type.type_to_val.
Proof.
  intros t1 t2.
  generalize dependent t2.
  induction t1 using go_type_ind; simpl;
    destruct t2; simpl; intros; auto;
    repeat lazymatch goal with
    | H: InjLV _ = InjLV _ |- _ => inv H
    | H: InjRV _ = InjRV _ |- _ => inv H
    | H: InjLV _ = InjRV _ |- _ => solve [ exfalso; inv H ]
    | H: InjRV _ = InjLV _ |- _ => solve [ exfalso; inv H ]
    | H: # (W64 _) = # (W64 _) |- _ =>
        solve [ exfalso; apply inj in H; lia ]
    end.
  - (* arrayT *)
    naive_solver.
  - (* structT *)
    generalize dependent decls0.
    induction decls as [|[d t] decls]; intros decls' Heq.
    + destruct decls' as [|[d' t']]; simpl in *; try congruence.
    + destruct decls' as [|[d' t']]; simpl in *; try congruence.
      inversion Heq as [[Hd Ht Hdecls]].
      apply (inj _) in Hd; subst d.
      apply Hfields in Ht; subst; auto.
      apply IHdecls in Hdecls; [ inv Hdecls; auto | auto ].
Qed.

#[global] Instance descriptor_into_val : IntoVal (go_string * go_type) :=
  { to_val_def := fun '(d, t) => (#d, #t)%V; }.

Global Instance wp_type_Match (t : go_type) (baseCase arrayCase structCase : val) :
  PureWp True
    (type.Match #t baseCase arrayCase structCase)
    (match t with
     | arrayT n t => (arrayCase #n #t)%V
     | structT d => (structCase #d)%V
     | _ => (baseCase #t)%V
     end).
Proof.
  rewrite type.Match_unseal.
  intros ?????. iIntros "Hwp".
  rewrite [in #t]to_val_unseal.
  destruct t; wp_call_lc "?"; try by iApply "Hwp".
  - rewrite to_val_unseal /=.
    by iApply "Hwp".
  - iDestruct ("Hwp" with "[$]") as "Hwp".
    iExactEq "Hwp".
    repeat f_equal.
    repeat rewrite !to_val_unseal /=.
    induction decls as [|[d t] decls]; simpl; auto.
    congruence.
Qed.

Lemma wp_type_size' (t: go_type) stk E :
  {{{ True }}}
    type.go_type_size_e #t @ stk; E
  {{{ RET (#(W64 (Z.of_nat (go_type_size t)))); £1 }}}.
Proof.
  rewrite type.go_type_size_e_unseal.
  rewrite go_type_size_unseal.

  induction t using go_type_ind; iIntros (Φ) "_ HΦ"; wp_call_lc "Hlc";
    try iApply ("HΦ" with "Hlc").

  - wp_apply IHt. iIntros "_". wp_pures.
    iSpecialize ("HΦ" with "Hlc"). iExactEq "HΦ".
    repeat f_equal.
    simpl; word.
  - iSpecialize ("HΦ" with "Hlc").
    iInduction decls as [| [d t] decls ] forall (Φ); wp_pures.
    + auto.
    + rewrite [in #(d :: t)%struct]to_val_unseal /=.
      wp_pures.
      wp_apply Hfields.
      { naive_solver. }
      iIntros "_". wp_pures.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      iApply ("IHdecls" with "[] [HΦ]").
      { iPureIntro. naive_solver. }
      wp_pures.
      iExactEq "HΦ".
      repeat f_equal. word.
Qed.

Global Instance wp_type_size (t: go_type) :
  PureWp True
         (type.go_type_size_e #t)
         (#(W64 (Z.of_nat (go_type_size t)))).
Proof.
  intros ?????; iIntros "Hwp".
  wp_apply wp_type_size'. iIntros "?".
  iApply ("Hwp" with "[$]").
Qed.

Context `{!IntoValTyped V t}.

Lemma wp_load_ty l (v: V) q :
  {{{ ▷ l ↦{q} v }}}
    type.load_ty_e #t #l
  {{{ RET #v; l ↦{q} v }}}.
Proof.
  (*
  iIntros (Φ) ">Hl HΦ".
  rewrite type.load_ty_e_unseal /=.
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

  rewrite type.load_ty_e_unseal /=.
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
        (*
        replace (uint.Z (W64 (go_type_size g))) with (Z.of_nat (go_type_size g)) by word.
         *)
        iApply (big_sepL_impl with "Hl2").
        iIntros "!>" (???) "H".
        iExactEq "H".
        rewrite loc_add_assoc.
        repeat f_equal.
        replace (uint.nat (W64 (S n))) with (S n) in * by word.
        apply has_go_type_len in Hty'.
        rewrite go_type_size_unseal /= length_app in Hty'.
        replace (uint.nat (W64 (S n))) with (S n) in Hty' by word.
        rewrite Nat.mul_succ_l in Hty'.
        assert (length a' = n) by word; subst.
        admit. }
      iIntros "Hl2".
      wp_pures.
      iApply "HΦ".
      rewrite big_sepL_app.
      rewrite Hlen'.
      iFrame "Hl1".
      admit.
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

End goose_lang.
