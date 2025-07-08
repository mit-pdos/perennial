From Coq Require Import Program.Equality.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From New.golang.defn Require Export dynamic_typing.
From New.golang.theory Require Export typing.
From New.golang.theory Require Import assume list.
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

#[global] Instance to_val_bool_inj : Inj eq eq (λ (b: bool), #b).
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
    rewrite list.Nil_unseal /list.Nil_def.
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

Lemma desc_to_val_unfold (p: go_string * go_type) :
  #p = (#p.1, #p.2)%V.
Proof.
  destruct p.
  rewrite {1}to_val_unseal //.
Qed.

#[global] Instance arrayT_pure_wp (n: w64) (elemT: go_type) :
  PureWp True
         (type.arrayT #n #elemT)
         (#(arrayT n elemT)).
Proof.
  pure_wp_start.
  rewrite to_val_unseal /=.
  iApply "HΦ".
Qed.

#[global] Instance structT_pure_wp (decls: list (go_string * go_type)) :
  PureWp True
         (type.structT #decls)
         (#(structT decls)).
Proof.
  pure_wp_start.
  rewrite to_val_unseal /=.
  iExactEq "HΦ".
  repeat f_equal.
  induction decls as [|[f t] decls]; simpl; auto.
  - rewrite list.Nil_unseal //.
  - rewrite IHdecls.
    repeat f_equal.
    repeat rewrite to_val_unseal //=.
Qed.

(* A [list.Nil] doesn't match up with [#decls], so this explicitly provides a
   pure reduction for that case. *)
#[global] Instance structT_pure_wp_nil :
  PureWp True (type.structT list.Nil) (#(structT [])).
Proof.
  pure_wp_start. rewrite to_val_unseal /=. done.
Qed.

#[global] Instance mapT_pure_wp (keyT elemT: go_type) :
  PureWp True
         (type.mapT #keyT #elemT)
         (#(mapT keyT elemT)).
Proof.
  pure_wp_start.
  iApply "HΦ".
Qed.

#[global] Instance chanT_pure_wp (elemT: go_type) :
  PureWp True
         (type.chanT #elemT)
         (#(chanT elemT)).
Proof.
  pure_wp_start.
  iApply "HΦ".
Qed.

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
    rewrite list.Nil_unseal /list.Nil_def.
    repeat rewrite !to_val_unseal /=.
    induction decls as [|[d t] decls]; simpl; auto.
    congruence.
Qed.

Lemma wp_type_size (t: go_type) stk E :
  {{{ True }}}
    type.go_type_size #t @ stk; E
  {{{ RET (#(W64 (Z.of_nat (go_type_size t)))); £1 ∗ ⌜Z.of_nat (go_type_size t) < 2^64⌝ }}}.
Proof.
  rewrite type.go_type_size_unseal.
  rewrite go_type_size_unseal.

  induction t using go_type_ind; iIntros (Φ) "_ HΦ"; wp_call_lc "Hlc";
    try solve [ iApply ("HΦ" with "[$Hlc]"); simpl; word ].

  - wp_apply IHt. iIntros "_".
    wp_apply wp_assume_mul_no_overflow. iIntros (Hoverflow).
    wp_pures.
    wp_apply IHt. iIntros "[_ %]".
    wp_pures.
    iSpecialize ("HΦ" with "[$Hlc]").
    { iPureIntro. move: Hoverflow. simpl. word. }
    iExactEq "HΦ".
    repeat f_equal.
    simpl; word.
  - iInduction decls as [| [d t] decls ] forall (Φ); wp_pures.
    + iApply "HΦ"; iFrame. auto.
    + rewrite [in #(d :: t)%struct]to_val_unseal /=.
      wp_pures.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      iApply ("IHdecls" with "[] [HΦ] [$Hlc]").
      { iPureIntro. naive_solver. }
      iIntros "[Hlc %]".
      wp_apply Hfields.
      { naive_solver. }
      iIntros "[_ %]".
      wp_apply wp_sum_assume_no_overflow.
      iIntros "%". wp_pures.
      iDestruct ("HΦ" with "[$Hlc]") as "HΦ".
      { iPureIntro. word. }
      iExactEq "HΦ".
      repeat f_equal. word.
Qed.

(* note: not an instance to take advantage of overflow assumption *)
Lemma wp_type_size_pure_wp (t: go_type) :
  PureWp True
         (type.go_type_size #t)
         (#(W64 (Z.of_nat (go_type_size t)))).
Proof.
  intros ?????; iIntros "Hwp".
  wp_apply wp_type_size. iIntros "[? %]".
  iApply ("Hwp" with "[$]").
Qed.

Lemma wp_zero_val (t: go_type) stk E :
  {{{ True }}}
    type.zero_val #t @ stk; E
  {{{ RET (zero_val t); £1 }}}.
Proof.
  rewrite type.zero_val_unseal.
  rewrite zero_val_unseal.
  induction t using go_type_ind; iIntros (Φ) "_ HΦ"; wp_call_lc "Hlc";
    try solve [
        rewrite [in (Match _ _ _ _ _)%E]to_val_unseal /=; wp_pures;
        iApply "HΦ"; done
      ].
  - iDestruct ("HΦ" with "[$Hlc]") as "HΦ".
    replace n with (W64 (uint.nat n)) by word.
    assert (Z.of_nat (uint.nat n) < 2^64) by word.
    generalize dependent (uint.nat n); clear n; intros n Hbound.
    iInduction n as [|n] forall (Hbound Φ).
    + rewrite bool_decide_eq_true_2; [ | auto ].
      wp_pures.
      iApply "HΦ"; done.
    + rewrite (bool_decide_eq_false_2 (W64 (S n) = _)); [ | word ].
      wp_pures.
      wp_apply IHt; iIntros "_".
      wp_pures.
      replace (word.sub (W64 (S n)) (W64 1)) with (W64 n) by word.
      wp_bind (If _ _ _)%E.
      iApply "IHn".
      { word. }
      wp_pures.
      iExactEq "HΦ".
      f_equal.
      simpl.
      replace (uint.nat (W64 (S n))) with (S (uint.nat n)) by word.
      simpl.
      reflexivity.
  - iDestruct ("HΦ" with "[$Hlc]") as "HΦ".
    iInduction decls as [|[f ft] decls] forall (Φ).
    + wp_pures.
      iApply "HΦ".
    + wp_pures.
      rewrite [in # (_ :: _)%struct]to_val_unseal.
      wp_pures.
      wp_apply Hfields.
      { naive_solver. }
      iIntros "_".
      wp_pures.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      iApply "IHdecls".
      { iPureIntro; naive_solver. }
      wp_pures.
      iApply "HΦ".
Qed.

#[global] Instance wp_zero_val_pure_wp (t: go_type) :
  PureWp True
         (type.zero_val #t)
         (zero_val t).
Proof.
  intros ?????; iIntros "Hwp".
  wp_apply wp_zero_val. iIntros "?".
  iApply ("Hwp" with "[$]").
Qed.

End goose_lang.
