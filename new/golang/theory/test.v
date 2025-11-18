From New.golang.theory Require Export postlifting.

Section test.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} {core_sem : go.CoreSemantics}.

Definition someStructType : go.type :=
  go.StructType [(go.FieldDecl "a"%go (go.PointerType (go.Named "uint64"%go [])))].

Lemma wp_test  :
  {{{ True }}}
  GoEquals someStructType (StructV {[ "a"%go := #null ]}, StructV {[ "a"%go := #null ]})%V
  {{{ RET #true; True }}}.
Proof.
  iIntros "% _ HΦ".

  (* TODO: abstract into lemma *)
  iApply (wp_GoInstruction [] (GoEquals someStructType)).
  { intros. repeat econstructor. }
  iNext; iIntros "* %Hstep"; inv Hstep; inv Hpure.
  iIntros "? $ !>". simpl.

  (* precondition/typeclass *)
  assert (go.is_comparable someStructType) as Hcomp.
  { rewrite go.is_comparable_struct. repeat constructor. apply into_val_comparable. }
  rewrite Hcomp.

  rewrite go._go_eq_struct. simpl.
  wp_pures.
  wp_apply wp_StructFieldGet_untyped. (* TODO: use struct field get instance *)
  { rewrite lookup_singleton //. }
  iIntros "_".
  wp_apply wp_StructFieldGet_untyped.
  { rewrite lookup_singleton //. }
  iIntros "_".
  wp_pures. by iApply "HΦ".
Qed.

End test.
