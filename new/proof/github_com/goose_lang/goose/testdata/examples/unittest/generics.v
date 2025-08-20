From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples
  Require Import unittest.generics.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit generics := define_is_pkg_init True%I.

Section generic_proofs.
Context `{!IntoVal T'} `{!IntoValTyped T' T} `{Hbounded: BoundedTypeSize T}.

Lemma wp_BoxGet (b: generics.Box.t T') :
  {{{ is_pkg_init generics }}}
    @! generics.BoxGet #T #b
  {{{ RET #(generics.Box.Value' b); True }}}.
Proof using Hbounded.
  wp_start as "_"; try wp_auto.
  iApply struct_fields_split in "b"; iNamed "b".
  wp_auto.
  iApply "HΦ"; done.
Qed.

Lemma wp_Box__Get (b: generics.Box.t T') :
  {{{ is_pkg_init generics }}}
    b @ generics.Box.id @ "Get" #T #()
  {{{ RET #(generics.Box.Value' b); True }}}.
Proof using Hbounded.
  wp_start as "_"; try wp_auto.
  iApply struct_fields_split in "b"; iNamed "b".
  wp_auto.
  iApply "HΦ"; done.
Qed.

Lemma wp_makeGenericBox (value: T') :
  {{{ is_pkg_init generics }}}
    @! generics.makeGenericBox #T #value
  {{{ RET #(generics.Box.mk value); True }}}.
Proof.
  wp_start as "_"; try wp_auto.
  iApply "HΦ"; done.
Qed.
End generic_proofs.

Lemma wp_BoxGet2 (b: generics.Box.t w64) :
  {{{ is_pkg_init generics }}}
    @! generics.BoxGet2 #b
  {{{ RET #(generics.Box.Value' b); True }}}.
Proof.
  wp_start as "_"; try wp_auto.
  iApply struct_fields_split in "b"; iNamed "b".
  wp_auto.
  iApply "HΦ"; done.
Qed.

Lemma wp_makeBox :
  {{{ is_pkg_init generics }}}
    @! generics.makeBox #()
  {{{ RET #(generics.Box.mk (W64 42)); True }}}.
Proof.
  wp_start as "_"; try wp_auto.
  iApply "HΦ"; done.
Qed.

Lemma wp_useBoxGet :
  {{{ is_pkg_init generics }}}
    @! generics.useBoxGet #()
  {{{ RET #(W64 42); True }}}.
Proof.
  wp_start as "_"; try wp_auto.
  (* TODO: how to fix automation that does this? *)
  rewrite <- (default_val_eq_zero_val (V:=generics.Box.t w64)).
  wp_auto.
  (* TODO: why does this get shelved? *)
  (* About IntoValTyped. *)
  Global Hint Mode IntoValTyped ! - - - : typeclass_instances.
  unshelve wp_apply wp_makeGenericBox --no-auto. { apply _. }
  (* TODO: it's a [wp_load] inside the auto causing the typeclass goal. *)
  unshelve wp_auto. { apply _. }
  unshelve wp_apply wp_Box__Get --no-auto. { apply _. }
  wp_auto. iApply "HΦ"; done.
Qed.

Lemma wp_useContainer :
  {{{ is_pkg_init generics }}}
    @! generics.useContainer #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "_"; try wp_auto.
  rewrite <- (default_val_eq_zero_val (V:=generics.Container.t w64)).
  wp_auto.
  (* NOTE: there's no way to reduce the pair here to a #x to use the list wp
  theorems, and anyway there's no wp for map literals yet *)
Abort.

Lemma wp_useMultiParam :
  {{{ is_pkg_init generics }}}
    @! generics.useMultiParam #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "_"; try wp_auto.
  rewrite <- (default_val_eq_zero_val (V:=generics.MultiParam.t w64 bool)).
  wp_auto.
  iApply struct_fields_split in "mp"; iNamed "mp".
  with_strategy opaque [is_pkg_init] cbn.
  wp_auto.
  iApply "HΦ"; done.
Qed.

Lemma wp_multiParamFunc `{!IntoVal A'} `{!IntoValTyped A' A}
`{!IntoVal B'} `{!IntoValTyped B' B}
  (x: A') (y: B') :
  {{{ is_pkg_init generics }}}
    @! generics.multiParamFunc #A #B #x #y
  {{{ s, RET #s; s ↦* [y] }}}.
Proof.
  wp_start as "_"; try wp_auto.
  unshelve wp_apply wp_slice_literal.
  { apply _. }
  iIntros (sl) "H".
  wp_auto.
  iApply "HΦ". iFrame.
Qed.

Lemma wp_useMultiParamFunc :
  {{{ is_pkg_init generics }}}
    @! generics.useMultiParamFunc #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "_"; try wp_auto.
  unshelve wp_apply wp_multiParamFunc.
  { apply _. }
  { apply _. }
  iIntros (s) "H".
  wp_auto.
  iApply "HΦ"; done.
Qed.

End wps.
