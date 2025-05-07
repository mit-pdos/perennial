From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples
  Require Import unittest.generics.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

#[global] Program Instance : IsPkgInit generics := ltac2:(build_pkg_init ()).

Section generic_proofs.
Context `{!IntoVal T'} `{!IntoValTyped T' T} `{Hbounded: BoundedTypeSize T}.

Lemma wp_BoxGet (b: generics.Box.t T') :
  {{{ is_pkg_init generics }}}
    generics @ "BoxGet" #T #b
  {{{ RET #(generics.Box.Value' b); True }}}.
Proof using Hbounded.
  wp_start as "_"; try wp_auto.
  iApply struct_fields_split in "b"; iNamed "b".
  wp_auto.
  iApply "HΦ"; done.
Qed.

Lemma wp_Box__Get (b: generics.Box.t T') :
  {{{ is_pkg_init generics }}}
    b @ generics @ "Box" @ "Get" #T #()
  {{{ RET #(generics.Box.Value' b); True }}}.
Proof using Hbounded.
  wp_start as "_"; try wp_auto.
  iApply struct_fields_split in "b"; iNamed "b".
  wp_auto.
  iApply "HΦ"; done.
Qed.

Lemma wp_makeGenericBox (value: T') :
  {{{ is_pkg_init generics }}}
    generics @ "makeGenericBox" #T #value
  {{{ RET #(generics.Box.mk value); True }}}.
Proof.
  wp_start as "_"; try wp_auto.
  iApply "HΦ"; done.
Qed.
End generic_proofs.

Lemma wp_BoxGet2 (b: generics.Box.t w64) :
  {{{ is_pkg_init generics }}}
    generics @ "BoxGet2" #b
  {{{ RET #(generics.Box.Value' b); True }}}.
Proof.
  wp_start as "_"; try wp_auto.
  iApply struct_fields_split in "b"; iNamed "b".
  wp_auto.
  iApply "HΦ"; done.
Qed.

Lemma wp_makeBox :
  {{{ is_pkg_init generics }}}
    generics @ "makeBox" #()
  {{{ RET #(generics.Box.mk (W64 42)); True }}}.
Proof.
  wp_start as "_"; try wp_auto.
  iApply "HΦ"; done.
Qed.

Lemma wp_useBoxGet :
  {{{ is_pkg_init generics }}}
    generics @ "useBoxGet" #()
  {{{ RET #(W64 42); True }}}.
Proof.
  wp_start as "_"; try wp_auto.
  (* TODO: how to fix automation that does this? *)
  rewrite <- (default_val_eq_zero_val (V:=generics.Box.t w64)).
  wp_auto.
  (* TODO: why does this get shelved? *)
  unshelve wp_apply wp_makeGenericBox.
  { apply _. }
  unshelve wp_apply wp_Box__Get.
  { apply _. }
  iApply "HΦ"; done.
Qed.

End wps.
