From New.proof Require Import proof_prelude.
From New.proof Require Export std.
From New.generatedproof Require Export strings.
From Perennial Require Import base.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : strings.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) strings := build_get_is_pkg_init_wf.

Local Lemma wp_asciiSpace_init Φ :
  (∀ v, Φ v) -∗
  WP exception_do ((do: #()) ;;;
    let: "$r0" := (let: "$k0" := #(W64 9) in
    let: "$v1" := #(W8 1) in
    let: "$k2" := #(W64 10) in
    let: "$v3" := #(W8 1) in
    let: "$k4" := #(W64 11) in
    let: "$v5" := #(W8 1) in
    let: "$k6" := #(W64 12) in
    let: "$v7" := #(W8 1) in
    let: "$k8" := #(W64 13) in
    let: "$v9" := #(W8 1) in
    let: "$k10" := #(W64 32) in
    let: "$v11" := #(W8 1) in
    CompositeLiteral (go.ArrayType 256 go.uint8) (LiteralValue [KeyedElement (Some (KeyExpression go.int "$k0")) (ElementExpression go.uint8 "$v1"); KeyedElement (Some (KeyExpression go.int "$k2")) (ElementExpression go.uint8 "$v3"); KeyedElement (Some (KeyExpression go.int "$k4")) (ElementExpression go.uint8 "$v5"); KeyedElement (Some (KeyExpression go.int "$k6")) (ElementExpression go.uint8 "$v7"); KeyedElement (Some (KeyExpression go.int "$k8")) (ElementExpression go.uint8 "$v9"); KeyedElement (Some (KeyExpression go.int "$k10")) (ElementExpression go.uint8 "$v11")])) in
    do:  ((GlobalVarAddr strings.asciiSpace #()) <-[go.ArrayType 256 go.uint8] "$r0"))
  {{ Φ }}.
Proof. Admitted.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop strings get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    strings.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init strings }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ") as "Hown".
  { destruct Hinit as (-> & ?); done. }
  wp_apply wp_GlobalAlloc as "?" --no-auto.
  (* asciiSpace array literal - CompositeLiteral semantics can't handle KeyExpression *)
  iApply wp_asciiSpace_init. iIntros.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

End wps.
