From New.proof Require Import fmt.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.primitive Require Import disk.
From New.proof.github_com.goose_lang Require Import std.
From New.proof Require Import log.
From New.proof Require Import sync.
From New.proof Require Import encoding.binary.
From New.proof Require Import disk_prelude.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import unittest.
From New.generatedproof Require Import fmt.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples
  Require Export semantics.
From New.proof Require Export proof_prelude.

Unset Printing Records.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance : IsPkgInit (iProp Σ) semantics := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) semantics := build_get_is_pkg_init_wf.

Definition test_fun_ok name :=
  ∀ Φ, Φ #true -∗ WP @! name #() {{ Φ }}.

End wps.

Ltac _cleanup :=
  repeat rewrite -> decide_True by (auto; word);
  repeat rewrite -> decide_False by (auto; word).

Ltac wp_call_auto :=
  first [ wp_func_call; wp_call
        | wp_method_call; wp_call
        | wp_call ].

Ltac steps := repeat (
                  wp_call_auto ||
                  wp_auto ||
                  let x := fresh "x" in wp_alloc x as "?" ||
                  _cleanup
               ).

Ltac semantics_auto :=
  iIntros (Φ) "HΦ";
  (* start proof *)
  wp_func_call; wp_call;
  steps;
  try solve [ iExactEq "HΦ"; done ].
