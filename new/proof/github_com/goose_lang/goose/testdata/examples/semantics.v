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
  Require Import semantics.
From New.proof Require Import proof_prelude.

Unset Printing Records.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance : IsPkgInit (iProp Σ) semantics := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) semantics := build_get_is_pkg_init_wf.

Definition test_fun_ok name :=
  ∀ Φ, Φ #true -∗ WP @! name #() {{ Φ }}.

Ltac _cleanup :=
  repeat rewrite -> decide_True by (auto; word);
  repeat rewrite -> decide_False by (auto; word).

Ltac wp_call_auto :=
  (wp_func_call || wp_method_call || wp_call); try wp_call.

Ltac steps := repeat (wp_call_auto || wp_auto || _cleanup).

Ltac semantics_auto :=
  iIntros (Φ) "HΦ";
  (* start proof *)
  wp_func_call; wp_call;
  steps;
  try solve [ iExactEq "HΦ"; done ].

Lemma wp_testU64ToU32 :
  test_fun_ok semantics.testU64ToU32.
Proof. semantics_auto. Qed.

Lemma wp_testU32ToU64 :
  test_fun_ok semantics.testU32ToU64.
Proof. semantics_auto. Qed.

Lemma wp_testU32Len :
  test_fun_ok semantics.testU32Len.
Proof. semantics_auto. Qed.

Lemma wp_testU32NewtypeLen :
  test_fun_ok semantics.testU32NewtypeLen.
Proof. semantics_auto. Qed.

Lemma wp_testUint32Untyped :
  test_fun_ok semantics.testUint32Untyped.
Proof. semantics_auto. Qed.

Lemma wp_testPrimitiveTypesEqual :
  test_fun_ok semantics.testPrimitiveTypesEqual.
Proof. semantics_auto. Qed.

Lemma wp_testDefinedStrTypesEqual :
  test_fun_ok semantics.testDefinedStrTypesEqual.
Proof. semantics_auto. Qed.

Lemma wp_testListTypesEqual :
  test_fun_ok semantics.testListTypesEqual.
Proof. semantics_auto. Qed.

Lemma wp_testStructUpdates :
  test_fun_ok semantics.testStructUpdates.
Proof.
  semantics_auto.
  wp_alloc x1 as "H"; wp_auto.
  repeat (wp_call_auto || wp_auto).
  wp_end.
Qed.

Lemma wp_testOrCompare :
  test_fun_ok semantics.testOrCompare.
Proof. semantics_auto. Qed.
Lemma wp_testAndCompare :
  test_fun_ok semantics.testAndCompare.
Proof. semantics_auto. Qed.
Lemma wp_testShiftMod :
  test_fun_ok semantics.testShiftMod.
Proof. semantics_auto. Qed.

Lemma wp_testParamsInterface :
  test_fun_ok semantics.testParamsInterface.
Proof. semantics_auto. Qed.

Lemma wp_testEmptyInterface :
  test_fun_ok semantics.testEmptyInterface.
Proof. semantics_auto. Qed.

Lemma wp_testTypeAssertionInterface :
  test_fun_ok semantics.testTypeAssertionInterface.
Proof.
  semantics_auto.
  (* TODO: looks like translation bug *)
Abort.

Lemma wp_testByteSliceToString :
  test_fun_ok semantics.testByteSliceToString.
Proof.
  iIntros (Φ) "HΦ".
  wp_func_call; wp_call.
  wp_auto.
  wp_apply wp_slice_make2; [ word | ].
  iIntros (sl) "[Hs Hcap]".
  wp_auto.
  iDestruct (own_slice_len with "Hs") as %Hlen.
  rewrite length_replicate in Hlen.
  steps.
  wp_apply (wp_store_slice_index with "[$Hs]") as "Hs".
  { len. }
  steps.
  wp_apply (wp_store_slice_index with "[$Hs]") as "Hs".
  { len. }
  steps.
  wp_apply (wp_store_slice_index with "[$Hs]") as "Hs".
  { len. }
  steps.
  (* missing semantics? *)
Abort.

(* this doesn't formally mean anything but if panic is opaque it tells you the code
has a panic *)
Lemma wp_shouldPanic :
  ∀ (Φ: goose_lang.val → iProp Σ),
  (∀ Ψ (v: goose_lang.val), WP @! go.panic v {{ Ψ }}) -∗
  WP @! semantics.shouldPanic #() {{ Φ }}.
Proof.
  iIntros (Φ) "Hpanic".
  wp_func_call. wp_call.
  wp_apply "Hpanic".
Qed.

End wps.
