From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import merkle.
From Perennial.Helpers Require Import NamedProps.

From New.proof Require Import bytes.
From New.proof.github_com.goose_lang Require Import primitive std.
From New.proof.github_com.sanjit_bhat.pav Require Import cryptoffi cryptoutil safemarshal.
From New.proof.github_com.tchajed Require Import marshal.

Notation emptyNodeTag := (W8 0) (only parsing).
Notation leafNodeTag := (W8 1) (only parsing).
Notation innerNodeTag := (W8 2) (only parsing).

Notation cutNodeTy := (W8 0) (only parsing).
Notation leafNodeTy := (W8 1) (only parsing).
Notation innerNodeTy := (W8 2) (only parsing).

Notation max_depth := 256%nat.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition is_initialized : iProp Σ :=
  ∃ sl_emptyHash emptyHash,
  "#HemptyHash" ∷ (global_addr merkle.emptyHash) ↦□ sl_emptyHash ∗
  "#Hsl_emptyHash" ∷ sl_emptyHash ↦*□ emptyHash ∗
  "#His_emptyHash" ∷ cryptoffi.is_hash (Some [emptyNodeTag]) emptyHash.

#[global] Instance : IsPkgInit merkle := define_is_pkg_init is_initialized.
#[global] Instance : GetIsPkgInitWf merkle := build_get_is_pkg_init.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop merkle get_is_pkg_init →
  {{{ own_initializing ∗ is_initialization get_is_pkg_init ∗ is_pkg_defined merkle }}}
    merkle.initialize' #()
  {{{ RET #(); own_initializing ∗ is_pkg_init merkle }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #Hinit & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown $Hinit]").
  2:{ destruct_and! Hinit. rewrite H7. iFrame. } (* FIXME: automation *)
  iIntros "Hown". wp_auto.
  wp_apply (safemarshal.wp_initialize' with "[$Hown $Hinit]") as "[Hown #?]".
  { naive_solver. }
  1: admit.
  wp_apply (marshal.wp_initialize' with "[$Hown $Hinit]") as "[Hown #?]".
  { naive_solver. }
  1: admit.
  wp_apply (cryptoutil.wp_initialize' with "[$Hown $Hinit]") as "[Hown #?]".
  { naive_solver. }
  1: admit.
  wp_apply (cryptoffi.wp_initialize' with "[$Hown $Hinit]") as "[Hown #?]".
  { naive_solver. }
  1: admit.
  wp_apply (std.wp_initialize' with "[$Hown $Hinit]") as "[Hown #?]".
  { naive_solver. }
  1: admit.
  wp_apply (primitive.wp_initialize' with "[$Hown $Hinit]") as "[Hown #?]".
  { naive_solver. }
  1: admit.
  wp_apply (bytes.wp_initialize' with "[$Hown $Hinit]") as "[Hown #?]".
  { naive_solver. }
  1: admit.
  iFrame.

  wp_call. wp_auto.
  wp_apply wp_globals_get.
  wp_apply assume.wp_assume.
  rewrite bool_decide_eq_true. iIntros (<-).
  iDestruct "addr" as "HemptyHash". wp_auto.
  wp_func_call. wp_call.
  (* TODO(goose): need to unfold Go [const] expr for [wp_auto]. *)
  rewrite /merkle.emptyNodeTag.
  wp_auto.
  wp_apply wp_slice_literal as "* Hsl".
  wp_apply (cryptoutil.wp_Hash with "[$Hsl]") as "* @".
  wp_apply wp_globals_get --no-auto.
  wp_store.
  iPersist "HemptyHash Hsl_hash".
  wp_auto.
  iEval (rewrite Hinit is_pkg_init_unfold /=).
  iFrame "∗#".
Admitted.

End proof.
