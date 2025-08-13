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

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} `{!GoContext}.
Context `{!ghost_varG Σ ()}.

Definition is_initialized : iProp Σ :=
  ∃ sl_emptyHash emptyHash,
  "#HemptyHash" ∷ (global_addr merkle.emptyHash) ↦□ sl_emptyHash ∗
  "#Hsl_emptyHash" ∷ sl_emptyHash ↦*□ emptyHash ∗
  "#His_hash" ∷ cryptoffi.cryptoffi.is_hash (Some [emptyNodeTag]) emptyHash.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'merkle).
#[global] Instance is_pkg_init_globals_test : IsPkgInit merkle :=
  {|
    is_pkg_init_def := is_initialized;
    is_pkg_init_deps := deps;
  |}.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init merkle = (is_pkg_init merkle) →
  {{{ own_initializing ∗ is_initialization get_is_pkg_init ∗ is_pkg_defined merkle }}}
    merkle.initialize' #()
  {{{ RET #(); own_initializing ∗ is_pkg_init merkle }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #Hinit & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown $Hinit]").
  2:{ rewrite Hinit //. }
  iIntros "Hown". wp_auto.
  (* TODO: initialize specs for all these other packages. *)
Admitted.

End proof.
