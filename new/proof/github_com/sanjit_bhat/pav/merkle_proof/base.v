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
Context `{hG: heapGS Σ, !ffi_semantics _ _, !goGlobalsGS Σ}.
Context `{!ghost_varG Σ ()}.

Definition own_initialized `{!merkle.GlobalAddrs} : iProp Σ :=
  ∃ sl_emptyHash emptyHash,
  "#HemptyHash" ∷ merkle.emptyHash ↦□ sl_emptyHash ∗
  "#Hsl_emptyHash" ∷ sl_emptyHash ↦*□ emptyHash ∗
  "#His_hash" ∷ cryptoffi.cryptoffi.is_hash (Some [emptyNodeTag]) emptyHash.

Definition is_initialized (γtok : gname) `{!merkle.GlobalAddrs} : iProp Σ :=
  inv nroot (ghost_var γtok 1 () ∨ own_initialized).

Lemma wp_initialize' pending postconds γtok :
  merkle ∉ pending →
  postconds !! merkle = Some (∃ (d : merkle.GlobalAddrs), is_pkg_defined merkle ∗ is_initialized γtok)%I →
  {{{ own_globals_tok pending postconds }}}
    merkle.initialize' #()
  {{{ (_ : merkle.GlobalAddrs), RET #();
      is_pkg_defined merkle ∗ is_initialized γtok ∗ own_globals_tok pending postconds
  }}}.
Proof.
  intros ??. wp_start as "Hunused".
  wp_call.
  wp_apply (wp_package_init with "[$]").
  { rewrite H0 //. }
  { set_solver. }
  { iIntros "* #Hdefs Hvars Htok".
    wp_auto.
    wp_func_call.
    wp_call.
    wp_apply wp_slice_literal as "* Hsl_b".
    wp_apply (cryptoutil.wp_Hash with "[$Hsl_b]") as "* @".
    { (* TODO(goose): merkle init fn doesn't yet have is_pkg_init merkle,
    but still needs way to provide init for deps. *)
      admit. }
    iApply wp_fupd.
    wp_globals_get.
    wp_auto.
    iPersist "Hvars Hsl_b Hsl_hash".
    iFrame "Htok".
    iSplitR; [done|].
    rewrite /is_initialized.
    iMod (inv_alloc with "[-]") as "#?".
    2: { repeat iModIntro. iFrame "#". }
    iNext. iRight.
    iFrame "#". }
  iApply "HΦ".
Admitted.

Context `{!merkle.GlobalAddrs}.

#[global]
Program Instance is_pkg_init_merkle : IsPkgInit merkle := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_merkle.
#[local] Transparent is_pkg_init_merkle.

End proof.
