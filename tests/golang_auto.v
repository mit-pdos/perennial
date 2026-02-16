From New.proof Require Import proof_prelude.
From New.proof.github_com.goose_lang.primitive Require Import disk.
From New.proof Require Import fmt.
From New.proof Require Import log.
From New.proof Require Import sync.
From New.proof.github_com.goose_lang Require Import std.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples
  Require Import unittest.

Section proof.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : unittest.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) unittest := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) unittest := build_get_is_pkg_init_wf.

Lemma wp_useInts (x: w64) (y: w32) :
  {{{ is_pkg_init unittest }}}
    @! unittest.useInts #x #y
  {{{ (a: w64) (b: w32), RET (#a, #b);
      ⌜uint.Z a = (uint.Z y + 1)%Z⌝ ∗
      ⌜uint.Z b = (uint.Z y + 3) `mod` 2^32⌝ }}}.
Proof using W.
  wp_start as "_".
  Fail wp_alloc y as "y".
  wp_alloc y_ptr as "y".
  wp_pures.
  Fail wp_alloc x_ptr as "y".
  wp_alloc x_ptr as "x".
  wp_pures. wp_alloc_auto. wp_pures.
  wp_load.
  wp_auto.
  iApply "HΦ".
  word.
Qed.

Lemma wp_useInts_auto (x: w64) (y: w32) :
  {{{ is_pkg_init unittest }}}
    @! unittest.useInts #x #y
  {{{ (a: w64) (b: w32), RET (#a, #b);
      ⌜uint.Z a = (uint.Z y + 1)%Z⌝ ∗
      ⌜uint.Z b = (uint.Z y + 3) `mod` 2^32⌝ }}}.
Proof using W.
  wp_start.
  Show 1.
  wp_auto.
  iApply "HΦ".
  word.
Qed.

Lemma wp_repeatLocalVars :
  {{{ is_pkg_init unittest }}}
    @! unittest.repeatLocalVars #()
  {{{ RET #(); True }}}.
Proof using W.
  wp_start.
  wp_auto.
  (* all points-tos should be gone *)
  Show 1.
  wp_end.
Qed.

Lemma wp_load_pointsto_not_found (x_l y_l: loc) (x: w64) :
  {{{ x_l ↦ x }}}
    ![go.uint64] #y_l
  {{{ RET #x; True }}}.
Proof using W.
  wp_start as "x".
  Fail wp_load.
Abort.

Lemma wp_load_not_next (f: func.t) (x_l: loc) (x: w64) :
  {{{ x_l ↦ x }}}
    #f #x;;;
    ![go.uint64] #x_l
  {{{ RET #x; True }}}.
Proof using W.
  wp_start as "x".
  Fail wp_load.
Abort.

Lemma wp_store_pointsto_not_found (x_l y_l: loc) (x: w64) :
  {{{ x_l ↦ x }}}
    #y_l <-[go.uint64] #x
  {{{ RET #(); True }}}.
Proof using W.
  wp_start as "x". wp_auto.
  Fail wp_store.
Abort.

Lemma wp_store_pointsto_not_fraction (x_l y_l: loc) (x: w64) :
  {{{ x_l ↦□ x }}}
    #x_l <-[go.uint64] #x
  {{{ RET #(); True }}}.
Proof using W.
  wp_start as "x". wp_auto.
  Fail wp_store.
Abort.

Lemma wp_store_not_next (f: func.t) (x_l y_l: loc) (x: w64) :
  {{{ x_l ↦ x }}}
    #f #x;;;
    #y_l <-[go.uint64] #x
  {{{ RET #x; True }}}.
Proof using W.
  wp_start as "x". wp_auto.
  Fail wp_store.
Abort.

Lemma wp_apply_not_wp (x_l: loc) (x: w64) :
  {{{ x_l ↦ x }}}
    ![go.uint64] #x_l
  {{{ RET #x; True }}}.
Proof using W.
  wp_start as "x". wp_auto.
  Fail wp_apply "HΦ".
Abort.

End proof.
