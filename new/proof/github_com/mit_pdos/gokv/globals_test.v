(** This file is an example of working with global variables and package
    initialization. *)

From New.proof Require Import grove_prelude.
From New.code.github_com.mit_pdos.gokv Require Import globals_test.
Require Import New.generatedproof.github_com.mit_pdos.gokv.globals_test.
From Perennial.algebra Require Import map.

From New.golang Require Import theory.

Section proof.
Context `{!heapGS Σ}.
Context `{!globalsGS Σ}.
Context `{!ghost_varG Σ ()}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : globals_test.main.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) globals_test.main := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) globals_test.main := build_get_is_pkg_init_wf.
(** A proof can refer to global variable addresses as [global_addr
    PKG_NAME.VAR_NAME], as in this package-specific helper definition. *)
Local Definition own_initialized : iProp Σ :=
  "HglobalB" ∷ (global_addr main.globalB) ↦ "b"%go ∗
  "HglobalA" ∷ (global_addr main.globalA) ↦ "a"%go ∗
  "HglobalY" ∷ (global_addr main.globalY) ↦ ""%go ∗
  "HGlobalX" ∷ (global_addr main.GlobalX) ↦ (W64 10).

(* gname for escrow token. This allows for transferring ownership of
   [own_initialized] through a persistent [is_pkg_init] as defined below.*)
Context (γtok : gname).

(** (COPY ME.) This creates a definition with the initialization predicates of
    all the dependencies of [main]. *)
#[global] Instance is_pkg_init_globals_test : IsPkgInit globals_test.main :=
  define_is_pkg_init inv nroot (ghost_var γtok 1 () ∨ own_initialized).

(** (COPY ME.) This creates a definition that describes a [get_is_pkg_init] map
    that that contains all the definitions for this package and its
    dependencies. This gets implicitly used in the [wp_initialize']
    precondition. *)
#[global] Instance : GetIsPkgInitWf globals_test.main := build_get_is_pkg_init_wf.

(** (COPY ME.) This is the spec that should be proved for any package's
    initialization function. The package-specific predicate is encapsulated in
    [is_pkg_init PKG_NAME]. *)
Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop globals_test.main get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init ∗ is_go_context ∗ □ is_pkg_defined globals_test.main }}}
    main.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init globals_test.main }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #? & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.

  wp_call. wp_auto. wp_apply wp_globals_get.
  wp_apply assume.wp_assume. rewrite bool_decide_eq_true. iIntros (<-).
  iDestruct "addr" as "?". wp_auto.

  repeat (wp_apply wp_globals_get; wp_apply assume.wp_assume; rewrite bool_decide_eq_true; iIntros (<-);
          iDestruct "addr" as "?"; wp_auto).

  (* go into foo() *)
  wp_func_call. wp_call.
  iApply wp_fupd.
  repeat wp_apply wp_globals_get.
  iFrame. iEval (rewrite is_pkg_init_unfold).
  iMod (inv_alloc with "[-]") as "#$".
  2:{ repeat iModIntro. iFrame "#". }
  iNext. iRight.
  iFrame "∗#".
Qed.

(** Every program proof spec should have [is_pkg_init PKG_NAME] as its first
    conjunct in its precondition. *)
Lemma wp_main :
  {{{ is_pkg_init globals_test.main ∗ own_initialized }}}
  @! main.main #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. iNamed "Hpre". wp_func_call. wp_call.
  wp_func_call. wp_call.
  repeat wp_apply wp_globals_get.
  by iApply "HΦ".
Qed.

End proof.

(** The following is a "closed theorem" that uses the above specs. If you aren't
    interested in "closed" theorems, ignore this. *)
From Perennial.goose_lang Require Import adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require Import grove_ffi.adequacy.
From New.proof Require Import grove_prelude.
Section closed.

Definition globals_testΣ : gFunctors := #[heapΣ ; ghost_varΣ ()].

(** This closed theorem assumes that the initial state [σ] is such that there
    exists a [GoContext] so that [is_init (H:=go_ctx) σ] holds. This moreover
    assumes that the [GoContext] is such that [is_pkg_defined_pure] holds. As
    assumptions of the top-level theorem, their definitions should be audited.
    *)
Lemma globals_test_boot σ (g : goose_lang.global_state) (go_ctx : GoContext) :
  ffi_initgP g.(global_world) →
  ffi_initP σ.(world) g.(global_world) →
  is_init σ →
  is_pkg_defined_pure globals_test.main →
  dist_adequate_failstop [
      ((main.initialize' #() ;; @! main.main #())%E, σ) ] g (λ _, True).
Proof.
  simpl.
  intros ? ? Hginit Hdef_main.
  apply (grove_ffi_dist_adequacy_failstop globals_testΣ).
  { done. }
  { constructor; done. }
  intros HG.
  iIntros "_".
  iModIntro.
  iSplitL.
  2:{ iIntros. iApply fupd_mask_intro; [set_solver|iIntros "_"; done]. }
  iApply big_sepL_cons.
  iSplitL.
  {
    iIntros (HL) "_".
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    iIntros "Hglobals".
    iMod (ghost_var_alloc ()) as (γtok) "Hescrow".
    iMod (go_init (λ k, default True%I (({[
                                globals_test.main := is_pkg_init globals_test.main
                            ]} : gmap _ _) !! k)) with "[$]")
      as "(? & #?)"; [done|].
    iModIntro. iExists (λ _, True)%I.
    Unshelve.
    2:{ apply (is_pkg_init_globals_test γtok). }
    wp_apply (wp_initialize' with "[-Hescrow]").
    2:{ iFrame "∗#". iModIntro. iApply (is_pkg_defined_boot with "[$]"). done. }
    { rewrite /= -insert_empty lookup_insert_eq //. }
    iIntros "* (Hown & #Hinit)".
    iApply fupd_wp. iDestruct (is_pkg_init_access with "Hinit") as "Hinv".
    simpl. iInv "Hinv" as ">[Hbad|Hi]" "Hclose".
    { iCombine "Hbad Hescrow" gives %[Hbad _]. done. }
    iMod ("Hclose" with "[$Hescrow]") as "_". iModIntro.
    wp_auto.
    by wp_apply (wp_main with "[$]").
  }
  by iApply big_sepL_nil.
Qed.

Print Assumptions globals_test_boot.

End closed.
