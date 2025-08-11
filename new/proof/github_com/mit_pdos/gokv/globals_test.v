From New.proof Require Import grove_prelude.
From New.code.github_com.mit_pdos.gokv Require Import globals_test.
Require Import New.generatedproof.github_com.mit_pdos.gokv.globals_test.
From Perennial.algebra Require Import map.

From New.golang Require Import theory.

Section proof.
Context `{!heapGS Σ}.
Context `{!globalsGS Σ}.
Context `{!ghost_varG Σ ()}.
Context `{!GoContext}.

Definition own_initialized : iProp Σ :=
  "HglobalB" ∷ (global_addr main.globalB) ↦ "b"%go ∗
  "HglobalA" ∷ (global_addr main.globalA) ↦ "a"%go ∗
  "HglobalY" ∷ (global_addr main.globalY) ↦ ""%go ∗
  "HGlobalX" ∷ (global_addr main.GlobalX) ↦ (W64 10).

Context (γtok : gname).

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'globals_test.main).
Instance is_pkg_init_globals_test : IsPkgInit globals_test.main :=
  {|
    is_pkg_init_def := inv nroot (ghost_var γtok 1 () ∨ own_initialized);
    is_pkg_init_deps := deps;
  |}.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init globals_test.main = (is_pkg_init globals_test.main) →
  {{{ own_initializing ∗ is_initialization get_is_pkg_init ∗ is_pkg_defined globals_test.main }}}
    main.initialize' #()
  {{{ RET #(); own_initializing ∗ is_pkg_init globals_test.main }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #Hinit & #Hdef)".
  wp_call.
  wp_apply (wp_package_init with "[$Hown $Hinit]").
  2:{ rewrite Hinit //. }
  iFrame "∗#". iIntros "Hown".
  wp_auto. wp_call. wp_auto.
  wp_apply wp_globals_get. wp_apply assume.wp_assume. rewrite bool_decide_eq_true. iIntros (<-).
  iDestruct "addr" as "?". wp_auto.

  repeat (wp_apply wp_globals_get; wp_apply assume.wp_assume; rewrite bool_decide_eq_true; iIntros (<-);
          iDestruct "addr" as "?"; wp_auto).

  (* go into foo() *)

  wp_func_call. wp_call.
  iApply wp_fupd.
  repeat wp_apply wp_globals_get.
  iFrame. rewrite Hinit.
  iMod (inv_alloc with "[-]") as "#?".
  2:{ repeat iModIntro. rewrite is_pkg_init_unfold /=. iFrame "#". }
  iNext. iRight.
  iFrame "∗#".
Qed.

Lemma wp_main :
  {{{ is_pkg_init main ∗ own_initialized }}}
  ⊥ @ main.main #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. iNamed "Hpre". wp_func_call. wp_call.
  wp_func_call. wp_call.
  repeat wp_apply wp_globals_get.
  by iApply "HΦ".
Qed.

End proof.

From Perennial.goose_lang Require Import adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require Import grove_ffi.adequacy.
From New.proof Require Import grove_prelude.
Section closed.

Definition globals_testΣ : gFunctors := #[heapΣ ; ghost_varΣ ()].

Lemma globals_test_boot σ (g : goose_lang.global_state) :
  ffi_initgP g.(global_world) →
  ffi_initP σ.(world) g.(global_world) →
  σ.(globals) = ∅ → (* FIXME: this should be abstracted into a "goose_lang.init" predicate or something. *)
  dist_adequate_failstop [
      ((main.initialize' #() ;; main @ "main" #())%E, σ) ] g (λ _, True).
Proof.
  simpl.
  intros ? ? Hgempty.
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
    rewrite Hgempty.
    iMod (ghost_var_alloc ()) as (γtok) "Hescrow".
    iMod (go_global_init
            (λ _, {[ main := _ ]}) with "[$]") as
      (hGlobals) "Hpost".
    iModIntro.
    iExists (λ _, True)%I.
    wp_apply (wp_initialize' with "[$]").
    { set_solver. }
    { rewrite lookup_singleton_eq. done. }
    iIntros "* (Hdef & Hinit & Htok)".
    iApply fupd_wp. iInv "Hinit" as ">[Hbad|Hi]" "Hclose".
    { iCombine "Hbad Hescrow" gives %[Hbad _]. done. }
    iMod ("Hclose" with "[$Hescrow]") as "_". iModIntro.
    wp_auto.
    by wp_apply (wp_main with "[$]").
  }
  by iApply big_sepL_nil.
Qed.

Print Assumptions globals_test_boot.

End closed.
