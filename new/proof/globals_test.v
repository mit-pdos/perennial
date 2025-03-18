From New.proof Require Import grove_prelude.
From New.code.github_com.mit_pdos.gokv Require Import globals_test.
Require Import New.generatedproof.github_com.mit_pdos.gokv.globals_test.
From Perennial.algebra Require Import map.

From New.golang Require Import theory.

Section proof.
Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.
Context `{!ghost_varG Σ ()}.

(* FIXME: autogenerate this *)
Local Instance wp_globals_alloc_inst :
  WpGlobalsAlloc main.vars' (@main.GlobalAddrs) (@main.var_addrs) (λ _, main.own_allocated).
Proof.
  solve_wp_globals_alloc.
Qed.

Definition own_initialized `{!main.GlobalAddrs} : iProp Σ :=
  "HglobalB" ∷ main.globalB ↦ "b"%go ∗
  "HglobalA" ∷ main.globalA ↦ "a"%go ∗
  "HglobalY" ∷ main.globalY ↦ ""%go ∗
  "HglobalX" ∷ main.GlobalX ↦ (W64 10).

Definition is_initialized (γtok : gname) `{!main.GlobalAddrs} : iProp Σ :=
  inv nroot (ghost_var γtok 1 () ∨ own_initialized).

Lemma wp_initialize' pending postconds γtok :
  main ∉ pending →
  postconds !! main = Some (∃ (d : main.GlobalAddrs), is_pkg_defined main ∗ is_initialized γtok)%I →
  {{{ own_globals_tok pending postconds }}}
    main.initialize' #()
  {{{ (_ : main.GlobalAddrs), RET #();
      is_pkg_defined main ∗ is_initialized γtok ∗ own_globals_tok pending postconds
  }}}.
Proof.
  intros ??. wp_start as "Hunused".
  wp_call.
  wp_apply (wp_package_init with "[$]").
  { rewrite H0 //. }
  { set_solver. }
  { (* prove init function *)
    iIntros "* #Hdefs Hvars Htok".
    wp_auto.

    iNamed "Hvars".

    (* go into foo() *)
    wp_func_call.
    wp_call.
    iApply wp_fupd.
    repeat (wp_globals_get || wp_auto).
    iFrame "Htok".
    iSplitR; first done.
    unfold is_initialized.
    iMod (inv_alloc with "[-]") as "#?".
    2:{ repeat iModIntro. iFrame "#". }
    iNext. iRight.
    iFrame "∗#".
  }
  iApply "HΦ".
Qed.

Context `{!main.GlobalAddrs}.

Lemma wp_main :
  {{{ is_pkg_defined main ∗ own_initialized }}}
  main @ "main" #()
  {{{ RET #(); True }}}.
Proof.
  iIntros (?) "[#Hdef Hpre] HΦ".
  iNamed "Hpre".
  wp_func_call. wp_call.
  wp_func_call. wp_call.
  wp_func_call. wp_call.
  repeat (wp_globals_get || wp_auto).
  by iApply "HΦ".
Qed.

End proof.

From Perennial.goose_lang Require Import adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require Import grove_ffi.adequacy.
From New.proof Require Import grove_prelude.
Section closed.

Definition globals_testΣ : gFunctors := #[heapΣ ; goGlobalsΣ; ghost_varΣ ()].

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
    { rewrite lookup_singleton. done. }
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
