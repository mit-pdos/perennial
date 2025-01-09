From New.proof Require Import grove_prelude.
From New.code.github_com.mit_pdos.gokv Require globals_test.
From Perennial.algebra Require Import map.

Section proof.

Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition own_defined : iProp Σ :=
  ∃ globalB_addr globalA_addr globalY_addr GlobalX_addr,
    "#HglobalB_addr" ∷ is_global_addr globals_test.globalB globalB_addr ∗
    "HglobalB" ∷ globalB_addr ↦ (default_val go_string) ∗
    "#HglobalA_addr" ∷ is_global_addr globals_test.globalA globalA_addr ∗
    "HglobalA" ∷ globalA_addr ↦ (default_val go_string) ∗
    "#HglobalY_addry" ∷ is_global_addr globals_test.globalY globalY_addr ∗
    "HglobalY" ∷ globalY_addr ↦ (default_val go_string) ∗
    "#HGlobalX_addr" ∷ is_global_addr globals_test.GlobalX GlobalX_addr ∗
    "HGlobalX" ∷ GlobalX_addr ↦ (default_val w64)
.

Lemma wp_define' :
  {{{ own_unused_vars globals_test.pkg_name' ∅ }}}
    globals_test.define' #()
  {{{ vars, RET #();
      own_defined ∗
      own_unused_vars globals_test.pkg_name' vars
  }}}.
Proof.
  iIntros (?) "Hunused HΦ".
  wp_call.
  rewrite -!default_val_eq_zero_val /=.

  wp_alloc globalB_ptr as "?".
  wp_apply (wp_globals_put with "[Hunused]"); [| iFrame |]; [set_solver | ].
  iIntros "[Hunused #?]".
  wp_pures.

  wp_alloc globalA_ptr as "?".
  wp_apply (wp_globals_put with "[Hunused]"); [| iFrame |]; [set_solver | ].
  iIntros "[Hunused #?]".
  wp_pures.

  wp_alloc globalY_ptr as "?".
  wp_apply (wp_globals_put with "[Hunused]"); [| iFrame |]; [set_solver | ].
  iIntros "[Hunused #?]".
  wp_pures.

  wp_alloc GlobalX_ptr as "?".
  wp_apply (wp_globals_put with "[Hunused]"); [| iFrame |]; [set_solver | ].
  iIntros "[Hunused #?]".
  wp_pures.

  iApply "HΦ".
  iFrame "#∗".
Qed.

Definition own_initialized : iProp Σ :=
  ∃ globalB_addr globalA_addr globalY_addr GlobalX_addr,
  "#HglobalB_addr" ∷ is_global_addr globals_test.globalB globalB_addr ∗
  "#HglobalA_addr" ∷ is_global_addr globals_test.globalA globalA_addr ∗
  "#HglobalY_addr" ∷ is_global_addr globals_test.globalY globalY_addr ∗
  "#HGlobalX_addr" ∷ is_global_addr globals_test.GlobalX GlobalX_addr ∗

  "HglobalB" ∷ globalB_addr ↦ "b"%go ∗
  "HglobalA" ∷ globalA_addr ↦ "a"%go ∗
  "HglobalY" ∷ globalY_addr ↦ ""%go ∗
  "HglobalX" ∷ GlobalX_addr ↦ (W64 10)
.

Lemma wp_initialize' pending postconds :
  globals_test.pkg_name' ∉ pending →
  postconds !! globals_test.pkg_name' = Some own_initialized →
  {{{ own_globals_tok pending postconds }}}
    globals_test.initialize' #()
  {{{ RET #(); is_initialized globals_test.pkg_name' own_initialized }}}.
Proof.
  iIntros (???) "Hunused HΦ".
  wp_call.
  wp_apply (wp_package_init with "[$]").
  { eassumption. }
  { set_solver. }
  { (* prove init function *)
    iIntros "Hvars Htok".
    wp_pures.
    wp_apply (wp_define' with "[$]").
    iIntros (?) "[Hdefined Hvars]".
    iMod ("Htok" with "[$]") as "Htok".
    iNamed "Hdefined".
    wp_pures.

    (* go into foo() *)
    wp_call.
    wp_apply (wp_globals_get with "[]"); first iFrame "#".
    wp_store.
    wp_pures.
    wp_apply (wp_globals_get with "[]"); first iFrame "#".
    wp_store.
    wp_pures.
    wp_apply (wp_globals_get with "[]"); first iFrame "#".
    wp_store.
    wp_pures.
    wp_apply (wp_globals_get with "[]"); first iFrame "#".
    wp_load.
    wp_pures.
    wp_apply (wp_globals_get with "[]"); first iFrame "#".
    wp_store.
    wp_pures.
    wp_apply (wp_globals_get with "[]"); first iFrame "#".
    wp_store.
    wp_pures.
    iFrame "Htok".
    iFrame "∗#".
  }
  iIntros "His Htok".
  iApply "HΦ".
  iFrame.
Qed.

Lemma wp_main :
  {{{ own_initialized }}}
  globals_test.main #()
  {{{ RET #(); True }}}.
Proof.
  iIntros (?) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_call.
  wp_call.
  wp_apply wp_globals_get; first iFrame "#".
  wp_store.
  wp_pures.
  wp_apply wp_globals_get; first iFrame "#".
  wp_load.
  wp_pures.
  wp_apply wp_globals_get; first iFrame "#".
  wp_load.
  wp_pures.
  by iApply "HΦ".
Qed.

End proof.

From Perennial.goose_lang Require Import adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require Import grove_ffi.adequacy.
From New.proof Require Import grove_prelude.
Section closed.

Definition globals_testΣ : gFunctors := #[heapΣ ; goGlobalsΣ].

Lemma globals_test_boot σ (g : goose_lang.global_state) :
  ffi_initgP g.(global_world) →
  ffi_initP σ.(world) g.(global_world) →
  σ.(globals) = ∅ → (* FIXME: this should be abstracted into a "goose_lang.init" predicate or something. *)
  dist_adequate_failstop [
      ((globals_test.initialize' #() ;; globals_test.main #())%E, σ) ] g (λ _, True).
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
    iMod (go_global_init
            (λ _, {[ globals_test.pkg_name' := own_initialized ]}) with "[$]") as
      (hGlobals) "[Hpost Hg]".
    iModIntro.
    iExists (λ _, True)%I.
    wp_apply (wp_initialize' with "[$]").
    { set_solver. }
    { rewrite lookup_singleton. done. }
    iIntros "Hinit".
    iMod (own_package_post_toks_get globals_test.pkg_name' with "[$]") as "[? _]".
    { set_solver. }
    iMod (is_initialized_get_post with "[$] [$]") as "Hinit".
    wp_pures.
    by wp_apply (wp_main with "[$]").
  }
  by iApply big_sepL_nil.
Qed.

Print Assumptions globals_test_boot.

End closed.
