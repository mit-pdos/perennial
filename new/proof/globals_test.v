From New.proof Require Import grove_prelude.
From New.code.github_com.mit_pdos.gokv Require globals_test.
From Perennial.algebra Require Import map.

Section proof.

Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition own_defined : iProp Σ :=
  ∃ globalB_addr globalA_addr globalY_addr GlobalX_addr,
    "#HglobalB_addr" ∷ is_global_addr globals_test.globalB globalB_addr ∗
    "HglobalB" ∷ globalB_addr ↦ (default_val string) ∗
    "#HglobalA_addr" ∷ is_global_addr globals_test.globalA globalA_addr ∗
    "HglobalA" ∷ globalA_addr ↦ (default_val string) ∗
    "#HglobalY_addry" ∷ is_global_addr globals_test.globalY globalY_addr ∗
    "HglobalY" ∷ globalY_addr ↦ (default_val string) ∗
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

  "HglobalB" ∷ globalB_addr ↦ "b" ∗
  "HglobalA" ∷ globalA_addr ↦ "a" ∗
  "HglobalY" ∷ globalY_addr ↦ "" ∗
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
  { reflexivity. }
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

End proof.
