From New.proof Require Import grove_prelude.
From New.code.github_com.mit_pdos.gokv Require globals_test.
From Perennial.algebra Require Import map.
From New.proof Require Import std.

Section proof.

Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition is_defined : iProp Σ :=
  "HglobalB" ∷ ∃ globalB_addr, is_global_addr globals_test.globalB globalB_addr ∗
  "HglobalA" ∷ ∃ globalA_addr, is_global_addr globals_test.globalA globalA_addr ∗
  "HglobalY" ∷ ∃ globalY_addr, is_global_addr globals_test.globalY globalY_addr ∗
  "HGlobalX" ∷ ∃ GlobalX_addr, is_global_addr globals_test.GlobalX GlobalX_addr
.

Lemma wp_define' :
  {{{ own_unused_vars globals_test.pkg_name' ∅ }}}
    globals_test.define' #()
  {{{ RET #(); is_defined }}}.
Proof.
  iIntros (?) "Hunused HΦ".
  wp_call.
  rewrite -!default_val_eq_zero_val /=.

  wp_alloc globalB_ptr as "?".
  wp_apply (wp_globals_put with "[Hunused]"); [| | iFrame |]; [set_solver | reflexivity |].
  iIntros "[Hunused #?]".
  wp_pures.

  wp_alloc globalA_ptr as "?".
  wp_apply (wp_globals_put with "[Hunused]"); [| | iFrame |]; [set_solver| reflexivity |].
  iIntros "[Hunused #?]".
  wp_pures.

  wp_alloc globalY_ptr as "?".
  wp_apply (wp_globals_put with "[Hunused]"); [| | iFrame |]; [set_solver| reflexivity |].
  iIntros "[Hunused #?]".
  wp_pures.

  wp_alloc GlobalX_ptr as "?".
  wp_apply (wp_globals_put with "[Hunused]"); [| | iFrame |]; [set_solver| reflexivity |].
  iIntros "[Hunused #?]".
  wp_pures.

  iApply "HΦ".
  iFrame "#".
Qed.

Lemma wp_initialize' :
  {{{ True }}}
    globals_test.initialize' #()
  {{{ RET #(); True }}}.
Proof.
Admitted.

End proof.
