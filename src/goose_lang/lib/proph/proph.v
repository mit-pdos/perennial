From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode lifting.
From Perennial.goose_lang.lib Require Export proph.impl.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Theorem wp_NewProph_list :
  {{{ True }}}
    NewProph #()
  {{{ pvs (p : proph_id), RET #p; proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply wp_new_proph. auto.
Qed.

Theorem wp_ResolveProph_list (p : proph_id) pvs v :
  {{{ proph p pvs }}}
    ResolveProph (#p) (Val v)
  {{{ pvs', RET (LitV LitUnit); ⌜pvs = v::pvs'⌝ ∗ proph p pvs' }}}.
Proof.
  iIntros (Φ) "Hp HΦ". wp_lam.
  wp_apply (wp_resolve_proph with "Hp"). auto.
Qed.

End goose_lang.
