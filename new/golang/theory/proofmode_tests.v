From New.golang Require Import theory.

Section mem.

Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Lemma failing_wp_load_error_message (x y : loc) Φ :
  y ↦ (W64 0) -∗
  WP (do: load_ty uint64T #x ;;; load_ty uint64T #y) {{ Φ }}.
Proof.
  iIntros "Hy".
  Fail wp_load.
  (*
Init.Tactic_failure (Init.Some message:(wp_load: could not find a points-to in context covering the address))
   *)
Abort.

End mem.
