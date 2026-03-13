From New.golang Require Import defn.

Module rand.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

(* runtime_rand is a Go runtime primitive (go:linkname runtime.rand).
   We model it as returning an arbitrary uint64. *)
Definition runtime_randⁱᵐᵖˡ : val :=
  λ: <>, ArbitraryInt.

End code.
End rand.
