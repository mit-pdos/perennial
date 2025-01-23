From New.proof Require Import proof_prelude.
Require Import New.generatedproof.structs.etcdclient.

Module context.
Module Context.
  Definition t `{ffi_syntax} := interface.t.
End Context.
End context.

Module OpOption.
  Definition t `{ffi_syntax} := func.t.
End OpOption.

Section specs.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Definition has_Put (kv : interface.t)
                   (ctx : context.Context.t)
                   (key val : go_string)
                   (opts : list OpOption.t)
  : iProp Σ :=
  ∀ opts_sl,
  {{{ opts_sl ↦* opts }}}
    interface.get #kv #ctx #key #val #opts_sl
  {{{ RET #(); True }}}
.

End specs.
