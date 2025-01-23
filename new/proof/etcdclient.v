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

(* TODO: data model also needs revision number. *)
Axiom kv_pointsto_revision : ∀ (key val : go_string) (rev : w64) , iProp Σ.
Axiom kv_pointsto : ∀ (key val : go_string) (rev : w64) , iProp Σ.

Axiom kv_pointsto_revision_persistent : ∀ key val rev, Persistent (kv_pointsto_revision key val rev).
Existing Instance kv_pointsto_revision_persistent.

Axiom kv_pointsto_get_revision :
  ∀ key val rev,
  ⊢ kv_pointsto key val rev -∗ kv_pointsto_revision key val rev.

Context {etcdN : namespace}.

Record PutOptions := mkPutOptions {
    prevKV: bool;
    ignoreValue : bool;
    ignoreLease : bool;
    val : list w8;
    leaseID : w64;
  }.

Axiom is_PutOptions : ∀ (o : PutOptions) (opts : list OpOption.t), iProp Σ.

Definition has_Put (kv : interface.t) : iProp Σ :=
  ∀ (ctx : context.Context.t)
    (key val : go_string)
    (opts : list OpOption.t)
    opts_sl
    putOptions,
  ∀ Φ,
  ⌜ putOptions = mkPutOptions false false false [] (W64 0) ⌝ →
  is_PutOptions putOptions opts -∗
  (|={⊤∖↑etcdN,∅}=> ∃ old_value old_rev, kv_pointsto key old_value old_rev ∗
   (∀ new_rev, ⌜ sint.Z new_rev > sint.Z old_rev ⌝ →
      kv_pointsto key val new_rev ={∅,⊤∖↑etcdN}=∗
      (∀ (resp_ptr : loc) (resp : PutResponse.t),
         resp_ptr ↦ resp -∗ Φ (#resp_ptr, #interface.nil)%V
      )
   )
  ) -∗
  (∀ (err : interface.t), ⌜ err ≠ interface.nil ⌝ → Φ (#null, #err)%V) -∗
  opts_sl ↦* opts -∗
  WP interface.get #kv #"Put" #ctx #key #val #opts_sl {{ Φ }}.

End specs.
