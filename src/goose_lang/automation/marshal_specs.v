From Perennial.goose_lang.automation Require Import goose_lang_auto std_specs.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import marshal_proof marshal_stateless_proof.

#[global] Opaque marshal.WriteInt.

Section proofs.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  #[global] Instance WriteInt_spec s vs (x: w64) :
    SPEC
      {{ own_slice s byteT 1 vs }}
      marshal.WriteInt s #x
      {{ s', RET slice_val s'; own_slice s' byteT 1 (vs ++ u64_le x) }}.
  Proof.
    iSteps.
    wp_apply (wp_WriteInt with "[$]").
    iSteps.
  Qed.

End proofs.
