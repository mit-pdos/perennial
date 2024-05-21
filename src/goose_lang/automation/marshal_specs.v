From Perennial.goose_lang.automation Require Import goose_lang_auto std_specs.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import marshal_proof marshal_stateless_proof.

#[global] Opaque marshal.WriteInt.
#[global] Opaque marshal.ReadInt.
#[global] Opaque marshal.WriteBytes.
#[global] Opaque marshal.ReadBytes.
#[global] Opaque u64_le.

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

  #[global] Instance WriteBytes_spec s (vs : list u8) data_sl (data : list u8) :
    SPEC q,
    {{ own_slice s byteT 1 vs ∗ own_slice_small data_sl byteT q data }}
      marshal.WriteBytes s data_sl
    {{ s', RET slice_val s';
      own_slice s' byteT 1 (vs ++ data) ∗
      own_slice_small data_sl byteT q data
    }}.
  Proof. iSteps. wp_apply (wp_WriteBytes with "[$]"). iSteps. Qed.

  #[global] Instance ReadInt_spec s (bs: list w8) (x: w64) :
    SPEC q,
      {{ own_slice_small s byteT q (u64_le x ++ bs) }}
      marshal.ReadInt s
      {{ s', RET (#x, s')%V; own_slice_small s' byteT q bs }}.
  Proof.
    iSteps.
    wp_apply (wp_ReadInt with "[$]"). iSteps.
  Qed.

  #[global] Instance ReadBytes_spec s (len: w64) :
   SPEC q (bs bs': list w8),
      {{ own_slice_small s byteT q (bs ++ bs') ∗ ⌜length bs = uint.nat len⌝  }}
         marshal.ReadBytes s #len
      {{ b s' q', RET (b, s')%V; own_slice_small b byteT q' bs ∗
           own_slice_small s' byteT q' bs' }}.
  Proof.
    iSteps.
    wp_apply (wp_ReadBytes with "[$]").
    { done. }
    iSteps.
  Qed.

End proofs.

Ltac len_simpl := autorewrite with len in *.
Hint Extern 2 (_ = _) => (progress len_simpl) : solve_pure_eq_add.
Hint Extern 2 (_ = _) => word : solve_pure_eq_add.
