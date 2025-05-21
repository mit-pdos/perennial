From Perennial.goose_lang.automation Require Import goose_lang_auto std_specs.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import marshal_proof marshal_stateless_proof.

#[global] Opaque marshal.NewEnc.
#[global] Opaque marshal.Enc__PutInt.
#[global] Opaque marshal.Enc__PutBytes.
#[global] Opaque marshal.Enc__Finish.
#[global] Opaque marshal.WriteInt.
#[global] Opaque marshal.ReadInt.
#[global] Opaque marshal.WriteBytes.
#[global] Opaque marshal.ReadBytes.
#[global] Opaque u64_le.
#[global] Opaque is_enc.

Section proofs.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  #[global] Instance NewEnc_spec (sz: w64) :
   SPEC
   {{ True }}
    marshal.NewEnc #sz
  {{ (enc_v:val), RET enc_v;
     is_enc enc_v (uint.Z sz) [] (uint.Z sz) }}.
  Proof.
    iSteps.
    wp_apply (wp_new_enc); auto.
  Qed.

  #[global] Instance Enc__PutInt_spec enc_v sz r (x: w64) remaining :
    SPEC
    {{ is_enc enc_v sz r remaining ∗ ⌜8 ≤ remaining⌝ }}
      marshal.Enc__PutInt enc_v #x
    {{ RET #(); is_enc enc_v sz (r ++ [EncUInt64 x]) (remaining - 8) }}.
  Proof.
    iSteps.
    wp_apply (wp_Enc__PutInt with "[$]"); auto.
  Qed.

  #[global] Instance Enc__PutBytes_spec enc_v r sz remaining b_s q bs :
    SPEC
  {{ is_enc enc_v sz r remaining ∗ own_slice_small b_s byteT q bs ∗ ⌜Z.of_nat (length bs) ≤ remaining⌝ }}
    marshal.Enc__PutBytes enc_v (slice_val b_s)
  {{ RET #(); is_enc enc_v sz (r ++ [EncBytes bs]) (remaining - Z.of_nat (length bs)) ∗
               own_slice_small b_s byteT q bs }}.
  Proof.
    iSteps.
    wp_apply (wp_Enc__PutBytes with "[$]"); auto.
  Qed.

  #[global] Instance Enc__Finish_spec enc_v r sz remaining :
      SPEC
    {{ is_enc enc_v sz r remaining }}
      marshal.Enc__Finish enc_v
    {{ s data, RET slice_val s; ⌜has_encoding data r⌝ ∗
                                ⌜length data = Z.to_nat sz⌝ ∗
                                own_slice s byteT (DfracOwn 1) data }}.
  Proof.
    iStep.
    wp_apply (wp_Enc__Finish with "[$]"); auto.
  Qed.

  #[global] Instance WriteInt_spec s vs (x: w64) :
    SPEC
      {{ own_slice s byteT (DfracOwn 1) vs }}
      marshal.WriteInt s #x
      {{ s', RET slice_val s'; own_slice s' byteT (DfracOwn 1) (vs ++ u64_le x) }}.
  Proof.
    iSteps.
    wp_apply (wp_WriteInt with "[$]").
    iSteps.
  Qed.

  #[global] Instance WriteBytes_spec s (vs : list u8) data_sl (data : list u8) :
    SPEC q,
    {{ own_slice s byteT (DfracOwn 1) vs ∗ own_slice_small data_sl byteT q data }}
      marshal.WriteBytes s data_sl
    {{ s', RET slice_val s';
      own_slice s' byteT (DfracOwn 1) (vs ++ data) ∗
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
