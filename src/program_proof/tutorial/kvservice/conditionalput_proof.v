From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Goose Require Import github_com.mit_pdos.gokv.tutorial.kvservice.conditionalput_gk.

Module conditionalPut.
Section conditionalPut.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        opId : u64;
        key : string;
        expectedVal : string;
        newVal : string;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(opId)) ++
              (u64_le $ length $ string_to_bytes args.(key)) ++ string_to_bytes args.(key) ++
              (u64_le $ length $ string_to_bytes args.(expectedVal)) ++ string_to_bytes args.(expectedVal) ++
              (u64_le $ length $ string_to_bytes args.(newVal)) ++ string_to_bytes args.(newVal).

Definition own (args_ptr:loc) (args:C) (q:dfrac) : iProp Σ :=
  "Hargs_opId" ∷ args_ptr ↦[conditionalput_gk.S :: "OpId"]{q} #args.(opId) ∗
  "Hargs_key" ∷ args_ptr ↦[conditionalput_gk.S :: "Key"]{q} #(str args.(key)) ∗
  "Hargs_expectedVal" ∷ args_ptr ↦[conditionalput_gk.S :: "ExpectedVal"]{q} #(str args.(expectedVal)) ∗
  "Hargs_newVal" ∷ args_ptr ↦[conditionalput_gk.S :: "NewVal"]{q} #(str args.(newVal)).

Lemma wp_Encode (args_ptr:loc) (args:C) (pre_sl:Slice.t) (prefix:list u8) :
  {{{
        own args_ptr args (DfracDiscarded) ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    conditionalput_gk.Marshal #args_ptr (slice_val pre_sl)
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) (prefix ++ enc)
  }}}.

Proof.
  iIntros (?) "H HΦ". iDestruct "H" as "[Hown Hsl]". iNamed "Hown".
  wp_rec. wp_pures.
  wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr". wp_pures.
  wp_loadField. wp_load. wp_apply (wp_WriteInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_loadField.
  wp_apply wp_StringToBytes. iIntros (?) "Hargs_key_enc". wp_pures.
  wp_apply (wp_slice_len).
  iDestruct (own_slice_sz with "Hargs_key_enc") as "%Hargs_key_sz".
  iApply own_slice_to_small in "Hargs_key_enc".
  wp_load. wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.
  wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hargs_key_enc]").
  iIntros (?) "[Hsl _]". wp_store.

  wp_loadField.
  wp_apply wp_StringToBytes. iIntros (?) "Hargs_expectedVal_enc". wp_pures.
  wp_apply (wp_slice_len).
  iDestruct (own_slice_sz with "Hargs_expectedVal_enc") as "%Hargs_expectedVal_sz".
  iApply own_slice_to_small in "Hargs_expectedVal_enc".
  wp_load. wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.
  wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hargs_expectedVal_enc]").
  iIntros (?) "[Hsl _]". wp_store.

  wp_loadField.
  wp_apply wp_StringToBytes. iIntros (?) "Hargs_newVal_enc". wp_pures.
  wp_apply (wp_slice_len).
  iDestruct (own_slice_sz with "Hargs_newVal_enc") as "%Hargs_newVal_sz".
  iApply own_slice_to_small in "Hargs_newVal_enc".
  wp_load. wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.
  wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hargs_newVal_enc]").
  iIntros (?) "[Hsl _]". wp_store.

  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

   done.
Qed.

Lemma wp_Decode enc enc_sl (args:C) (suffix:list u8) (q:dfrac):
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT q (enc ++ suffix)
  }}}
    conditionalput_gk.Unmarshal (slice_val enc_sl)
  {{{
        args_ptr suff_sl, RET (#args_ptr, suff_sl); own args_ptr args (DfracOwn 1) ∗
                                                    own_slice_small suff_sl byteT q suffix
  }}}.

Proof.
  iIntros (?) "[%Henc Hsl] HΦ". wp_rec.
  wp_apply wp_allocStruct; first by val_ty.
  iIntros (?) "Hstruct". wp_pures.
  wp_apply wp_ref_to; first done.
  iIntros (?) "Hptr". wp_pures.
  iDestruct (struct_fields_split with "Hstruct") as "HH".
  iNamed "HH".

  rewrite Henc. rewrite -?app_assoc.

  wp_load. wp_apply (wp_ReadInt with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_storeField. wp_store.

  wp_apply wp_ref_of_zero; first done. iIntros (keyLen) "HkeyLen". wp_pures.
  wp_apply wp_ref_of_zero; first done. iIntros (keyBytes) "HkeyBytes". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %Hkey_sz.
  wp_apply (wp_ReadBytes with "[$]").
  { rewrite length_app in Hkey_sz. word. }
  iIntros (??) "[Hkey' Hsl]".

  wp_pures. wp_store. wp_store. wp_load.
  wp_apply (wp_StringFromBytes with "[$Hkey']"). iIntros "_".
  wp_storeField.

  wp_apply wp_ref_of_zero; first done. iIntros (expectedValLen) "HexpectedValLen". wp_pures.
  wp_apply wp_ref_of_zero; first done. iIntros (expectedValBytes) "HexpectedValBytes". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %HexpectedVal_sz.
  wp_apply (wp_ReadBytes with "[$]").
  { rewrite length_app in HexpectedVal_sz. word. }
  iIntros (??) "[HexpectedVal' Hsl]".

  wp_pures. wp_store. wp_store. wp_load.
  wp_apply (wp_StringFromBytes with "[$HexpectedVal']"). iIntros "_".
  wp_storeField.

  wp_apply wp_ref_of_zero; first done. iIntros (newValLen) "HnewValLen". wp_pures.
  wp_apply wp_ref_of_zero; first done. iIntros (newValBytes) "HnewValBytes". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %HnewVal_sz.
  wp_apply (wp_ReadBytes with "[$]").
  { rewrite length_app in HnewVal_sz. word. }
  iIntros (??) "[HnewVal' Hsl]".

  wp_pures. wp_store. wp_store. wp_load.
  wp_apply (wp_StringFromBytes with "[$HnewVal']"). iIntros "_".
  wp_storeField.

  wp_load. wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
Qed.

End conditionalPut.
End conditionalPut.

