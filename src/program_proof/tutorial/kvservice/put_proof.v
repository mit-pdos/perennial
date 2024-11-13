From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Goose Require Import github_com.mit_pdos.gokv.tutorial.kvservice.put_gk.

Module put.
Section put.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        opId : u64;
        key : string;
        val : string;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(opId)) ++
              (u64_le $ length $ string_to_bytes args.(key)) ++ string_to_bytes args.(key) ++
              (u64_le $ length $ string_to_bytes args.(val)) ++ string_to_bytes args.(val).

Definition own (args_ptr:loc) (args:C) (q:dfrac) : iProp Σ :=
  "Hargs_opId" ∷ args_ptr ↦[put_gk.S :: "OpId"]{q} #args.(opId) ∗
  "Hargs_key" ∷ args_ptr ↦[put_gk.S :: "Key"]{q} #(str args.(key)) ∗
  "Hargs_val" ∷ args_ptr ↦[put_gk.S :: "Val"]{q} #(str args.(val)).

Lemma wp_Encode (args_ptr:loc) (args:C) (pre_sl:Slice.t) (prefix:list u8) :
  {{{
        own args_ptr args (DfracDiscarded) ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    put_gk.Marshal #args_ptr (slice_val pre_sl)
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
  wp_apply wp_StringToBytes. iIntros (?) "Hargs_val_enc". wp_pures.
  wp_apply (wp_slice_len).
  iDestruct (own_slice_sz with "Hargs_val_enc") as "%Hargs_val_sz".
  iApply own_slice_to_small in "Hargs_val_enc".
  wp_load. wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.
  wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hargs_val_enc]").
  iIntros (?) "[Hsl _]". wp_store.


  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding. 
  rewrite ?string_bytes_length.
  rewrite Hargs_key_sz.
  rewrite Hargs_val_sz.
  rewrite ?w64_to_nat_id. exact.
Qed.

Lemma wp_Decode enc enc_sl (args:C) (suffix:list u8) (q:dfrac):
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT q (enc ++ suffix)
  }}}
    put_gk.Unmarshal (slice_val enc_sl)
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

  wp_apply wp_ref_of_zero; first done. iIntros (valLen) "HvalLen". wp_pures.
  wp_apply wp_ref_of_zero; first done. iIntros (valBytes) "HvalBytes". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %Hval_sz.
  wp_apply (wp_ReadBytes with "[$]").
  { rewrite length_app in Hval_sz. word. }
  iIntros (??) "[Hval' Hsl]".

  wp_pures. wp_store. wp_store. wp_load.
  wp_apply (wp_StringFromBytes with "[$Hval']"). iIntros "_".
  wp_storeField.

  wp_load. wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
Qed.

End put.
End put.

