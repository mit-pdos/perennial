From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Goose Require Import github_com.mit_pdos.gokv.tutorial.objectstore.dir.recordchunk_gk.

Module recordChunk.
Section recordChunk.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        writeId : u64;
        server : u64;
        contentHash : string;
        index : u64;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(writeId)) ++
              (u64_le args.(server)) ++
              (u64_le $ length $ string_to_bytes args.(contentHash)) ++ string_to_bytes args.(contentHash) ++
              (u64_le args.(index)).

Definition own (args_ptr: loc) (args: C) (dq: dfrac) : iProp Σ :=
  "Hargs_writeId" ∷ args_ptr ↦[recordchunk_gk.S :: "WriteId"]{dq} #args.(writeId) ∗
  "Hargs_server" ∷ args_ptr ↦[recordchunk_gk.S :: "Server"]{dq} #args.(server) ∗
  "Hargs_contentHash" ∷ args_ptr ↦[recordchunk_gk.S :: "ContentHash"]{dq} #(str args.(contentHash)) ∗
  "Hargs_index" ∷ args_ptr ↦[recordchunk_gk.S :: "Index"]{dq} #args.(index).

Lemma wp_Encode (args_ptr:loc) (args:C) (pre_sl:Slice.t) (prefix:list u8) (dq: dfrac):
  {{{
        own args_ptr args dq ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    recordchunk_gk.Marshal #args_ptr (slice_val pre_sl)
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        own args_ptr args dq ∗
        own_slice enc_sl byteT (DfracOwn 1) (prefix ++ enc)
  }}}.

Proof.
  iIntros (?) "H HΦ". iDestruct "H" as "[Hown Hsl]". iNamed "Hown".
  wp_rec. wp_pures.
  wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "Hptr". wp_pures.
  wp_loadField. wp_load. wp_apply (wp_WriteInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.
  wp_loadField. wp_load. wp_apply (wp_WriteInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_loadField.
  wp_apply wp_StringToBytes. iIntros (?) "Hargs_contentHash_enc". wp_pures.
  wp_apply (wp_slice_len).
  iDestruct (own_slice_sz with "Hargs_contentHash_enc") as "%Hargs_contentHash_sz".
  iApply own_slice_to_small in "Hargs_contentHash_enc".
  wp_load. wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.
  wp_load. wp_apply (wp_WriteBytes with "[$Hsl $Hargs_contentHash_enc]").
  iIntros (?) "[Hsl _]". wp_store.
  wp_loadField. wp_load. wp_apply (wp_WriteInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.


  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

  unfold has_encoding. 
  rewrite ?string_bytes_length.
  rewrite Hargs_contentHash_sz.
  rewrite ?w64_to_nat_id. exact.

Qed.

Lemma wp_Decode enc enc_sl (args: C) (suffix: list u8) (dq: dfrac):
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT dq (enc ++ suffix)
  }}}
    recordchunk_gk.Unmarshal (slice_val enc_sl)
  {{{
        args_ptr suff_sl, RET (#args_ptr, suff_sl); own args_ptr args (DfracOwn 1) ∗
                                                    own_slice_small suff_sl byteT dq suffix
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

  wp_load. wp_apply (wp_ReadInt with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_storeField. wp_store.

  wp_apply wp_ref_of_zero; first done. iIntros (contentHashLen) "HcontentHashLen". wp_pures.
  wp_apply wp_ref_of_zero; first done. iIntros (contentHashBytes) "HcontentHashBytes". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %HcontentHash_sz.
  wp_apply (wp_ReadBytes with "[$]").
  { rewrite length_app in HcontentHash_sz. word. }
  iIntros (??) "[HcontentHash' Hsl]".

  wp_pures. wp_store. wp_store. wp_load.
  wp_apply (wp_StringFromBytes with "[$HcontentHash']"). iIntros "_".
  wp_storeField.

  wp_load. wp_apply (wp_ReadInt with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_storeField. wp_store.

  wp_load. wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
Qed.

End recordChunk.
End recordChunk.

