From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Goose Require Import github_com.mit_pdos.gokv.tutorial.objectstore.chunk.writechunk_gk.

Module writeChunk.
Section writeChunk.

Typeclasses Opaque app.

Context `{!heapGS Σ}.

Record C :=
    mkC {
        writeId : u64;
        chunk : list u8;
        index : u64;
        }.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(writeId)) ++
              (u64_le $ length $ args.(chunk)) ++ args.(chunk) ++
              (u64_le args.(index)).

Definition own (args_ptr:loc) (args:C) (q:dfrac) : iProp Σ :=(chunk_sl : Slice.t)
  "Hargs_writeId" ∷ args_ptr ↦[writechunk_gk.S :: "WriteId"]{q} #args.(writeId) ∗
  "Hargs_chunk" ∷ args_ptr ↦[writechunk_gk.S :: "Chunk"]{q} (slice_val chunk_sl) ∗
  "Hargs_chunk_sl" ∷ own_slice_small chunk_sl byteT q args.(chunk)
   ∗
  "Hargs_index" ∷ args_ptr ↦[writechunk_gk.S :: "Index"]{q} #args.(index).

Lemma wp_Encode (args_ptr:loc) (args:C) (pre_sl:Slice.t) (prefix:list u8) :
  {{{
        own args_ptr args (DfracDiscarded) ∗
        own_slice pre_sl byteT (DfracOwn 1) prefix
  }}}
    writechunk_gk.Marshal #args_ptr (slice_val pre_sl)
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


  iDestruct (own_slice_small_sz with "Hargs_chunk_enc") as "%Hargs_chunk_sz".
  wp_loadField. wp_load. wp_apply wp_slice_len. wp_load.
  wp_apply (wp_WriteInt with "[$Hsl]"). iIntros (?) "Hsl". wp_store.

  wp_loadField. wp_load. wp_load.
  wp_apply (wp_WriteBytes with "[$Hsl $Hargs_chunk_enc]").
  iIntros (?) "[Hsl _]". wp_store.
  wp_loadField. wp_load. wp_apply (wp_WriteInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_store.

  wp_load. iApply "HΦ". iModIntro. rewrite -?app_assoc.
  iFrame. iPureIntro.

   done.
Qed.

Lemma wp_Decode enc enc_sl (args:C) (suffix:list u8) (q:dfrac):
  {{{
        ⌜has_encoding enc args⌝ ∗
        own_slice_small enc_sl byteT q (enc ++ suffix)
  }}}
    writechunk_gk.Unmarshal (slice_val enc_sl)
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

  wp_apply wp_allocN; first done; first by val_ty.
  iIntros (?) "HchunkLen". iApply array_singleton in "HchunkLen". wp_pures.
  wp_apply wp_allocN; first done; first by val_ty.
  iIntros (?) "Hchunk". iApply array_singleton in "Hchunk". wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures. wp_store. wp_store. wp_load. wp_load.

  iDestruct (own_slice_small_sz with "Hsl") as %Hchunk_sz.
  wp_apply (wp_ReadBytesCopy with "[$]").
  { rewrite length_app in Hchunk_sz. word. }
  iIntros (??) "[Hchunk' Hsl]". iApply own_slice_to_small in "Hchunk'".

  wp_pures. wp_store. wp_store. wp_storeField.

  wp_load. wp_apply (wp_ReadInt with "[$Hsl]"). iIntros (?) "Hsl".
  wp_pures. wp_storeField. wp_store.

  wp_load. wp_pures. iApply "HΦ". iModIntro. rewrite ?string_to_bytes_to_string. iFrame.
Qed.

End writeChunk.
End writeChunk.

