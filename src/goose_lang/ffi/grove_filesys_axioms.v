From Perennial.goose_lang Require Export prelude ffi.grove_prelude.
From Perennial.goose_lang Require Export lang.
From iris.base_logic Require Import ghost_map.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Export prelude ffi.grove_prelude.

Section filesys.
Context `{!heapGS Σ}.

Axiom wpc_Read : ∀ filename (dq:dfrac) content,
  {{{
      filename f↦{dq} content
  }}}
    Read #(str filename) @ ⊤
  {{{
       s, RET slice_val s; typed_slice.is_slice s byteT 1 content ∗
                           filename f↦{dq} content
  }}}
  {{{
      filename f↦{dq} content
  }}}.

Axiom wpc_Write : ∀ filename content_old content (content_sl:Slice.t) q {stk E},
  {{{
      filename f↦ content_old ∗
      typed_slice.is_slice_small content_sl byteT q content
  }}}
    Write #(str filename) (slice_val content_sl) @ stk ; E
  {{{
       RET #(); filename f↦ content ∗
      typed_slice.is_slice_small content_sl byteT q content
  }}}
  {{{
      filename f↦ content_old ∨
      filename f↦ content
  }}}.

Axiom wpc_AtomicAppend : ∀ filename content_old content (content_sl:Slice.t) q,
  {{{
      filename f↦ content_old ∗
      typed_slice.is_slice_small content_sl byteT q content
  }}}
    AtomicAppend #(str filename) (slice_val content_sl) @ ⊤
  {{{
       RET #(); filename f↦ (content_old ++ content) ∗
      typed_slice.is_slice_small content_sl byteT q (content_old ++ content)
  }}}
  {{{
      filename f↦ content_old ∨
      filename f↦ (content_old ++ content)
  }}}.

End filesys.
