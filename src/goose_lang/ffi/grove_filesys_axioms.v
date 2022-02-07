From Perennial.goose_lang Require Export prelude ffi.grove_prelude.
From Perennial.goose_lang Require Export lang.
From iris.base_logic Require Import ghost_map.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Export prelude ffi.grove_ffi.

Class filesysG Σ := FileSysG {
  filesys_gname : gname ; (* Name of str -> []byte authmap used for filesys ffi *)
  filesys_inG :> ghost_mapG Σ string (list byte)
}.

Context `{!heapGS Σ}.

Definition file_mapsto {fG:filesysG Σ} (s:string) (c:list byte) (dq:dfrac): iProp Σ :=
  s ↪[filesys_gname]{dq} c.

Notation "s f↦{ q } c" := (file_mapsto s c q)
(at level 20, q at level 50, format "s  f↦{ q } c") : bi_scope.

Notation "s f↦ c" := (s f↦{DfracOwn 1} c)%I
(at level 20, format "s  f↦ c") : bi_scope.

Context `{!filesysG Σ}.

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

Axiom wpc_Write : ∀ filename content_old content (content_sl:Slice.t) dq,
  {{{
      filename f↦ content_old ∗
      typed_slice.is_slice content_sl byteT dq content
  }}}
    Write #(str filename) (slice_val content_sl) @ ⊤
  {{{
       RET #(); filename f↦ content ∗
      typed_slice.is_slice content_sl byteT dq content
  }}}
  {{{
      filename f↦ content_old ∨
      filename f↦ content
  }}}.
