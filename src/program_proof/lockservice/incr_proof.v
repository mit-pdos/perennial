From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.lockservice Require Import lockservice_crash nondet.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section incr_proof.
Context `{!heapG Σ}.

Definition IncrCrashInvariant : iProp Σ := True.

Class filesysG Σ := FileSysG {
  filesys_gname : gname ; (* Name of str -> []byte authmap used for filesys ffi *)
  filesys_inG :> mapG Σ string (list byte)
}.

Definition file_mapsto {fG:filesysG Σ} (s:string) (c:list byte) (q:Qp): iProp Σ :=
  s [[filesys_gname]]↦{q} c.

Context `{!filesysG Σ}.

Notation "s f↦{ q } c" := (file_mapsto s c q)
(at level 20, q at level 50, format "s  f↦{ q } c") : bi_scope.

Notation "s f↦ c" := (s f↦{1} c)%I
(at level 20, format "s  f↦ c") : bi_scope.

Axiom wp_Read : ∀ filename (q:Qp) content,
  {{{
      filename f↦{q} content
  }}}
    grove_ffi.Read #(str filename)
  {{{
       s, RET slice_val s; typed_slice.is_slice s byteT 1 content
  }}}.

Axiom wp_Write : ∀ filename (q:Qp) content_old content (content_sl:Slice.t) q,
  {{{
      filename f↦ content_old ∗
      typed_slice.is_slice content_sl byteT q content
  }}}
    grove_ffi.Write #(str filename) (slice_val content_sl)
  {{{
       RET #(); filename f↦ content ∗
      typed_slice.is_slice content_sl byteT q content
  }}}.

Require Import Decimal Ascii String DecimalString.
Search "string_of_uint".

(* Spec for U64ToString will be annoying *)
Axiom wp_U64ToString : ∀ (u:u64),
  {{{
       True
  }}}
    grove_ffi.U64ToString #u
  {{{
       RET #(str NilZero.string_of_int (Z.to_int (int.Z u))); True
  }}}.

Lemma increment_core_indepotent (isrv:loc) (seq args:u64) :
  {{{
       IncrCrashInvariant
  }}}
    IncrServer__increment_core #isrv #seq #args @ 37 ; ⊤
  {{{
      RET #(); True
  }}}
  {{{
       IncrCrashInvariant
  }}}.
Proof.
Admitted.

End incr_proof.
