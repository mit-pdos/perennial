From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.program_proof.lockservice Require Import lockservice_crash rpc_proof rpc_durable nondet kv_proof fmcounter_map.
Require Import Decimal Ascii String DecimalString.

Section incr_proof.
Context `{!heapG Σ}.

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

(* Spec for U64ToString will be annoying *)
Axiom wp_U64ToString : ∀ (u:u64),
  {{{
       True
  }}}
    grove_ffi.U64ToString #u
  {{{
       RET #(str NilZero.string_of_int (Z.to_int (int.Z u))); True
  }}}.


(* Proof for increment backed by kv service
   requires taking
 *)

Definition IncrCrashInvariant (args:RPCValC) : iProp Σ := True.

Lemma increment_core_indepotent (isrv:loc) (seq:u64) (args:RPCValC) :
  {{{
       IncrCrashInvariant args
  }}}
    IncrServer__increment_core #isrv #seq (into_val.to_val args) @ 37 ; ⊤
  {{{
      RET #(); True
  }}}
  {{{
       IncrCrashInvariant args
  }}}.
Proof.
  iIntros (Φ Φc) "Hpre Hpost".
  wpc_call; first done.
  { iFrame. }
  iCache with "Hpre Hpost".
  {
    iDestruct "Hpost" as "[HΦc _]". iModIntro. by iApply "HΦc".
  }
  wpc_pures.

  wpc_bind (ref #0)%E.
  wpc_frame.
  wp_apply (wp_alloc_untyped); first done.
  iIntros (l) "Hl". iNamed 1.
  wpc_pures.
  wpc_bind (ref _)%E.

  (* Use has_encoding data [] ∨ ... in invariant *)

Admitted.

End incr_proof.
