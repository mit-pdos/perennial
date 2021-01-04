From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc_durable nondet kv_proof fmcounter_map.
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

Axiom wpc_Read : ∀ filename (q:Qp) content,
  {{{
      filename f↦{q} content
  }}}
    grove_ffi.Read #(str filename) @ 37 ; ⊤
  {{{
       s, RET slice_val s; typed_slice.is_slice s byteT 1 content ∗
                           filename f↦{q} content
  }}}
  {{{
      filename f↦{q} content
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

Definition u64_to_string : u64 -> string := λ u, NilZero.string_of_int (Z.to_int (int.Z u)).

(* Spec for U64ToString will be annoying *)
Axiom wp_U64ToString : ∀ (u:u64),
  {{{
       True
  }}}
    grove_ffi.U64ToString #u
  {{{
       RET #(str u64_to_string u); True
  }}}.


(* Proof for increment backed by kv service
   requires taking
 *)

Definition IncrCrashInvariant (seq:u64) (args:RPCValC) : iProp Σ :=
  "Hfown_oldv" ∷ (("incr_request_" +:+ u64_to_string seq) +:+ "_oldv") f↦ []
.

Lemma increment_core_indepotent (isrv:loc) (seq:u64) (args:RPCValC) :
  {{{
       IncrCrashInvariant seq args
      (* TODO: add ownership of kck so we can make RPCs with it *)
  }}}
    IncrServer__increment_core #isrv #seq (into_val.to_val args) @ 37 ; ⊤
  {{{
      RET #(); True
  }}}
  {{{
       IncrCrashInvariant seq args
  }}}.
Proof.
  iIntros (Φ Φc) "Hpre Hpost".
  wpc_call; first done.
  { iFrame. }
  unfold IncrCrashInvariant.
  iNamed "Hpre".
  iCache with "Hfown_oldv Hpost".
  {
    iDestruct "Hpost" as "[HΦc _]". iModIntro. by iApply "HΦc".
  }
  wpc_pures.

  wpc_bind (ref #0)%E.
  wpc_frame.
  wp_apply (wp_alloc_untyped); first done.
  iIntros (l) "Hl". iNamed 1.
  wpc_pures.

  wpc_bind (grove_ffi.U64ToString _).
  wpc_frame.
  wp_apply wp_U64ToString.
  iNamed 1.
  wpc_pures.

  wpc_apply (wpc_Read with "Hfown_oldv").
  iSplit.
  { (* Show that the crash obligation of the function we're calling implies our crash obligation *)
    iDestruct "Hpost" as "[Hpost _]".
    iModIntro. done.
  }
  iNext.
  iIntros (content) "[Hcontent_slice Hfown_oldv]".
  wpc_pures.

  wpc_bind (slice.len _).
  wpc_frame.
  wp_apply wp_slice_len.
  iNamed 1.

  wpc_pures.
  Search "is_slice".
  iDestruct (slice.is_slice_sz with "Hcontent_slice") as "%Hslice_len".
  simpl in Hslice_len.
  assert (int.Z content.(Slice.sz) = 0) as -> by word.
  destruct bool_decide eqn:Hs.
  {
    apply bool_decide_eq_true in Hs.
    iExFalso; iPureIntro.
    done.
  }

  (* case that no durable oldv chosen *)
  wpc_pures.

  (* Use has_encoding data [] ∨ ... in invariant *)

Admitted.

End incr_proof.
