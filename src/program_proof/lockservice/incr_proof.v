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

Variable γ:kvservice_names.

Context `{!kvserviceG Σ}.

(* This is the double-fupd crash obligation. *)
Definition KVGetPreClientWeak (cid:u64) (γrpc:durable_rpc_names) (PreCond:iProp Σ): iProp Σ :=
  ∀ (seq:u64), cid fm[[γrpc.(cseq)]]↦ int.nat seq ={⊤}=∗ (
            cid fm[[γrpc.(cseq)]]↦ int.nat seq ∗
                   (own γrpc.(proc) (Excl ()) ∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq) ={⊤}=∗ own γrpc.(proc) (Excl ()) ∗ PreCond
  ).
(*
  Should use up previous γPost to prove this fupd.
  We want to be able to show
 *)

Definition IdempotentPre γrpc (cid seq:u64) (PreCond : RPCValC → iProp Σ) : (RPCValC → iProp Σ) :=
  λ (args:RPCValC),
        (own γrpc.(proc) (Excl ()) -∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq ={⊤}=∗ own γrpc.(proc) (Excl ()) ∗ PreCond args)%I.

Lemma server_takes_idempotent_request γrpc γPost γPre (cid key va:u64) PreCond PostCond req lastSeqM lastReplyM:
  (int.Z (map_get lastSeqM req.(Req_CID)).1 < int.Z req.(Req_Seq))%Z →
  is_durable_RPCServer γrpc -∗
  is_durable_RPCRequest γrpc γPost γPre (IdempotentPre γrpc req.(Req_CID) req.(Req_Seq) PreCond) (PostCond) req -∗
  RPCServer_durable_own γrpc lastSeqM lastReplyM ={⊤}=∗
  PreCond req.(Req_Args) ∗
  RPCServer_durable_own_processing γrpc req lastSeqM lastReplyM.
Proof.
  intros Hrseq.
  iIntros "HserverInv HreqInv Hsown".

  iInv "HreqInv" as "[#>Hreqeq_lb Hcases]" "HMClose".
  iNamed "Hsown".

  iDestruct "Hcases" as "[[>Hunproc [>Hbad|Hpre]]|[#>Hlseq_lb _]]".
  {
    iDestruct (own_valid_2 with "Hproc_own Hbad") as %H; contradiction.
  }
  {
    iDestruct "Hpre" as "[>HγPre HidemPre]".
    iSpecialize ("HidemPre" with "[Hproc_own]").
    {  done. }
    (* Expectedly stuck trying to show req.cid fm[lseq]≥ req.seq to use the
       HidemPre fupd Indeed, we won't be able to take PreCond out of the old
       request until we actually update the seqno on durable storage. Otherwise,
       we could be holding the proc token, so we know no one else is currently
       processing the old request, then we steal PreCond from the old request
       invariant, then we could crash before we update lastSeq, and then after
       restarting, the old request might *actually* be run again, so it needs
       its PreCond.

       So, we can only actually get the PreCond as soon as we actually update
       the lastSeq. This means the core function would not be given [PreCond], but
       [(own proc ∗ fm[lseq]≥ fact) ={⊤}=∗ PreCond].

       This'll also mean the fupd where we go from PreCond -> PostCond must
       happen at the same time as the lseq update.
     *)
Admitted.


Definition IncrServer_core_own (srv:loc) : iProp Σ :=
  ∃ (kck kvserver:loc),
  "Hkvserver" ∷ srv ↦[IncrServer.S :: "kvserver"] #kvserver ∗
  "Hkck" ∷ srv ↦[IncrServer.S :: "kck"] #kck ∗
  "His_kvserver" ∷ is_kvserver γ kvserver ∗
  "Hkck_own" ∷ own_kvclerk γ kck kvserver
  (* This is using the non-crash-safe version of kvserver in kv_proof.v *)
  .

Lemma increment_core_indepotent (isrv:loc) (seq:u64) (args:RPCValC) :
  {{{
       IncrCrashInvariant seq args ∗
                        IncrServer_core_own isrv
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
  iIntros (Φ Φc) "[HincrCrashInv Hisown] Hpost".
  wpc_call; first done.
  { iFrame. }
  unfold IncrCrashInvariant.
  iNamed "HincrCrashInv".
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
  iNamed "Hisown".

  wpc_bind (struct.loadF _ _ _).
  wpc_frame.
  wp_loadField.
  iNamed 1.

  (* Use has_encoding data [] ∨ ... in invariant *)

Admitted.

End incr_proof.
