From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc_durable nondet kv_proof fmcounter_map.
Require Import Decimal Ascii String DecimalString.
From Perennial.goose_lang Require Import ffi.grove_ffi.

Section incr_proof.

(* Proof for increment backed by another increment service
 *)

Context `{!heapG Σ}.
Context `{!filesysG Σ}.

Definition has_encoding_for_short_clerk data cid seq (args:RPCValC) :=
   has_encoding data [EncUInt64 cid ; EncUInt64 seq ; EncUInt64 args.1 ; EncUInt64 args.2.1].

Definition ProxyIncrCrashInvariant (seq:u64) (args:RPCValC) : iProp Σ :=
  ("Hfown_oldv" ∷ ("procy_incr_request_" +:+ u64_to_string seq) f↦ []) ∨
  ("Hfown_oldv" ∷ ∃ data cid sseq, ("procy_incr_request_" +:+ u64_to_string seq) f↦ data ∗
   ⌜has_encoding_for_short_clerk data cid sseq args⌝
   )
.

(* TODO: should probably make RPCValC to be nicer than (u64 * (u64 * ())); no need for the unit *)

(* TODO: these definitions should ultimately refer to incr_proof.v *)
Record incrservice_names := KVserviceGN {
  incr_rpcGN : rpc_names;
  (* fmcounter_map of key -> counter value *)
  incr_mapGN : gname;
}.

Axiom is_incrserver : incrservice_names → loc → iProp Σ.

Instance is_incrserver_pers γ incrserver : Persistent (is_incrserver γ incrserver).
Admitted.

Axiom own_incrclerk : incrservice_names → loc → loc → iProp Σ.

Variable γ:incrservice_names.

Context `{!kvserviceG Σ}.

Definition ProxyIncrServer_core_own (srv:loc) : iProp Σ :=
  ∃ (kck incrserver:loc),
  "Hkvserver" ∷ srv ↦[IncrProxyServer.S :: "incrserver"] #incrserver ∗
  "Hkck" ∷ srv ↦[IncrProxyServer.S :: "ick"] #kck ∗
  "His_kvserver" ∷ is_incrserver γ incrserver ∗
  "Hkck_own" ∷ own_incrclerk γ kck incrserver
  (* This is using the non-crash-safe version of kvserver in kv_proof.v *)
.

Lemma wp_DecodeShortTermIncrClerk cid seq args (isrv:loc) (content:Slice.t) data :
{{{
     is_slice content byteT 1 data ∗
     ⌜has_encoding_for_short_clerk data cid seq args⌝
}}}
  DecodeShortTermIncrClerk #isrv (slice_val content)
{{{
     c, RET #c; True
}}}.
Proof.
  iIntros (Φ) "[Hslice %Henc] HΦ".
  Opaque struct.t. (* TODO: put this here to avoid unfolding the struct defns all the way *)
  Opaque struct.get.
  wp_lam.
  wp_pures.
  iDestruct "Hslice" as "[Hsmall _]".
  wp_apply (wp_new_dec with "Hsmall"); first done.
  iIntros (decv) "His_dec".
  wp_pures.
  wp_apply (wp_ref_of_zero); first done.
  iIntros (ck) "Hck".
  wp_pures.
  iDestruct (struct_fields_split with "Hck") as "Hck".
  Transparent struct.t.
  iSimpl in "Hck".
  Opaque struct.t.
  iNamed "Hck".
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "His_dec").
  iIntros "His_dec".
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "His_dec").
  iIntros "His_dec".
  wp_storeField.
  Search "wp_getField".
  Check struct_fields_split.
  iDestruct (struct_fields_split ck 1 ShortTermIncrClerk.S with "[cid seq req incrserver]") as "Hck"; eauto.
  {
    admit.
  }
Admitted.

Lemma increment_proxy_core_indepotent (isrv:loc) (seq:u64) (args:RPCValC) :
  {{{
       ProxyIncrCrashInvariant seq args ∗
       ProxyIncrServer_core_own isrv
      (* TODO: add ownership of kck so we can make RPCs with it *)
  }}}
    IncrProxyServer__proxy_increment_core #isrv #seq (into_val.to_val args) @ 37 ; ⊤
  {{{
      RET #(); True
  }}}
  {{{
       ProxyIncrCrashInvariant seq args
  }}}.
Proof.
  Opaque struct.t. (* TODO: put this here to avoid unfolding the struct defns all the way *)
  iIntros (Φ Φc) "[HincrCrashInv Hisown] Hpost".
  wpc_call; first done.
  { iFrame. }
  unfold ProxyIncrCrashInvariant.
  iNamed "HincrCrashInv".
  iCache with "HincrCrashInv Hpost".
  {
    iDestruct "Hpost" as "[HΦc _]". iModIntro. by iApply "HΦc".
  }
  wpc_pures.

  wpc_bind (grove_ffi.U64ToString _).
  wpc_frame.
  wp_apply wp_U64ToString.
  iNamed 1.

  wpc_pures.

  wpc_bind (ref _)%E.
  wpc_frame.
  wp_apply (wp_ref_of_zero); first done.
  iIntros (ck) "Hck".
  iNamed 1.

  wpc_pures.

  iDestruct "HincrCrashInv" as "[Hcase|Hcase]".
  - iNamed "Hcase".
    iCache with "Hfown_oldv Hpost".
    { (* Re-prove crash obligation in the special case. Nothing interesting about this. *)
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc". by iLeft.
    }

    wpc_apply (wpc_Read with "Hfown_oldv").
    iSplit.
    { (* Show that the crash obligation of the function we're calling implies our crash obligation *)
      iDestruct "Hpost" as "[Hpost _]".
      iModIntro. iIntros. iApply "Hpost". by iLeft.
    }
    iNext.
    iIntros (content) "[Hcontent_slice Hfown_oldv]".
    wpc_pures.

    wpc_bind (slice.len _).
    wpc_frame.
    wp_apply wp_slice_len.
    iNamed 1.

    wpc_pures.
    iDestruct (slice.is_slice_sz with "Hcontent_slice") as "%Hslice_len".
    simpl in Hslice_len.
    assert (int.Z content.(Slice.sz) = 0) as -> by word.
    destruct bool_decide eqn:Hs.
    {
      apply bool_decide_eq_true in Hs.
      iExFalso; iPureIntro.
      done.
    }

    (* case that no durable short-term clerk was found *)
    wpc_pures.
    iNamed "Hisown".
    admit.
  - iNamed "Hcase".
    iCache with "Hfown_oldv Hpost".
    { (* Re-prove crash obligation in the special case. Nothing interesting about this. *)
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc". by iRight.
    }

    iNamed "Hfown_oldv".
    iDestruct "Hfown_oldv" as "[Hfown_oldv %Henc]".
    wpc_apply (wpc_Read with "Hfown_oldv").
    iSplit.
    { (* crash obligation of called implies our crash obligation *)
      iDestruct "Hpost" as "[Hpost _]".
      iModIntro. iIntros. iApply "Hpost". iRight.
      by iExists _, _, _; iFrame.
    }
    iNext.
    iIntros (content) "[Hcontent_slice Hfown_oldv]".

    iCache with "Hfown_oldv Hpost".
    { (* Prove crash obligation after destructing above; TODO: do this earlier *)
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc". iRight.
      by iExists _, _, _; iFrame.
    }
    wpc_pures.

    wpc_bind (slice.len _)%E.
    wpc_frame.
    wp_apply (wp_slice_len).
    iNamed 1.
    wpc_pures.

    iNamed "Hisown".

    destruct bool_decide eqn:Hlen.
    { (* Case: found old short-term clerk *)
      wpc_pures.

      wpc_bind (struct.loadF _ _ _)%E.
      wpc_frame.
      wp_loadField.
      iNamed 1.
      (* TODO: spec for DecodeShortTermIncrClerk, and then MakePreparedRequest *)
      admit.
    }
    {
      (* TODO: Use has_encoding_length and is_slize_sz to get contradiction *)
      iExFalso.
      admit.
    }
Admitted.

End incr_proof.
