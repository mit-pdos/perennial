From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.tutorial Require Import lockservice.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section marshal_proof.
Context `{!heapGS Σ}.

(* TODO: copied this naming convention from "u64_le". What does le actually
   mean? *)
Definition bool_le (b:bool) : list u8 := if b then [U8 1] else [U8 0].

Lemma wp_EncodeBool (b:bool) :
  {{{ True }}}
    EncodeBool #b
  {{{ sl, RET (slice_val sl); own_slice sl byteT 1 (bool_le b) }}}
.
Proof.
Admitted.

Lemma wp_DecodeBool sl b q :
  {{{ own_slice sl byteT q (bool_le b) }}}
    DecodeBool (slice_val sl)
  {{{ RET #b; True }}}
.
Proof.
Admitted.

Lemma wp_EncodeUint64 x:
  {{{ True }}}
    EncodeUint64 #x
  {{{ sl, RET (slice_val sl); own_slice sl byteT 1 (u64_le x) }}}
.
Proof.
Admitted.

Lemma wp_DecodeUint64 sl x q :
  {{{ own_slice_small sl byteT q (u64_le x) }}}
    DecodeUint64 (slice_val sl)
  {{{ RET #x; own_slice_small sl byteT q (u64_le x) }}}
.
Proof.
Admitted.

End marshal_proof.

Section rpc_definitions.
(* NOTE: "global" context because RPC specs are known by multiple machines. *)
Context `{!gooseGlobalGS Σ}.
Definition tryAcquire_core_spec (args:u64) (Φ:u64 → iPropO Σ): iPropO Σ.
Admitted.

Definition release_core_spec (args:u64) (Φ:iPropO Σ): iPropO Σ.
Admitted.

Definition getFreshNum_core_spec (Φ:u64 → iPropO Σ): iPropO Σ.
Admitted.

End rpc_definitions.

Section rpc_server_proofs.
Context `{!heapGS Σ}.
Lemma wp_Server__getFreshNum (s:loc) Ψ Φ :
  getFreshNum_core_spec Ψ -∗
  (∀ n, Ψ n -∗ Φ #n) -∗
  WP Server__getFreshNum #s {{ v, Φ v }}
.
Proof.
Admitted.

Lemma wp_Server__tryAcquire (s:loc) (args:u64) Ψ Φ :
  tryAcquire_core_spec args Ψ -∗
  (∀ err, Ψ err -∗ Φ #err) -∗
  WP Server__tryAcquire #s #args {{ v, Φ v }}
.
Proof.
Admitted.

Lemma wp_Server__release (s:loc) (args:u64) Ψ Φ :
  release_core_spec args Ψ -∗
  (Ψ -∗ Φ #()) -∗
  WP Server__release #s #args {{ v, Φ v }}
.
Proof.
Admitted.

End rpc_server_proofs.

Section encoded_rpc_definitions.
(* This section is boilerplate. *)
Context `{!gooseGlobalGS Σ}.
Context `{!urpcregG Σ}.

Program Definition getFreshNum_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (
  getFreshNum_core_spec (λ num, ∀ enc_reply, ⌜enc_reply = u64_le num⌝ -∗ Φ enc_reply)
  )%I
.
Next Obligation.
  (* solve_proper.
Defined. *)
Admitted.

Program Definition tryAcquire_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args,
   ⌜enc_args = u64_le args⌝ ∗
   tryAcquire_core_spec args (λ err, ∀ enc_reply, ⌜enc_reply = u64_le err⌝ -∗ Φ enc_reply)
  )%I
.
Next Obligation.
  (* solve_proper.
Defined. *)
Admitted.

Program Definition release_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args,
   "%Henc" ∷ ⌜enc_args = u64_le args⌝ ∗
   release_core_spec args (Φ [])
  )%I
.
Next Obligation.
  (* solve_proper.
Defined. *)
Admitted.

Definition is_lockserver_host host : iProp Σ :=
  ∃ γrpc,
  "#H1" ∷ handler_spec γrpc host (U64 0) getFreshNum_spec ∗
  "#H2" ∷ handler_spec γrpc host (U64 1) tryAcquire_spec ∗
  "#H3" ∷ handler_spec γrpc host (U64 2) release_spec ∗
  "#Hdom" ∷ handlers_dom γrpc {[ U64 0; U64 1; U64 2 ]}
  .

End encoded_rpc_definitions.

Section start_server_proof.
(* This section is boilerplate. *)
Context `{!heapGS Σ}.
Context `{!urpcregG Σ}.

Lemma wp_Server__Start (s:loc) (host:u64) :
  {{{
        "#Hhost" ∷ is_lockserver_host host
  }}}
    Server__Start #s #host
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  (* begin symbolic execution *)
  wp_lam.
  wp_pures.
  wp_apply (map.wp_NewMap).
  iIntros (handlers) "Hhandlers".

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_apply (urpc_proof.wp_MakeServer with "Hhandlers").
  iIntros (r) "Hr".
  wp_pures.

  iNamed "Hhost".
  wp_apply (wp_StartServer2 with "[$Hr]").
  { set_solver. }
  { (* Here, we show that the functions being passed in Go inside `handlers`
       satisfy the spec they should. *)
    (* First, show that the functions passed in are ALL the RPCs this host is
       suppose to provide. *)
    unfold handlers_complete.
    repeat rewrite dom_insert_L.
    rewrite dom_empty_L.
    iSplitL "".
    { iExactEq "Hdom". f_equal. set_solver. }

    (* Now show the RPC specs, one at a time *)
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold impl_handler_spec2.
      iIntros (?????) "!# Hreq_sl Hrep HΦ Hspec".
      wp_pures.
      iDestruct "Hspec" as (?) "[%Henc Hspec]". subst.
      wp_apply (wp_DecodeUint64 with "[$]").
      iIntros "Hreq_sl".
      wp_apply (wp_Server__release with "[$]").
      iIntros "HΨ".
      wp_pures.
      iApply ("HΦ" with "[$] [$]").
      by iApply (own_slice_small_nil _ 1).
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold impl_handler_spec2.
      iIntros (?????) "!# Hreq_sl Hrep HΦ Hspec".
      wp_pures.
      iDestruct "Hspec" as (?) "[%Henc Hspec]". subst.
      wp_apply (wp_DecodeUint64 with "[$]").
      iIntros "Hreq_sl".
      wp_apply (wp_Server__tryAcquire with "[$]").
      iIntros (?) "HΨ".
      wp_apply wp_EncodeUint64.
      iIntros (?) "Henc_req".
      wp_store.
      iApply ("HΦ" with "[HΨ] [$]").
      { iApply "HΨ". done. }
      by iDestruct (own_slice_to_small _ _ 1 with "Henc_req") as "$".
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold impl_handler_spec2.
      iIntros (?????) "!# Hreq_sl Hrep HΦ Hspec".
      wp_pures.
      iEval (rewrite /getFreshNum_spec /=) in "Hspec".
      wp_apply (wp_Server__getFreshNum with "[$]").
      iIntros (?) "HΨ".
      wp_apply wp_EncodeUint64.
      iIntros (?) "Henc_req".
      wp_store.
      iApply ("HΦ" with "[HΨ] [$]").
      { iApply "HΨ". done. }
      by iDestruct (own_slice_to_small with "Henc_req") as "$".
    }
    by iApply big_sepM_empty.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End start_server_proof.

Section client_proof.
(* This section is boilerplate. *)
Context `{!heapGS Σ, !urpcregG Σ}.
Definition is_Client (cl:loc) : iProp Σ :=
  ∃ (urpcCl:loc) host,
  "#Hcl" ∷ readonly (cl ↦[Client :: "cl"] #urpcCl) ∗
  "#HurpcCl" ∷ is_uRPCClient urpcCl host ∗
  "#Hhost" ∷ is_lockserver_host host
.

Lemma wp_Client__getFreshNum cl Φ :
  is_Client cl -∗
  □ getFreshNum_core_spec (λ num, Φ (#num, #0)%V) -∗
  (∀ (err:u64), ⌜err ≠ U64 0⌝ -∗ Φ (#0, #err)%V ) -∗
  WP Client__getFreshNum #cl {{ Φ }}
.
Proof.
  iIntros "Hcl #Hspec Herr".
  (* symbolic execution *)
  wp_lam.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.
  wp_apply (wp_NewSlice).
  iIntros (?) "Hreq_sl".
  wp_pures.
  iNamed "Hcl".
  wp_loadField.
  iNamed "Hhost".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".
  wp_apply (wp_Client__Call2' with "[$] [$H1] [$] [$] [Hspec]").
  {
    iModIntro. iModIntro.
    rewrite replicate_0.
    rewrite /getFreshNum_spec /=.
    iFrame "#".
    (* FIXME: want to know that
       Φ -∗ Ψ, core_spec Ψ ⊢ core_spec Φ,
       i.e. that core_spec is contravariant.
     *)
    admit.
  }
Admitted.

End client_proof.

Section clerk_proof.
Context `{!heapGS Σ}.
Context `{!urpcregG Σ}.

Definition is_Clerk (ck:loc) : iProp Σ :=
  ∃ (cl:loc),
  "#Hcl" ∷ readonly (ck ↦[Clerk :: "rpcCl"] #cl) ∗
  "#HisCl" ∷ is_Client cl
.

Definition is_Locked (ck:loc) : iProp Σ :=
  ∃ (cl:loc) (n:u64),
  "#Hcl" ∷ readonly (ck ↦[Locked :: "rpcCl"] #cl) ∗
  "#Hid" ∷ readonly (ck ↦[Locked :: "id"] #n)
.

Lemma wp_Clerk__Acquire (ck:loc) :
  {{{ is_Clerk ck }}}
    Clerk__Acquire #ck
  {{{ (l:loc), RET #l; is_Locked l }}}
.
Proof.
  iIntros (Φ) "#Hck HΦ".
  wp_lam.
  (* symbolic execution *)
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (id_ptr) "Hid".
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (err_ptr) "Herr".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (l) "Hl".
  wp_pures.

  wp_forBreak.
  wp_pures.
  iNamed "Hck".
  wp_loadField.
  wp_apply (wp_Client__getFreshNum with "[$]").
  2:{ (* case: error *)
    iIntros (err) "%Herr". wp_pures.
    wp_store.
    wp_store.
    wp_load.
    wp_pures.
    wp_if_destruct.
    {
      iModIntro. iLeft.
      iSplitR; first done.
      iFrame.
      admit. (* TODO: weaken loop inv for err *)
    }
    by exfalso.
  }
  (* case: successful RPC *)
  iModIntro.
  (* TODO: put resources in front of Φ with wp_wand(_frame?) *)
Admitted.

Lemma wp_Locked__Release (l:loc) :
  {{{ is_Locked l }}}
    Locked__Release #l
  {{{ RET #(); True }}}
.
Proof.
Admitted.

End clerk_proof.
