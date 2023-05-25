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
  {{{ sl, RET (slice_val sl); is_slice sl byteT 1 (bool_le b) }}}
.
Proof.
Admitted.

Lemma wp_DecodeBool sl b q :
  {{{ is_slice sl byteT q (bool_le b) }}}
    DecodeBool (slice_val sl)
  {{{ RET #b; True }}}
.
Proof.
Admitted.

Lemma wp_EncodeUint64 x:
  {{{ True }}}
    EncodeUint64 #x
  {{{ sl, RET (slice_val sl); is_slice sl byteT 1 (u64_le x) }}}
.
Proof.
Admitted.

Lemma wp_DecodeUint64 sl x q :
  {{{ is_slice_small sl byteT q (u64_le x) }}}
    DecodeUint64 (slice_val sl)
  {{{ RET #x; is_slice_small sl byteT q (u64_le x) }}}
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
Context `{!heapGS Σ}.
Context `{!urpcregG Σ}.

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
      by iApply (is_slice_small_nil _ 1).
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
      by iDestruct (is_slice_to_small _ _ 1 with "Henc_req") as "$".
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
      by iDestruct (is_slice_to_small with "Henc_req") as "$".
    }
    by iApply big_sepM_empty.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End start_server_proof.
