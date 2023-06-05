From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.tutorial Require Import kvservice.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.

(********************************************************************************)

(* FIXME: move this somewhere else *)
Fixpoint string_le (s:string): list u8 :=
  match s with
  | EmptyString => []
  | String x srest => [U8 (Ascii.nat_of_ascii x)] ++ (string_le srest)
  end
.

Axiom wp_stringToBytes :
  ∀ `{!heapGS Σ} (s:string),
  {{{
        True
  }}}
    prelude.Data.stringToBytes #(str s)
  {{{
        (sl:Slice.t), RET (slice_val sl); own_slice sl byteT 1 (string_le s)
  }}}
.

Axiom wp_bytesToString :
  ∀ `{!heapGS Σ} sl q (s:string),
  {{{
        own_slice_small sl byteT q (string_le s)
  }}}
    prelude.Data.bytesToString #(str s)
  {{{
        RET #(str s); own_slice_small sl byteT q (string_le s)
  }}}
.

Module putArgs.
Record t :=
  mk {
      opId: u64 ;
      key: string ;
      val: string ;
  }.

Definition encodes (x:list u8) (a:t) : Prop :=
  x = u64_le a.(opId) ++ (u64_le $ length $ string_le a.(key)) ++
      string_le a.(key) ++ string_le a.(val)
.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (a:loc) (args:t) : iProp Σ :=
  "HopId" ∷ a ↦[putArgs :: "opId"] #args.(opId) ∗
  "Hkey" ∷ a ↦[putArgs :: "key"] #(str args.(key)) ∗
  "Hval" ∷ a ↦[putArgs :: "val"] #(str args.(val))
.

Lemma wp_encode args_ptr args :
  {{{
        own args_ptr args
  }}}
    encodePutArgs #args_ptr
  {{{
        (sl:Slice.t) enc_args, RET (slice_val sl); own args_ptr args ∗
          ⌜encodes enc_args args⌝ ∗
          own_slice sl byteT 1 enc_args
  }}}
.
Proof.
Admitted.

Lemma wp_decode  sl enc_args args q :
  {{{
        ⌜encodes enc_args args⌝ ∗
        own_slice_small sl byteT q enc_args
  }}}
    decodePutArgs (slice_val sl)
  {{{
        (args_ptr:loc), RET #args_ptr; own args_ptr args ∗
                                       own_slice_small sl byteT q enc_args
  }}}
.
Proof.
Admitted.

End local_defs.
End putArgs.

Module conditionalPutArgs.
Record t :=
  mk {
      opId: u64 ;
      key: string ;
      expectedVal: string ;
      val: string ;
  }.

Definition encodes (x:list u8) (a:t) : Prop :=
  x = u64_le a.(opId) ++ (u64_le $ length $ string_le a.(key)) ++ string_le a.(key) ++
      (u64_le $ length $ string_le a.(expectedVal)) ++ string_le a.(val) ++ string_le a.(val)
.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (a:loc) (args:t) : iProp Σ :=
  "HopId" ∷ a ↦[conditionalPutArgs :: "opId"] #args.(opId) ∗
  "Hkey" ∷ a ↦[conditionalPutArgs :: "key"] #(str args.(key)) ∗
  "HexpectedVal" ∷ a ↦[conditionalPutArgs :: "expectedVal"] #(str args.(expectedVal)) ∗
  "Hval" ∷ a ↦[conditionalPutArgs :: "val"] #(str args.(val))
.

Lemma wp_encode args_ptr args :
  {{{
        own args_ptr args
  }}}
    encodeConditionalPutArgs #args_ptr
  {{{
        (sl:Slice.t) enc_args, RET (slice_val sl); own args_ptr args ∗
          ⌜encodes enc_args args⌝ ∗
          own_slice sl byteT 1 enc_args
  }}}
.
Proof.
Admitted.

Lemma wp_decode  sl enc_args args q :
  {{{
        ⌜encodes enc_args args⌝ ∗
        own_slice_small sl byteT q enc_args
  }}}
    decodeConditionalPutArgs (slice_val sl)
  {{{
        (args_ptr:loc), RET #args_ptr; own args_ptr args ∗
                                       own_slice_small sl byteT q enc_args
  }}}
.
Proof.
Admitted.

End local_defs.
End conditionalPutArgs.

Module getArgs.
Record t :=
  mk {
      opId: u64 ;
      key: string ;
  }.

Definition encodes (x:list u8) (a:t) : Prop :=
  x = u64_le a.(opId) ++ string_le a.(key)
.

Section local_defs.
Context `{!heapGS Σ}.
Definition own `{!heapGS Σ} (a:loc) (args:t) : iProp Σ :=
  "HopId" ∷ a ↦[getArgs :: "opId"] #args.(opId) ∗
  "Hkey" ∷ a ↦[getArgs :: "key"] #(str args.(key))
.

Lemma wp_encode args_ptr args :
  {{{
        own args_ptr args
  }}}
    encodeGetArgs #args_ptr
  {{{
        (sl:Slice.t) enc_args, RET (slice_val sl); own args_ptr args ∗
          ⌜encodes enc_args args⌝ ∗
          own_slice sl byteT 1 enc_args
  }}}
.
Proof.
Admitted.

Lemma wp_decode  sl enc_args args q :
  {{{
        ⌜encodes enc_args args⌝ ∗
        own_slice_small sl byteT q enc_args
  }}}
    decodeGetArgs (slice_val sl)
  {{{
        (args_ptr:loc), RET #args_ptr; own args_ptr args ∗
                                       own_slice_small sl byteT q enc_args
  }}}
.
Proof.
  Set Printing All.
Admitted.

End local_defs.

End getArgs.

(********************************************************************************)

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

Section monotonicity.
(* Q: parameter vs member? *)
Class MonotonicPred {PROP:bi} (P:PROP → PROP) :=
  {
    monotonic_fact: (∀ Φ Ψ, □(Φ -∗ Ψ) -∗ P Φ -∗ P Ψ);
  }.

Context `{!gooseGlobalGS Σ}.
Context {A B C : iProp Σ}.

Local Example spec1 Φ : iProp Σ := A ∗ Φ.
Local Example spec2 Φ : iProp Σ := (C -∗ Φ).
Local Example spec3 Φ : iProp Σ := A ∗ B ∗ (C -∗ Φ).
Local Example spec4 Φ : iProp Σ := |={⊤,∅}=> A ∗ Φ.
Local Example spec5 Φ : iProp Σ := (B -∗ (λ Ψ, |={∅,⊤}=> Ψ)%I Φ).
Local Example spec5' Φ : iProp Σ := (B -∗ |={∅,⊤}=> Φ).
Local Example spec6 Φ : iProp Σ := |={⊤,∅}=> A ∗ (B ={∅,⊤}=∗ Φ).

Instance monotonic_id {PROP:bi} : MonotonicPred (PROP:=PROP) (λ Φ, Φ)%I.
Proof. constructor. iIntros (??) "#$". Qed.

Instance monotonic_sep {PROP:bi} (P:PROP) Q :
  MonotonicPred Q → MonotonicPred (λ Φ, P ∗ Q Φ)%I.
Proof.
  constructor.
  iIntros (??) "#?[$ ?]".
  by iDestruct (monotonic_fact with "[] [-]") as "$".
Qed.

Instance monotonic_wand {PROP:bi} (P:PROP) Q :
  MonotonicPred Q → MonotonicPred (λ Φ, P -∗ Q Φ)%I.
Proof.
  constructor.
  iIntros (??) "#Hwand HΦ HP".
  iSpecialize ("HΦ" with "HP").
  by iDestruct (monotonic_fact with "[] [-]") as "$".
Qed.

Instance monotonic_fupd Eo Ei (Q:iProp Σ → iProp Σ) :
  MonotonicPred Q → MonotonicPred (λ Φ, |={Eo,Ei}=> Q Φ)%I.
Proof.
  constructor. iIntros (??) "#? >HQ". by iApply monotonic_fact.
Qed.

Local Instance monotonc_example_1 : MonotonicPred spec1 := _.
Local Instance monotonc_example_2 : MonotonicPred spec2 := _.
Local Instance monotonc_example_3 : MonotonicPred spec3 := _.
Local Instance monotonc_example_4 : MonotonicPred spec4 := _.
(* FIXME: the old instances are being used to prove the new ones.... *)
Local Instance monotonc_example_5' : MonotonicPred spec5' := _.
Local Instance monotonc_example_5 : MonotonicPred spec5 := _.

End monotonicity.

Section rpc_definitions.
(* NOTE: "global" context because RPC specs are known by multiple machines. *)
Context `{!gooseGlobalGS Σ}.

Definition getFreshNum_core_spec (Φ:u64 → iPropO Σ): iPropO Σ.
Admitted.

Definition put_core_spec (args:putArgs.t) (Φ:iPropO Σ): iPropO Σ.
Admitted.

Global Instance put_core_MonotonicPred args : MonotonicPred (put_core_spec args).
Admitted.

Definition conditionalPut_core_spec (args:conditionalPutArgs.t) (Φ:string → iPropO Σ): iPropO Σ.
Admitted.

Definition get_core_spec (args:getArgs.t) (Φ:string → iPropO Σ): iPropO Σ.
Admitted.

End rpc_definitions.

Section rpc_server_proofs.
Context `{!heapGS Σ}.

(* FIXME: make use of explicit spec montonicity and get rid of Ψ+Φ. *)
Lemma wp_Server__getFreshNum (s:loc) Ψ Φ :
  getFreshNum_core_spec Ψ -∗
  (∀ n, Ψ n -∗ Φ #n) -∗
  WP Server__getFreshNum #s {{ v, Φ v }}
.
Proof.
Admitted.

Lemma wp_Server__put (s:loc) args_ptr (args:putArgs.t) Ψ Φ :
  put_core_spec args Ψ -∗
  putArgs.own args_ptr args -∗
  (Ψ -∗ Φ #()) -∗
  WP Server__put #s #args_ptr {{ v, Φ v }}
.
Proof.
Admitted.

Lemma wp_Server__conditionalPut (s:loc) args_ptr (args:conditionalPutArgs.t) Ψ Φ :
  conditionalPut_core_spec args Ψ -∗
  conditionalPutArgs.own args_ptr args -∗
  (∀ r, Ψ r -∗ Φ #(str r)) -∗
  WP Server__conditionalPut #s #args_ptr {{ v, Φ v }}
.
Proof.
Admitted.

Lemma wp_Server__get (s:loc) args_ptr (args:getArgs.t) Ψ Φ :
  get_core_spec args Ψ -∗
  getArgs.own args_ptr args -∗
  (∀ r, Ψ r -∗ Φ #(str r)) -∗
  WP Server__get #s #args_ptr {{ v, Φ v }}
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
  getFreshNum_core_spec (λ (num:u64), ∀ enc_reply, ⌜enc_reply = u64_le num⌝ -∗ Φ enc_reply)
  )%I
.
Next Obligation.
  (* solve_proper.
Defined. *)
Admitted.

Program Definition put_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args,
   "%Henc" ∷ ⌜putArgs.encodes enc_args args⌝ ∗
   put_core_spec args (∀ enc_reply, Φ enc_reply)
  )%I
.
Next Obligation.
  (* solve_proper.
Defined. *)
Admitted.

Program Definition conditionalPut_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args,
   "%Henc" ∷ ⌜conditionalPutArgs.encodes enc_args args⌝ ∗
   conditionalPut_core_spec args (λ rep, Φ (string_le rep))
  )%I
.
Next Obligation.
  (* solve_proper.
Defined. *)
Admitted.

Program Definition get_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args,
   "%Henc" ∷ ⌜getArgs.encodes enc_args args⌝ ∗
   get_core_spec args (λ rep, Φ (string_le rep))
  )%I
.
Next Obligation.
  (* solve_proper.
Defined. *)
Admitted.

Definition is_lockserver_host host : iProp Σ :=
  ∃ γrpc,
  "#H0" ∷ handler_spec γrpc host (U64 0) getFreshNum_spec ∗
  "#H1" ∷ handler_spec γrpc host (U64 1) put_spec ∗
  "#H2" ∷ handler_spec γrpc host (U64 2) conditionalPut_spec ∗
  "#H3" ∷ handler_spec γrpc host (U64 3) get_spec ∗
  "#Hdom" ∷ handlers_dom γrpc {[ U64 0; U64 1; U64 2; U64 3 ]}
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
      iDestruct "Hspec" as (?) "[%Henc Hspec]".
      wp_apply (getArgs.wp_decode with "[$Hreq_sl]").
      { by iPureIntro. }
      iIntros (?) "[Hargs Hreq_sl]".
      wp_apply (wp_Server__get with "[$] [$]").
      iIntros (?) "HΨ".
      wp_pures. wp_apply wp_stringToBytes.
      iIntros (ret_sl) "Hret_sl".
      iDestruct (own_slice_to_small with "Hret_sl") as "Hret_sl".
      wp_store.
      iApply ("HΦ" with "[$] [$] [$]").
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold impl_handler_spec2.
      iIntros (?????) "!# Hreq_sl Hrep HΦ Hspec".
      wp_pures.
      iDestruct "Hspec" as (?) "[%Henc Hspec]".
      wp_apply (conditionalPutArgs.wp_decode with "[$Hreq_sl]").
      { done. }
      iIntros (?) "[Hargs Hreq_sl]".
      wp_apply (wp_Server__conditionalPut with "[$] [$]").
      iIntros (?) "HΨ".
      wp_apply wp_stringToBytes.
      iIntros (?) "Henc_req".
      wp_store.
      iApply ("HΦ" with "[HΨ] [$]").
      { iApply "HΨ". }
      by iDestruct (own_slice_to_small with "Henc_req") as "$".
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold impl_handler_spec2.
      iIntros (?????) "!# Hreq_sl Hrep HΦ Hspec".
      wp_pures.
      iDestruct "Hspec" as (?) "[%Henc Hspec]".
      wp_apply (putArgs.wp_decode with "[$Hreq_sl]").
      { done. }
      iIntros (?) "[Hargs Hreq_sl]".
      wp_apply (wp_Server__put with "[$] [$]").
      iIntros "HΨ". wp_pures.
      iApply ("HΦ" with "[HΨ] [$]").
      { iApply "HΨ". }
      by iApply (own_slice_small_nil _ 1).
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

Lemma wp_Client__getFreshNumRpc cl Φ :
  is_Client cl -∗
  □ getFreshNum_core_spec (λ num, Φ (#num, #0)%V) -∗
  (∀ (err:u64), ⌜err ≠ U64 0⌝ -∗ Φ (#0, #err)%V ) -∗
  WP Client__getFreshNumRpc #cl {{ Φ }}
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

  wp_bind (urpc.Client__Call _ _ _ _ _).
  wp_apply (wp_frame_wand with "[-Hreq_sl Hrep]").
  { iNamedAccu. }

  wp_apply (wp_Client__Call2 with "[$] [] [$] [$] [Hspec]"); first iFrame "#".
  { (* case: got a reply *)
    iModIntro. iModIntro.
    rewrite replicate_0.
    rewrite /getFreshNum_spec /=.
    (* FIXME: want to know that
       Φ -∗ Ψ, core_spec Φ ⊢ core_spec Ψ,
       i.e. that core_spec is covariant.
     *)
    admit.
  }
  { (* case: Call returns error *)
    iIntros (??) "Hreq_sl Hrep". iNamed 1.
    wp_pures.
    wp_if_destruct.
    { by exfalso. }
    wp_pures.
    iApply "Herr".
    done.
  }
Admitted.

Lemma wp_Client__putRpc cl Φ args args_ptr :
  is_Client cl -∗
  putArgs.own args_ptr args -∗
  □ put_core_spec args (Φ #0) -∗
  (∀ (err:u64), ⌜err ≠ U64 0⌝ -∗ Φ #err) -∗
  WP Client__putRpc #cl #args_ptr {{ Φ }}
.
Proof.
  iIntros "Hcl Hargs #Hspec Herr".
  (* symbolic execution *)
  wp_lam.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.
  wp_apply (putArgs.wp_encode with "[$]").
  iIntros (??) "(Hargs & %Henc & Hreq_sl)".
  wp_pures.
  iNamed "Hcl".
  wp_loadField.
  iNamed "Hhost".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".
  wp_apply (wp_Client__Call2 with "[$] [] [$] [$] [Hspec]"); first iFrame "#".
  {
    iModIntro. iModIntro.
    rewrite /put_spec /=.
    iExists _; iFrame "%".
    iApply (monotonic_fact with "[] Hspec").
    iIntros "HΦ".
    iIntros (?) "Hreq_sl". iIntros (?) "Hrep Hrep_sl".
    by wp_pures.
  }
  {
    iIntros (??) "Hreq_sl Hrep".
    wp_pures.
    wp_if_destruct.
    { by exfalso. }
    wp_pures.
    iApply "Herr".
    done.
  }
Qed.

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
