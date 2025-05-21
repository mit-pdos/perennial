From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.tutorial Require Import kvservice.
From Perennial.program_proof.grove_shared Require Import urpc_proof monotonic_pred.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang.automation Require Import extra_tactics proof_automation marshal_specs.
From Perennial.goose_lang Require Import proofmode.

Set Default Proof Using "Type".

Unset Printing Projections.


Section rpc_definitions.
(* NOTE: "global" context because RPC specs are known by multiple machines. *)
Context `{!gooseGlobalGS Σ}.

Definition getFreshNum_core_spec (Φ:u64 → iPropO Σ): iPropO Σ :=
  (* TUTORIAL: write a more useful spec *)
  (∀ opId, Φ opId)%I.

Global Instance getFreshNum_core_MonotonicPred : MonotonicPred (getFreshNum_core_spec).
Proof. apply _. Qed.

Definition put_core_spec (args:put.C) (Φ:unit → iPropO Σ): iPropO Σ :=
  (* TUTORIAL: write a more useful spec *)
  Φ ().

Global Instance put_core_MonotonicPred args : MonotonicPred (put_core_spec args).
Proof. apply _. Qed.

Definition conditionalPut_core_spec (args:conditionalPut.C) (Φ:byte_string → iPropO Σ): iPropO Σ :=
  (* TUTORIAL: write a more useful spec *)
  (∀ status, Φ status)%I.

Global Instance conditionalPut_core_MonotonicPred args : MonotonicPred (conditionalPut_core_spec args).
Proof. apply _. Qed.

Definition get_core_spec (args:get.C) (Φ:byte_string → iPropO Σ): iPropO Σ :=
  (* TUTORIAL: write a more useful spec *)
  (∀ ret, Φ ret)%I.

Definition get_core_MonotonicPred args : MonotonicPred (get_core_spec args).
Proof. apply _. Qed.

End rpc_definitions.

Section rpc_server_proofs.
Context `{!heapGS Σ}.

Definition own_Server (s:loc) : iProp Σ :=
  ∃ (nextFreshId:u64) (lastReplies:gmap u64 byte_string) (kvs:gmap byte_string byte_string)
    (lastReplies_loc kvs_loc:loc),
  "HnextFreshId" ∷ s ↦[Server :: "nextFreshId"] #nextFreshId ∗
  "HlastReplies" ∷ s ↦[Server :: "lastReplies"] #lastReplies_loc ∗
  "Hkvs" ∷ s ↦[Server :: "kvs"] #kvs_loc ∗
  "HlastRepliesM" ∷ own_map lastReplies_loc (DfracOwn 1) lastReplies ∗
  "HkvsM" ∷ own_map kvs_loc (DfracOwn 1) kvs
.

Definition is_Server (s:loc) : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ s ↦[Server :: "mu"]□ mu ∗
  "#HmuInv" ∷ is_lock nroot mu (own_Server s)
.

#[global] Instance is_server_pers s : Persistent (is_Server s).
Proof. apply _. Qed.

(* FIXME: make use of explicit spec montonicity and get rid of Ψ+Φ. *)
#[global] Instance wp_Server__getFreshNum (s:loc) Ψ :
  SPEC
  {{
        is_Server s ∗
        getFreshNum_core_spec Ψ
  }}
    Server__getFreshNum #s
  {{ (n:u64), RET #n; Ψ n }}
.
Proof.
  iSteps.
Qed.

#[global] Instance wp_Server__put (s:loc) args__v Ψ :
  SPEC (args: put.C),
  {{{
        "#Hsrv" ∷ is_Server s ∗
        "Hspec" ∷ put_core_spec args Ψ ∗
        "Hargs" ∷ put.own args__v args (DfracOwn 1)
  }}}
  Server__put #s args__v
  {{{
        RET #(); Ψ ()
  }}
.
Proof.
  iSteps.
  wp_if_destruct; [ by iSteps | ].
  iSteps.
Qed.

#[global] Instance wp_Server__conditionalPut (s:loc) args__v Ψ :
  SPEC (args: conditionalPut.C), {{{
        "#Hsrv" ∷ is_Server s ∗
        "Hspec" ∷ conditionalPut_core_spec args Ψ ∗
        "Hargs" ∷ conditionalPut.own args__v args (DfracOwn 1)
  }}}
    Server__conditionalPut #s args__v
  {{{ r, RET #(str r); Ψ r }}}
.
Proof.
  iSteps.
  wp_if_destruct; iSteps.
  wp_if_destruct; iSteps.
Qed.
#[global] Opaque Server__conditionalPut.

#[global] Instance wp_Server__get (s:loc) args__v :
  SPEC args Ψ, {{{
        "#Hsrv" ∷ is_Server s ∗
        "Hspec" ∷ get_core_spec args Ψ ∗
        "Hargs" ∷ get.own args__v args (DfracOwn 1)
  }}}
    Server__get #s args__v
  {{{
        r, RET #(str r); Ψ r
  }}
.
Proof.
  iSteps.
  wp_if_destruct; iSteps.
Qed.
#[global] Opaque Server__get.

#[global] Instance wp_MakeServer :
  SPEC {{ emp }}
    MakeServer #()
  {{ (s:loc), RET #s; is_Server s }}
.
Proof.
  iSteps.
Qed.

End rpc_server_proofs.

Section encoded_rpc_definitions.
(* This section is boilerplate. *)
Context `{!gooseGlobalGS Σ}.
Context `{!urpcregG Σ}.

Program Definition getFreshNum_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (
  getFreshNum_core_spec (λ (num:u64), Φ (u64_le num))
  )%I
.
Next Obligation.
  solve_proper.
Defined.

Program Definition put_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args,
   "%Henc" ∷ ⌜put.has_encoding enc_args args⌝ ∗
   put_core_spec args (λ _, ∀ enc_reply, Φ enc_reply)
  )%I
.
Next Obligation.
  rewrite /put_core_spec. solve_proper.
Defined.

Program Definition conditionalPut_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args,
   "%Henc" ∷ ⌜conditionalPut.has_encoding enc_args args⌝ ∗
   conditionalPut_core_spec args (λ rep, Φ rep)
  )%I
.
Next Obligation.
  rewrite /conditionalPut_core_spec. solve_proper.
Defined.

Program Definition get_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args,
   "%Henc" ∷ ⌜get.has_encoding enc_args args⌝ ∗
   get_core_spec args (λ rep, Φ rep)
  )%I
.
Next Obligation.
  solve_proper.
Defined.

Definition is_kvserver_host host : iProp Σ :=
  ∃ γrpc,
  "#H0" ∷ is_urpc_spec_pred γrpc host (W64 0) getFreshNum_spec ∗
  "#H1" ∷ is_urpc_spec_pred γrpc host (W64 1) put_spec ∗
  "#H2" ∷ is_urpc_spec_pred γrpc host (W64 2) conditionalPut_spec ∗
  "#H3" ∷ is_urpc_spec_pred γrpc host (W64 3) get_spec ∗
  "#Hdom" ∷ is_urpc_dom γrpc {[ W64 0; W64 1; W64 2; W64 3 ]}
  .

End encoded_rpc_definitions.

Section start_server_proof.
(* This section is boilerplate. *)
Context `{!heapGS Σ}.
Context `{!urpcregG Σ}.

Typeclasses Opaque MakeServer.
#[local] Opaque MakeServer.
Typeclasses Opaque urpc.MakeServer.
#[local] Opaque urpc.MakeServer.
#[local] Opaque Server__conditionalPut.
#[local] Opaque is_Server.

Typeclasses Opaque decodePutArgs.
#[local] Opaque decodePutArgs.

Typeclasses Opaque Server__getFreshNum.
#[local] Opaque Server__getFreshNum.

Lemma wp_Server__Start (s:loc) (host:u64) :
  {{{
        "#Hsrv" ∷ is_Server s ∗
        "#Hhost" ∷ is_kvserver_host host
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
  wp_rec.
  wp_pures.
  wp_apply (map.wp_NewMap) as (handlers) "Hhandlers".
  wp_apply (map.wp_MapInsert u64 with "Hhandlers") as "Hhandlers".
  wp_apply (map.wp_MapInsert with "Hhandlers") as "Hhandlers".
  wp_apply (map.wp_MapInsert with "Hhandlers") as "Hhandlers".

  wp_apply (map.wp_MapInsert with "Hhandlers") as "Hhandlers".
  wp_apply (urpc_proof.wp_MakeServer with "Hhandlers").
  iIntros (r) "Hr".

  iNamed "Hhost".
  wp_bind (urpc.Server__Serve _ _).
  iApply (wp_StartServer_pred with "[$Hr]"); [..|iNext].
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
      unfold is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iDestruct "Hspec" as (?) "[%Henc Hspec]".
      wp_apply (get.wp_Decode _ _ _ [] with "[Hreq_sl]").
      { rewrite app_nil_r. iFrame. by iPureIntro. }
      iIntros (??) "[Hargs Hreq_sl]".
      wp_apply (wp_Server__get with "[$]").
      iIntros (?) "HΨ".
      wp_pures. wp_apply wp_StringToBytes.
      iIntros (ret_sl) "Hret_sl".
      iDestruct (own_slice_to_small with "Hret_sl") as "Hret_sl".
      wp_store.
      iModIntro. iApply "HΦ"; iFrame.
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iDestruct "Hspec" as (?) "[%Henc Hspec]".
      wp_apply (conditionalPut.wp_Decode _ _ _ [] with "[Hreq_sl]").
      { rewrite app_nil_r. iFrame. done. }
      iIntros (??) "[Hargs Hreq_sl]".
      wp_apply (wp_Server__conditionalPut with "[$]").
      iIntros (?) "HΨ".
      wp_apply wp_StringToBytes.
      iIntros (?) "Henc_req".
      wp_store.
      iApply "HΦ"; iFrame.
      by iDestruct (own_slice_to_small with "Henc_req") as "$".
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iDestruct "Hspec" as (?) "[%Henc Hspec]".
      wp_apply (put.wp_Decode _ _ _ [] with "[Hreq_sl]").
      { rewrite app_nil_r. iFrame. done. }
      iIntros (??) "Hargs". iDestruct "Hargs" as "[Hargs _]".
      wp_apply (wp_Server__put with "[$Hsrv $Hargs Hspec //]").
      iIntros "HΨ". wp_pures.
      iApply "HΦ"; iFrame.
      by iDestruct (own_slice_small_nil _ (DfracOwn 1)) as "$".
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iEval (rewrite /getFreshNum_spec /=) in "Hspec".
      iSteps.
      unseal_diaframe => /=; iFrame; iSteps.
    }
    by iApply big_sepM_empty.
  }
  wp_pures.
  iSteps.
Qed.

End start_server_proof.

Section client_proof.
(* This section is boilerplate. *)
Context `{!heapGS Σ, !urpcregG Σ}.
Definition is_Client (cl:loc) : iProp Σ :=
  ∃ (urpcCl:loc) host,
  "#Hcl" ∷ cl ↦[Client :: "cl"]□ #urpcCl ∗
  "#HurpcCl" ∷ is_uRPCClient urpcCl host ∗
  "#Hhost" ∷ is_kvserver_host host
.

#[global] Instance is_Client_pers cl :
  Persistent (is_Client cl).
Proof. apply _. Qed.

#[local] Opaque urpc.MakeClient.
#[local] Opaque is_uRPCClient.

Lemma wp_makeClient (host:u64) :
  {{{
        "#Hhost" ∷ is_kvserver_host host
  }}}
    makeClient #host
  {{{
        (cl:loc), RET #cl; is_Client cl
  }}}.
Proof.
  iSteps.
  wp_apply wp_MakeClient.
  iSteps.
Qed.

#[local] Opaque urpc.Client__Call.

Lemma wp_Client__getFreshNumRpc Post cl :
  {{{
        "#Hcl" ∷ is_Client cl ∗
        "#Hspec" ∷ □ getFreshNum_core_spec Post
  }}}
    Client__getFreshNumRpc #cl
  {{{
        (err id:u64), RET (#id, #err); if decide (err = 0) then Post id else True
  }}}
.
Proof.
  iSteps.
  iRename select (_ ↦[slice.T _] _)%I into "Hrep".
  iRename select (own_slice _ _ _ _)%I into "Hreq_sl".
  wp_bind (urpc.Client__Call _ _ _ _ _).
  wp_apply (wp_frame_wand with "[-Hreq_sl Hrep]").
  { iNamedAccu. }
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".

  iRename select (getFreshNum_core_spec _) into "Hspec".

  wp_apply (wp_Client__Call2 with "[$] [] [$] [$] []"); first iFrame "#".
  iSplit.
  { (* case: got a reply *)
    iModIntro. iModIntro.
    rewrite /getFreshNum_spec /=.
    iApply (monotonic_fact with "[] Hspec").
    iModIntro.
    iSteps.
  }
  { (* case: Call returns error *)
    iSteps.
    wp_if_destruct; [ done | ].
    iSteps.
    iModIntro. iModIntro.
    rewrite decide_False //.
  }
Qed.
#[global] Opaque Client__getFreshNumRpc.

#[global] Opaque urpc.Client__Call.
#[global] Opaque encodePutArgs.

Lemma wp_Client__putRpc Post cl args args__v:
  {{{
        "Hargs" ∷ put.own args__v args (DfracOwn 1) ∗
        "#Hcl" ∷ is_Client cl ∗
        "#Hspec" ∷ □ put_core_spec args Post
  }}}
    Client__putRpc #cl args__v
  {{{
        (err:u64), RET #err; if decide (err = 0) then Post () else True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  (* symbolic execution *)
  wp_rec.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.
  wp_apply (putArgs.wp_encode) => /=. iExists _; iFrame.
  iIntros (sl bs) "!> (Hargs & Hreq_sl & %Henc)".
  wp_pures.
  iNamed "Hcl".
  wp_loadField.
  iNamed "Hhost".
  wp_bind (urpc.Client__Call _ _ _ _ _).
  wp_apply (wp_frame_wand with "[-Hreq_sl Hrep]").
  { iNamedAccu. }
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".
  wp_apply (wp_Client__Call2 with "[$] [] [$] [$] [Hspec]"); first by iFrame "#".
  iSplit.
  {
    iModIntro. iModIntro.
    rewrite /put_spec /=.
    iExists _; iFrame "%".
    iApply (monotonic_fact with "[] Hspec").
    iModIntro.
    iSteps.
  }
  {
    iSteps.
    wp_if_destruct.
    { by exfalso. }
    iModIntro. iSteps.
    by rewrite decide_False.
  }
Qed.

Typeclasses Opaque
  encodeConditionalPutArgs encodeGetArgs
.

Lemma wp_Client__conditionalPutRpc Post cl args argsᵥ :
  {{{
        "Hargs" ∷ conditionalPut.own args__v args (DfracOwn 1) ∗
        "#Hcl" ∷ is_Client cl ∗
        "#Hspec" ∷ □ conditionalPut_core_spec args Post
  }}}
    Client__conditionalPutRpc #cl args__v
  {{{
        (s:byte_string) (err:u64), RET (#str s, #err); if decide (err = 0) then Post s else True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  (* symbolic execution *)
  wp_rec.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.

  wp_apply (conditionalPutArgs.wp_encode).
  iExists _; iFrame.
  iIntros "!>" (??) "(Hargs & %Henc & Hreq_sl)".
  iNamed "Hcl".
  wp_loadField.
  iNamed "Hhost".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".

  wp_bind (urpc.Client__Call _ _ _ _ _).
  wp_apply (wp_frame_wand with "[-Hreq_sl Hrep]").
  { iNamedAccu. }

  wp_apply (wp_Client__Call2 with "[$] [] [$] [$] [Hspec]"); first by iFrame "#".
  iSplit.
  {
    iModIntro. iModIntro.
    rewrite /conditionalPut_spec /=.
    iExists _; iFrame "%".
    iApply (monotonic_fact with "[] Hspec").
    iModIntro.
    iSteps.
  }
  {
    iSteps.
    wp_if_destruct; [ by exfalso | ].
    iSteps.
    iModIntro. iModIntro. by rewrite decide_False.
  }
Qed.

Lemma wp_Client__getRpc Post cl args args__v :
  {{{
        "Hargs" ∷ get.own args__v args (DfracOwn 1) ∗
        "#Hcl" ∷ is_Client cl ∗
        "#Hspec" ∷ □ get_core_spec args Post
  }}}
    Client__getRpc #cl args__v
  {{{
        (s:byte_string) (err:u64), RET (#str s, #err); if decide (err = 0) then Post s else True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  (* symbolic execution *)
  wp_rec.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.
  wp_apply wp_NewSlice. iIntros (s) "Hs".
  wp_apply (get.wp_Encode with "[$]").
  iIntros (??) "(%Henc & Hargs_own & Hreq_sl)".
  wp_pures.
  iNamed "Hcl".
  wp_loadField.
  iNamed "Hhost".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".

  wp_bind (urpc.Client__Call _ _ _ _ _).
  wp_apply (wp_frame_wand with "[-Hreq_sl Hrep]").
  { iNamedAccu. }

  wp_apply (wp_Client__Call2 with "[$] [] [$] [$] [Hspec]"); first iFrame "#".
  iSplit.
  {
    iModIntro. iModIntro.
    rewrite /conditionalPut_spec /=.
    iExists _; iFrame "%".
    iApply (monotonic_fact with "[] Hspec").
    iModIntro.
    iSteps.
  }
  {
    iSteps.
    wp_if_destruct; [ by exfalso | ].
    iSteps.
    iModIntro. iModIntro.
    by rewrite decide_False.
  }
Qed.


End client_proof.

Section clerk_proof.
Context `{!heapGS Σ}.
Context `{!urpcregG Σ}.

Definition is_Clerk (ck:loc) : iProp Σ :=
  ∃ (cl:loc),
  "#Hcl" ∷ ck ↦[Clerk :: "rpcCl"]□ #cl ∗
  "#HisCl" ∷ is_Client cl
.

Typeclasses Opaque Client__putRpc.

Lemma wp_Clerk__Put (ck:loc) k v :
  {{{ is_Clerk ck }}}
    Clerk__Put #ck #(str k) #(str v)
  {{{ RET #(); True }}}
.
Proof.
  iIntros (Φ) "#Hck HΦ".
  wp_rec.
  (* symbolic execution *)
  wp_pures.
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (err_ptr) "Herr".
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (id_ptr) "Hid".
  wp_pures.

  iAssert (∃ (someErr someOpId:u64), "Hid" ∷ id_ptr ↦[uint64T] #someOpId ∗
                             "Herr" ∷ err_ptr ↦[uint64T] #someErr
          )%I with "[Herr Hid]" as "HH".
  { repeat iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.
  iNamed "Hck".
  wp_loadField.
  wp_apply (wp_Client__getFreshNumRpc (λ opId, True)%I with "[$HisCl]").
  { done. } (* TUTORIAL *)
  iIntros (err opId) "Hpost".
  wp_pures.
  wp_store.
  wp_store.
  wp_load.
  wp_if_destruct.
  2:{ (* case: didn't get a valid ID. *)
    iModIntro. iLeft.
    iSplitR; first done.
    iFrame.
  }
  (* case: successful RPC *)
  iModIntro. iRight.
  iSplitR; first done.
  wp_pures.

  wp_forBreak_cond.

  wp_load.
  wp_pures.
  wp_apply (wp_allocStruct).
  { val_ty. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_loadField.

  (* TUTORIAL: *)
  wp_apply (wp_Client__putRpc (λ _, True)%I with "[Hcl]").
  { instantiate (2:=put.mkC _ _ _). iFrame "∗#". done. }
  iClear "Hpost".
  iIntros (err) "Hpost".
  wp_pures.
  wp_if_destruct.
  2:{ (* case: RPC error *)
    wp_pures.
    iLeft.
    iModIntro. iSplitR; first done.
    iFrame.
  }
  iRight.
  iModIntro.
  iSplitR; first done.
  wp_pures.
  iModIntro. iApply "HΦ". done.
Qed.

Typeclasses Opaque Client__conditionalPutRpc.

Lemma wp_Clerk__ConditionalPut (ck:loc) k expectV newV :
  {{{ is_Clerk ck }}}
    Clerk__ConditionalPut #ck #(str k) #(str expectV) #(str newV)
  {{{ (ok:bool), RET #ok; True }}}
.
Proof.
  iIntros (Φ) "#Hck HΦ".
  wp_rec.
  (* symbolic execution *)
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (err_ptr) "Herr".
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (id_ptr) "Hid".
  wp_pures.

  iAssert (∃ (someErr someOpId:u64), "Hid" ∷ id_ptr ↦[uint64T] #someOpId ∗
                             "Herr" ∷ err_ptr ↦[uint64T] #someErr
          )%I with "[Herr Hid]" as "HH".
  { repeat iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.
  iNamed "Hck".
  wp_loadField.
  wp_apply (wp_Client__getFreshNumRpc (λ opId, True)%I with "[$HisCl]").
  { done. } (* TUTORIAL *)
  iIntros (err opId) "Hpost".
  wp_pures.
  wp_store.
  wp_store.
  wp_load.
  wp_if_destruct.
  2:{ (* case: didn't get a valid ID. *)
    iModIntro. iLeft.
    iSplitR; first done.
    iFrame.
  }
  (* case: successful RPC *)
  iModIntro. iRight.
  iSplitR; first done.
  wp_pures.

  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (ret_ptr) "Hret".
  wp_pures.
  wp_forBreak_cond.

  wp_load.
  wp_pures.
  wp_apply (wp_allocStruct).
  { val_ty. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_loadField.

  (* TUTORIAL: *)
  wp_apply (wp_Client__conditionalPutRpc (λ _, True)%I with "[Hcl]").
  { instantiate (2:=conditionalPut.mkC _ _ _ _). iFrame "∗#". done. }
  iClear "Hpost".
  iIntros (ret err) "Hpost".
  wp_pures.
  wp_if_destruct.
  2:{ (* case: RPC error, so retry *)
    wp_pures.
    iLeft.
    iModIntro. iSplitR; first done.
    iFrame.
  }
  wp_store.
  iRight.
  iModIntro.
  iSplitR; first done.
  wp_pures.
  wp_load.
  iModIntro. iApply "HΦ". done.
Qed.

Typeclasses Opaque Client__getRpc.

Lemma wp_Clerk__Get (ck:loc) k :
  {{{ is_Clerk ck }}}
    Clerk__Get #ck #(str k)
  {{{ v, RET #(str v); True }}}
.
Proof.
  iIntros (Φ) "#Hck HΦ".
  wp_rec.
  (* symbolic execution *)
  wp_pures.
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (err_ptr) "Herr".
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (id_ptr) "Hid".
  wp_pures.

  iAssert (∃ (someErr someOpId:u64), "Hid" ∷ id_ptr ↦[uint64T] #someOpId ∗
                             "Herr" ∷ err_ptr ↦[uint64T] #someErr
          )%I with "[Herr Hid]" as "HH".
  { repeat iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.
  iNamed "Hck".
  wp_loadField.
  wp_apply (wp_Client__getFreshNumRpc (λ opId, True)%I with "[$HisCl]").
  { done. } (* TUTORIAL *)
  iIntros (err opId) "Hpost".
  wp_pures.
  wp_store.
  wp_store.
  wp_load.
  wp_if_destruct.
  2:{ (* case: didn't get a valid ID. *)
    iModIntro. iLeft.
    iSplitR; first done.
    iFrame.
  }
  (* case: successful RPC *)
  iModIntro. iRight.
  iSplitR; first done.
  wp_pures.

  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (ret_ptr) "Hret".
  wp_pures.
  wp_forBreak_cond.

  wp_load.
  wp_pures.
  wp_apply (wp_allocStruct).
  { val_ty. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_loadField.

  (* TUTORIAL: *)
  wp_apply (wp_Client__getRpc (λ _, True)%I with "[Hcl]").
  { instantiate (2:=get.mkC _ _). iFrame "∗#". done. }
  iClear "Hpost".
  iIntros (ret err) "Hpost".
  wp_pures.
  wp_if_destruct.
  2:{ (* case: RPC error, so retry *)
    wp_pures.
    iLeft.
    iModIntro. iSplitR; first done.
    iFrame.
  }
  wp_store.
  iRight.
  iModIntro.
  iSplitR; first done.
  wp_pures.
  wp_load.
  iModIntro. iApply "HΦ". done.
Qed.

#[local] Opaque makeClient.
#[local] Opaque readonly.

Lemma wp_MakeClerk (host:u64) :
  {{{ is_kvserver_host host }}}
    MakeClerk #host
  {{{ ck, RET #ck; is_Clerk ck }}}
.
Proof.
  iSteps.
  wp_apply (wp_makeClient with "[$]").
  iSteps.
Qed.

End clerk_proof.
