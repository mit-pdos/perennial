From Goose.github_com.mit_pdos.gokv.urpc Require Import rpc.
From iris.base_logic.lib Require Import saved_prop.
From Perennial.program_proof Require Import dist_prelude.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.algebra Require Import auth_map.
From Perennial.base_logic Require Export lib.ghost_map lib.mono_nat.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Record rpc_reg_entry := RegEntry {
  rpc_reg_rpcid  : u64;
  rpc_reg_auxtype : Type;
  rpc_reg_aux : rpc_reg_auxtype;
  rpc_reg_args : list u8;
  rpc_reg_saved : gname;
}.

Class rpcregG (Σ : gFunctors) := RpcRegG {
  rpcreg_mono_natG :> mono_natG Σ;
  rpcreg_mapG :> mapG Σ u64 rpc_reg_entry;
  rpcreg_escrowG :> mapG Σ u64 unit;
  rpcreg_savedG :> savedPredG Σ (list u8);
}.

Section rpc_proof.

Existing Instances message_eq_decision message_countable.

Context `{!rpcregG Σ}.
Context `{!heapG Σ}.

(* A host-specific mapping from rpc ids on that host to pre/post conditions *)
Definition rpc_spec_map : Type :=
  gmap u64 { X: Type & ((X → list u8 → iProp Σ) * (X → list u8 → list u8 → iProp Σ))%type }.

Definition urpc_serverN : namespace := nroot.@"urpc_server".
Definition urpc_clientN : namespace := nroot.@"urpc_client".
Definition urpc_lockN : namespace := nroot.@"urpc_lock".

Record client_chan_gnames := {
  ccmapping_name : gname;
  ccescrow_name : gname;
  ccextracted_name : gname;
}.

Definition client_chan_inner (Γ : client_chan_gnames) (host: u64) : iProp Σ :=
  ∃ ms, "Hchan" ∷ host c↦ ms ∗
  "Hmessages" ∷ [∗ set] m ∈ ms,
    ∃ (rpcid seqno : u64) reqData replyData X Post (x : X) γ,
       "%Henc" ∷ ⌜ has_encoding (msg_data m) [EncUInt64 seqno;
                                              EncUInt64 (length replyData); EncBytes replyData] ⌝ ∗
       "#Hseqno" ∷ ptsto_ro (ccmapping_name Γ) seqno (RegEntry rpcid X x reqData γ) ∗
       "HPost_saved" ∷ saved_pred_own γ (Post x reqData) ∗
       "HPost" ∷ (Post x reqData replyData ∨ ptsto_mut (ccescrow_name Γ) seqno 1 tt)
.

Definition server_chan_inner (host: u64) (specs : rpc_spec_map) : iProp Σ :=
  ∃ ms, "Hchan" ∷ host c↦ ms ∗
  "Hmessages" ∷ [∗ set] m ∈ ms,
    ∃ rpcid seqno args X Pre Post (x : X) Γ γ,
       "%Henc" ∷ ⌜ has_encoding (msg_data m) [EncUInt64 rpcid; EncUInt64 seqno;
                                              EncUInt64 (length args); EncBytes args] ⌝ ∗
       "%Hlookup_spec" ∷ ⌜ specs !! rpcid = Some (existT X (Pre, Post)) ⌝ ∗
       "#Hseqno" ∷ ptsto_ro (ccmapping_name Γ) seqno (RegEntry rpcid X x args γ) ∗
       "HPre" ∷ □ (Pre x args) ∗
       "HPost_saved" ∷ saved_pred_own γ (Post x args) ∗
       "Hclient_chan_inv" ∷ inv urpc_clientN (client_chan_inner Γ (msg_sender m))
.

Definition handler_is : ∀ (X:Type) (host:u64) (rpcid:u64) (Pre:X → list u8 → iProp Σ)
                          (Post:X → list u8 → list u8 → iProp Σ), iProp Σ :=
  λ X host rpcid Pre Post, (∃ (specs: rpc_spec_map),
  "%Hprepost" ∷ ⌜ specs !! rpcid = Some (existT X (Pre, Post)) ⌝ ∗
  "#Hserver_inv" ∷ inv urpc_serverN (server_chan_inner host specs)
)%I.

Global Instance handler_is_pers_instance X host rpcid pre post : Persistent (handler_is X host rpcid pre post).
Proof. apply _. Qed.

Definition RPCClient_lock_inner Γ  (cl : loc) (lk : loc) (host : u64) mref : iProp Σ :=
  ∃ pending reqs estoks extoks (n : u64),
            "%Hnpos" ∷ ⌜ 0 < int.Z n ⌝%Z ∗
            "%Hdom_range" ∷ ⌜ ∀ id, (0 < int.Z id < int.Z n)%Z ↔ id ∈ dom (gset u64) reqs ⌝ ∗
            "%Hdom_eq_es" ∷ ⌜ dom (gset u64) reqs = dom (gset u64) estoks ⌝ ∗
            "%Hdom_eq_ex" ∷ ⌜ dom (gset u64) reqs = dom (gset u64) extoks ⌝ ∗
            "%Hdom_pending" ∷ ⌜ dom (gset u64) pending ⊆ dom (gset u64) reqs  ⌝ ∗
            "seq" ∷ cl ↦[RPCClient :: "seq"] #n ∗
            "Hmapping_ctx" ∷ map_ctx (ccmapping_name Γ) 1 reqs ∗
            "Hescrow_ctx" ∷ map_ctx (ccescrow_name Γ) 1 estoks ∗
            "Hextracted_ctx" ∷ map_ctx (ccextracted_name Γ) 1 extoks ∗
            "Hpending_map" ∷ map.is_map mref (pending, zero_val (struct.ptrT callback)) ∗
            "Hreqs" ∷ [∗ map] seqno ↦ req ∈ reqs, ∃ (Post : rpc_reg_auxtype req → list u8 → list u8 → iProp Σ),
                 "Hreg_entry" ∷  ptsto_ro (ccmapping_name Γ) seqno req ∗
                 "HPost_saved" ∷ saved_pred_own (rpc_reg_saved req) (Post (rpc_reg_aux req) (rpc_reg_args req)) ∗
                 (* (1) Reply thread has not yet processed, so it is in pending
                    and we have escrow token *)
                 (∃ rep_ptr (cb_done cb_cond : loc),
                    "Hpending_cb" ∷ ⌜ pending !! seqno  =
                                        Some (struct.mk_f callback [
                                          "reply" ::= #rep_ptr;
                                          "done" ::= #cb_done;
                                          "cond" ::= #cb_cond ])%V ⌝ ∗
                    "Hescrow" ∷ ptsto_mut (ccescrow_name Γ) seqno 1 tt ∗
                    "Hcond" ∷ is_cond cb_cond #lk ∗
                    "Hdone" ∷ cb_done ↦[boolT] #false) ∨
                 (* (2) Reply thread has received message, removed from pending,
                    but caller has not extracted ownership *)
                 (∃ reply (cb : unit), ⌜ pending !! seqno  = None ⌝ ∗ (* TODO: cb ownership *) True ∗
                               (Post (rpc_reg_aux req) (rpc_reg_args req) reply)) ∨
                 (* (3) Caller has extracted ownership *)
                 (⌜ pending !! seqno  = None ⌝ ∗ ptsto_mut (ccextracted_name Γ) seqno 1 tt).

Definition RPCClient_own (cl : loc) (host:u64) : iProp Σ :=
  ∃ Γ (lk : loc) r (mref : loc),
    "#Hstfields" ∷ ("mu" ∷ readonly (cl ↦[RPCClient :: "mu"] #lk) ∗
    "#send" ∷ readonly (cl ↦[RPCClient :: "send"] send_endpoint host r) ∗
    "#pending" ∷ readonly (cl ↦[RPCClient :: "pending"] #mref)) ∗
    "#Hchan" ∷ inv urpc_clientN (client_chan_inner Γ r) ∗
    "#Hlk" ∷ is_lock urpc_lockN #lk (RPCClient_lock_inner Γ cl lk host mref).

Definition RPCClient_reply_own (cl : loc) (r : chan) : iProp Σ :=
  ∃ Γ host (lk : loc) (mref : loc),
    "#Hstfields" ∷ ("mu" ∷ readonly (cl ↦[RPCClient :: "mu"] #lk) ∗
    "#pending" ∷ readonly (cl ↦[RPCClient :: "pending"] #mref)) ∗
    "#Hchan" ∷ inv urpc_clientN (client_chan_inner Γ r) ∗
    "#Hlk" ∷ is_lock urpc_lockN #lk (RPCClient_lock_inner Γ cl lk host mref).

Lemma wp_RPCClient__replyThread cl r :
  RPCClient_reply_own cl r -∗
  WP RPCClient__replyThread #cl (recv_endpoint r) {{ _, True }}.
Proof. Admitted.

Lemma wp_MakeRPCClient (host:u64):
  {{{
       True
  }}}
    MakeRPCClient #host
  {{{
       (cl_ptr:loc), RET #cl_ptr; RPCClient_own cl_ptr host
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.

  wp_apply (wp_Connect).
  iIntros (err r) "Hr".
  destruct err.
  { admit. (* TODO FIXME: RPCClient should check this error, or panic *) }
  wp_pures.

  replace (ref (InjLV #null))%E with (NewMap (struct.ptrT callback)) by naive_solver.
  wp_apply (wp_new_free_lock). iIntros (lk) "Hfree".
  wp_pures.
  (* XXX: I think this is going to have to be untyped since callback contains a slice in it *)
  wp_apply (map.wp_NewMap).
  iIntros (mref) "Hmref".

  wp_apply (wp_allocStruct).
  { enough (val_ty (send_endpoint host r) Sender) by naive_solver.
    econstructor.
  }
  iIntros (cl) "Hcl".
  iNamed "Hcl".
  iDestruct (struct_fields_split with "Hcl") as "Hcl". iNamed "Hcl".
  wp_pures.
  (* TODO: why do I have to unshelve this, when in other cases it appears to get picked up automatically *)
  unshelve (iMod (readonly_alloc_1 with "mu") as "#mu"); [| apply _ |].
  unshelve (iMod (readonly_alloc_1 with "send") as "#send"); [| apply _ |].
  unshelve (iMod (readonly_alloc_1 with "pending") as "#pending"); [| apply _ |].

  iMod (map_init (∅ : gmap u64 rpc_reg_entry)) as (γccmapping) "Hmapping_ctx".
  iMod (map_init (∅ : gmap u64 unit)) as (γccescrow) "Hescrow_ctx".
  iMod (map_init (∅ : gmap u64 unit)) as (γccextracted) "Hextracted_ctx".
  set (Γ := {| ccmapping_name := γccmapping; ccescrow_name := γccescrow;
               ccextracted_name := γccextracted |}).
  iMod (alloc_lock urpc_lockN _ _ (RPCClient_lock_inner Γ cl lk host mref) with
            "Hfree [Hmapping_ctx Hescrow_ctx Hextracted_ctx seq Hmref]") as "#Hlock".
  { iNext. iExists ∅, ∅, ∅, ∅, _. iFrame.
    rewrite ?dom_empty_L.
    iSplit; first done.
    iSplit.
    { iPureIntro. split; last by set_solver. word. }
    iSplit; first done.
    iSplit; first done.
    rewrite big_sepM_empty //.
  }
  iMod (inv_alloc urpc_clientN _ (client_chan_inner Γ r) with "[Hr]") as "#Hchan_inv".
  { iNext. iExists ∅. iFrame. rewrite big_sepS_empty //. }
  wp_bind (Fork _).
  iApply wp_fork.
  { iNext. wp_pures. iApply wp_RPCClient__replyThread. iExists _, _, _, _. iFrame "#". }
  iNext. wp_pures. iModIntro. iApply "HΦ".
  iExists _, _, _, _. iFrame "#".
Admitted.

Lemma wp_RPCClient__Call {X:Type} (x:X) (cl_ptr:loc) (rpcid:u64) (host:u64) req rep_ptr
      dummy_sl_val (reqData:list u8) Pre Post :
  {{{
      is_slice req byteT 1 reqData ∗
      rep_ptr ↦[slice.T byteT] dummy_sl_val ∗
      handler_is X host rpcid Pre Post ∗
      RPCClient_own cl_ptr host ∗
      □(▷ Pre x reqData)
  }}}
    RPCClient__Call #cl_ptr #rpcid (slice_val req) #rep_ptr
  {{{
       (b:bool) rep_sl (repData:list u8), RET #b;
       rep_ptr ↦[slice.T byteT] (slice_val rep_sl) ∗
       RPCClient_own cl_ptr host ∗
       typed_slice.is_slice req byteT 1 reqData ∗
       typed_slice.is_slice rep_sl byteT 1 repData ∗
       (⌜b = true⌝ ∨ ⌜b = false⌝ ∗ (▷ Post x reqData repData))
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  wp_lam.
  wp_pures.
  iDestruct "H" as "(Hslice&Hrep_ptr&Hhandler&Hclient&#HPre)".
  iNamed "Hclient". iNamed "Hstfields".
  replace (#false) with (zero_val boolT) by auto.
  wp_apply (wp_ref_of_zero); first done.
  iIntros (cb_done) "done".
  wp_loadField.
  wp_bind (lock.newCond _).
  wp_apply (wp_newCond with "[$]").
  iIntros (cb_cond) "cond".
  wp_pures.
  wp_apply (wp_StoreAt with "[$]"); first eauto.
  iIntros "done".
  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "(Hlked&Hlock_inner)".
  iNamed "Hlock_inner".
  wp_pures.
  wp_loadField. wp_pures.
  wp_loadField. wp_storeField.
  wp_loadField.
  wp_apply (map.wp_MapInsert with "[$]").
  iIntros "Hpending_map".
  wp_pures.
  wp_loadField.
  iMod (saved_pred_alloc (Post x reqData)) as (γ) "#Hsaved".
  assert (reqs !! n = None).
  { apply not_elem_of_dom. rewrite -Hdom_range. lia. }
  iMod (map_alloc_ro n (RegEntry rpcid X x reqData γ) with "Hmapping_ctx") as "(Hmapping_ctx&#Hreg)"; auto.
  iMod (map_alloc n tt with "Hescrow_ctx") as "(Hescrow_ctx&Hescrow)".
  { apply not_elem_of_dom. rewrite -Hdom_eq_es -Hdom_range. lia. }
  iMod (map_alloc n tt with "Hextracted_ctx") as "(Hextracted_ctx&Hextracted)".
  { apply not_elem_of_dom. rewrite -Hdom_eq_ex -Hdom_range. lia. }
  wp_apply (release_spec with "[-Hslice Hrep_ptr Hhandler HΦ Hextracted]").
  { iFrame "Hlk". iFrame "Hlked". iNext. iExists _, _, _, _, _.
    iFrame. rewrite ?dom_insert_L.
    assert (int.Z (word.add n 1) = int.Z n + 1)%Z as ->.
    { (* XXX: not true because of overflow, so there's actually a bug here *) admit. }
    iSplit.
    { iPureIntro. word. }
    iSplit.
    { iPureIntro. intros. set_unfold. split.
      * intros Hrange.
        assert (0 < int.Z id < int.Z n ∨ int.Z id = int.Z n)%Z.
        { word. }
        { naive_solver word. }
      * intros [Heq|Hin].
        { subst. word. }
        { apply Hdom_range in Hin. word. } }
    iSplit; first (iPureIntro; congruence).
    iSplit; first (iPureIntro; congruence).
    iSplit; first (iPureIntro; set_solver).
    rewrite big_sepM_insert; last first.
    { apply not_elem_of_dom. rewrite -Hdom_range. lia. }
    iEval (rewrite /named).
    iSplitR "Hreqs"; last first.
    { iApply (big_sepM_mono with "Hreqs").
      iIntros (k req' Hlookup). iDestruct 1 as (Post') "H".
      iExists Post'.
      assert (n ≠ k).
      { intros Heq. congruence. }
      setoid_rewrite lookup_insert_ne; eauto.
    }
    iExists Post.
    iFrame "Hreg Hsaved".
    iLeft. iExists _, _, _. iFrame.
    (* TODO: have to put in the cb fields here *)
    iPureIntro. rewrite lookup_insert //. }
  wp_pures.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc").
  { admit. (* TODO: overflow *) }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc").
  { admit. (* TODO: overflow *) }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_apply (wp_Enc__PutInt with "Henc").
  { admit. (* TODO: overflow *) }
  iIntros "Henc".
  wp_pures.
  iDestruct (is_slice_to_small with "Hslice") as "Hslice".
  iDestruct (is_slice_small_sz with "Hslice") as %Hsz.
  wp_apply (wp_Enc__PutBytes with "[$Henc $Hslice]").
  { admit. } (* TODO: overflow *)
  iIntros "[Henc Hsl]".
  wp_pures.
  wp_apply (wp_Enc__Finish with "[$Henc]").
  iIntros (rep_sl repData).
  iIntros "(%Hhas_encoding & % & Hrep_sl)".
  wp_pures.
  wp_loadField.
  iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
  iNamed "Hhandler".
  wp_apply (wp_Send with "[$]").
  { admit. } (* TODO: overflow *)
  iInv "Hserver_inv" as "Hserver_inner" "Hclo".
  iDestruct "Hserver_inner" as (ms) "(>Hchan'&H)".
  iApply (ncfupd_mask_intro _); first set_solver+.
  iIntros "Hclo'".
  iExists _. iFrame "Hchan'". iNext.
  iIntros "Hchan'". iNamed "H".
  iMod ("Hclo'") as "_".
  iMod ("Hclo" with "[Hmessages Hchan']") as "_".
  { iNext. iExists _. iFrame.
    destruct (decide (Message r repData ∈ ms)).
    { assert (ms ∪ {[Message r repData]} = ms) as -> by set_solver. iFrame. }
    iApply big_sepS_union; first by set_solver.
    iFrame "Hmessages".
    iApply big_sepS_singleton.
    iExists _, _, _, _, _, _, _.
    iExists _, _.
    iFrame "#". iSplit; eauto.
    iPureIntro. simpl. rewrite ?app_nil_l //= in Hhas_encoding. rewrite Hsz.
    assert (U64 (Z.of_nat (int.nat (req.(Slice.sz)))) = req.(Slice.sz)) as ->.
    { word. }
    eauto.
  }
  iModIntro. iIntros "Hsl_rep".
  wp_pures.
Abort.

End rpc_proof.
