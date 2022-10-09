From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require mpaxos.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.mpaxos Require Export ghost_proof marshal_proof.

Section definitions.

Record MPRecord :=
  {
    mp_OpType : Type ;
    mp_has_op_encoding : list u8 → mp_OpType → Prop ;
    mp_next_state : list u8 → mp_OpType → list u8 ;
    mp_compute_reply : list u8 → mp_OpType → list u8 ;
  }.

Context {mp_record:MPRecord}.
Notation OpType := (mp_OpType mp_record).
Notation has_op_encoding := (mp_has_op_encoding mp_record).
Notation next_state := (mp_next_state mp_record).
Notation compute_reply := (mp_compute_reply mp_record).

Definition client_logR := mono_listR (leibnizO (list u8)).

Class mpG Σ := {
    mp_ghostG :> mp_ghostG (EntryType:=(list u8 * (list u8 → iProp Σ))%type) Σ ;
    mp_urpcG :> urpcregG Σ ;
    mp_wgG :> waitgroupG Σ ; (* for apply proof *)
    mp_logG :> inG Σ client_logR;
    mp_apply_escrow_tok :> ghost_varG Σ unit ;
}.

Context `{!heapGS Σ}.
Context `{!mpG Σ}.

Definition own_log γ σ := own γ (●ML{#1/2} (σ : list (leibnizO (list u8)))).

(* RPC specs *)

(* Notation OpType := (mp_OpType mp_record). *)

Context (conf:list mp_server_names).

Definition applyAsFollower_core_spec γ γsrv args σ Q (Φ : u64 -> iProp Σ) : iProp Σ :=
  ("%Hσ_index" ∷ ⌜length σ = (int.nat args.(applyAsFollowerArgs.nextIndex) + 1)%nat⌝ ∗
   "%Hghost_op_σ" ∷ ⌜last σ = Some (args.(applyAsFollowerArgs.state), Q)⌝ ∗
   "%Hno_overflow" ∷ ⌜int.nat args.(applyAsFollowerArgs.nextIndex) < int.nat (word.add args.(applyAsFollowerArgs.nextIndex) 1)⌝ ∗
   "#Hprop_lb" ∷ is_proposal_lb γ args.(applyAsFollowerArgs.epoch) σ ∗
   "#Hprop_facts" ∷ is_proposal_facts conf γ args.(applyAsFollowerArgs.epoch) σ ∗
   "HΨ" ∷ ((is_accepted_lb γsrv args.(applyAsFollowerArgs.epoch) σ -∗ Φ (U64 0)) ∧
           (∀ (err:u64), ⌜err ≠ 0⌝ -∗ Φ err))
    )%I
.

Program Definition applyAsFollowerSpec_spec γ γsrv :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args σ Q,
    ⌜applyAsFollowerArgs.has_encoding encoded_args args⌝ ∗
    applyAsFollower_core_spec γ γsrv args σ Q (λ err, ∀ reply, ⌜reply = u64_le err⌝ -∗ Φ reply)
    )%I
.
Next Obligation.
  rewrite /applyAsFollower_core_spec.
  solve_proper.
Defined.

Definition appN := mpN .@ "app".
Definition escrowN := mpN .@ "escrow".
Definition is_inv γlog γsys :=
  inv appN (∃ σ,
        own_log γlog (fst <$> σ) ∗
        own_ghost γsys σ ∗
        □(
          (* ∀ σ' σ'prefix lastEnt, ⌜prefix σ' σ⌝ -∗ ⌜σ' = σ'prefix ++ [lastEnt]⌝ -∗ (lastEnt.2 (fst <$> σ'prefix))
             *)
          True
        )
      ).

(*
Definition Apply_core_spec γ γlog op enc_op :=
  λ (Φ : ApplyReply.C -> iPropO Σ) ,
  (
  ⌜has_op_encoding enc_op op⌝ ∗
  is_inv γlog γ ∗
  □(|={⊤∖↑pbN,∅}=> ∃ σ, own_log γlog σ ∗ (own_log γlog (σ ++ [op]) ={∅,⊤∖↑pbN}=∗
            Φ (ApplyReply.mkC 0 (compute_reply σ op))
  )) ∗
  □(∀ (err:u64) ret, ⌜err ≠ 0⌝ -∗ Φ (ApplyReply.mkC err ret))
  )%I
.

Program Definition Apply_spec γ :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ op γlog, Apply_core_spec γ γlog op enc_args
                      (λ reply, ∀ enc_reply, ⌜ApplyReply.has_encoding enc_reply reply⌝ -∗ Φ enc_reply)
  )%I
.
Next Obligation.
  unfold Apply_core_spec.
  solve_proper.
Defined.

Definition is_pb_host_pre ρ : (u64 -d> pb_system_names -d> pb_server_names -d> iPropO Σ) :=
  (λ host γ γsrv,
  handler_spec γsrv.(pb_urpc_gn) host (U64 0) (ApplyAsBackup_spec γ γsrv) ∗
  handler_spec γsrv.(pb_urpc_gn) host (U64 1) (SetState_spec γ γsrv) ∗
  handler_spec γsrv.(pb_urpc_gn) host (U64 2) (GetState_spec γ γsrv) ∗
  handler_spec γsrv.(pb_urpc_gn) host (U64 3) (BecomePrimary_spec_pre γ γsrv ρ) ∗
  handler_spec γsrv.(pb_urpc_gn) host (U64 4) (Apply_spec γ) ∗
  handlers_dom γsrv.(pb_urpc_gn) {[ (U64 0) ; (U64 1) ; (U64 2) ; (U64 3) ; (U64 4) ]})%I
.

Instance is_pb_host_pre_contr : Contractive is_pb_host_pre.
Proof.
Admitted.

Definition is_pb_host_def :=
  fixpoint (is_pb_host_pre).
Definition is_pb_host_aux : seal (is_pb_host_def). by eexists. Qed.
Definition is_pb_host := is_pb_host_aux.(unseal).
Definition is_pb_host_eq : is_pb_host = is_pb_host_def := is_pb_host_aux.(seal_eq).

Definition BecomePrimary_spec γ γsrv := BecomePrimary_spec_pre γ γsrv is_pb_host.

Lemma is_pb_host_unfold host γ γsrv:
  is_pb_host host γ γsrv ⊣⊢ is_pb_host_pre (is_pb_host) host γ γsrv
.
Proof.
  rewrite is_pb_host_eq. apply (fixpoint_unfold (is_pb_host_pre)).
Qed.

Global Instance is_pb_host_pers host γ γsrv: Persistent (is_pb_host host γ γsrv).
Proof.
  rewrite is_pb_host_unfold.
  apply _.
Qed.
 *)

(* End RPC specs *)

Definition is_mpaxos_host : (u64 -> mp_system_names -> mp_server_names -> iPropO Σ).
Admitted.

Global Instance is_mpaxos_host_pers host γ γsrv: Persistent (is_mpaxos_host host γ γsrv).
Proof.
Admitted.

Definition is_singleClerk (ck:loc) γ γsrv : iProp Σ :=
  ∃ (cl:loc) srv,
  "#Hcl" ∷ readonly (ck ↦[mpaxos.Clerk :: "cl"] #cl) ∗
  "#Hcl_rpc"  ∷ is_uRPCClient cl srv ∗
  "#Hsrv" ∷ is_mpaxos_host srv γ γsrv
.

(* End clerk specs *)

(* Server-side definitions *)

Definition is_applyFn (applyFn:val) : iProp Σ :=
  ∀ op_sl state_sl (state:list u8) (op_bytes:list u8) op,
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        readonly (is_slice_small op_sl byteT 1 op_bytes) ∗
        readonly (is_slice_small state_sl byteT 1 state)
  }}}
    applyFn (slice_val state_sl) (slice_val op_sl)
  {{{
        newstate_sl reply_sl,
        RET (slice_val newstate_sl, slice_val reply_sl);
        readonly (is_slice_small newstate_sl byteT 1 (next_state state op)) ∗
        readonly (is_slice_small reply_sl byteT 1 (compute_reply state op))
  }}}
.

(* Hides the ghost part of the log; this is suitable for exposing as part of
   interfaces for users of the library.
   . *)
Definition own_Server (s:loc) γ γsrv : iProp Σ :=
  ∃ st (isLeader:bool) (clerks_sl:Slice.t)
    state_sl applyFn clerks,
    let nextIndex := U64 (length st.(mp_log)) in
    let state := (default [] (last (fst <$> st.(mp_log)))) in
  (* physical *)
  "Hepoch" ∷ s ↦[mpaxos.Server :: "epoch"] #(st.(mp_epoch)) ∗
  "HnextIndex" ∷ s ↦[mpaxos.Server :: "nextIndex"] #nextIndex ∗
  "HisLeader" ∷ s ↦[mpaxos.Server :: "isLeader"] #isLeader ∗
  "Hclerks" ∷ s ↦[mpaxos.Server :: "clerks"] (slice_val clerks_sl) ∗
  "Hstate" ∷ s ↦[mpaxos.Server :: "state"] (slice_val state_sl) ∗
  "#Hstate_sl" ∷ readonly (is_slice_small state_sl byteT 1 state) ∗
  "HapplyFn" ∷ s ↦[mpaxos.Server :: "applyFn"] applyFn ∗

  (* clerks *)
  "%Hconf_clerk_len" ∷ ⌜length clerks = length (conf)⌝ ∗
  "#Hclerks_sl" ∷ readonly (is_slice_small clerks_sl ptrT 1 clerks) ∗
  "#Hclerks_rpc" ∷ ([∗ list] ck ; γsrv' ∈ clerks ; conf, is_singleClerk ck γ γsrv') ∗

  (* applyFn callback spec *)
  "#HisApplyFn" ∷ is_applyFn applyFn ∗

  (* ghost-state *)
  "Hghost" ∷ own_replica_ghost conf γ γsrv st ∗

  (* leader-only *)
  "HleaderOnly" ∷ (if isLeader then own_leader_ghost conf γ γsrv st else True) ∗
  "%HaccEpochEq" ∷ ⌜if isLeader then st.(mp_acceptedEpoch) = st.(mp_epoch) else True⌝
.

Definition is_Server (s:loc) γ γsrv : iProp Σ :=
  ∃ (mu:val),
  "#Hmu" ∷ readonly (s ↦[mpaxos.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock mpN mu (own_Server s γ γsrv)
  (* "#Hsys_inv" ∷ sys_inv γ *).

Lemma wp_singleClerk__applyAsFollower ck γ γsrv σ Q args_ptr args reply_ptr init_reply :
  {{{
        "#His_ck" ∷ is_singleClerk ck γ γsrv ∗
        "Hargs" ∷ applyAsFollowerArgs.own args_ptr args ∗
        "Hargs" ∷ applyAsFollowerReply.own reply_ptr init_reply 1 ∗

        "%Hσ_index" ∷ ⌜length σ = (int.nat args.(applyAsFollowerArgs.nextIndex) + 1)%nat⌝ ∗
        "%Hghost_op_σ" ∷ ⌜last σ = Some (args.(applyAsFollowerArgs.state), Q)⌝ ∗
        "%Hno_overflow" ∷ ⌜int.nat args.(applyAsFollowerArgs.nextIndex) < int.nat (word.add args.(applyAsFollowerArgs.nextIndex) 1)⌝ ∗
        "#Hprop_lb" ∷ is_proposal_lb γ args.(applyAsFollowerArgs.epoch) σ ∗
        "#Hprop_facts" ∷ is_proposal_facts conf γ args.(applyAsFollowerArgs.epoch) σ
  }}}
    singleClerk__applyAsFollower #ck #args_ptr #reply_ptr
  {{{
        reply, RET #(); applyAsFollowerReply.own reply_ptr reply 1 ∗
                                                 □if (decide (reply.(applyAsFollowerReply.err) = (U64 0))) then
                                                   is_accepted_lb γsrv args.(applyAsFollowerArgs.epoch) σ
                                                 else
                                                   True
  }}}.
Proof.
Admitted.

Lemma wp_Server__apply_internal s γ γsrv (op:OpType) (op_bytes:list u8) op_sl reply_ptr init_reply Q:
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        is_Server s γ γsrv ∗
        readonly (is_slice_small op_sl byteT 1 op_bytes) ∗
        (|={⊤∖↑ghostN,∅}=> ∃ σ, own_ghost γ σ ∗
            let oldstate := (default [] (last (fst <$> σ))) in
            let newstate := (next_state oldstate op) in
            (own_ghost γ (σ ++ [(newstate, Q)]) ={∅,⊤∖↑ghostN}=∗ True)) ∗
        applyReply.own reply_ptr init_reply 1
  }}}
    mpaxos.Server__apply #s (slice_val op_sl) #reply_ptr
  {{{
        reply, RET #(); £ 1 ∗ £ 1 ∗ applyReply.own reply_ptr reply 1 ∗
        if (decide (reply.(applyReply.err) = 0%Z)) then
          ∃ σ,
            let σphys := (λ x, x.1) <$> σ in
            (* ⌜reply.(applyReply.ret) = compute_reply σphys ghost_op.1⌝ ∗ *)
            let oldstate := (default [] (last (fst <$> σ))) in
            let newstate := (next_state oldstate op) in
            is_ghost_lb γ (σ ++ [(newstate, Q)])
        else
          True
  }}}.
Proof.
  iIntros (Φ) "(%Hop_enc & #Hsrv & #Hop & Hupd & Hreply) HΦ".
  wp_call.
  iNamed "Hsrv".

  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.

  wp_loadField.
  wp_if_destruct.
  { (* case not leader: return error *)
    wp_loadField.
    admit.
  }
  wp_loadField.
  wp_loadField.
  wp_apply ("HisApplyFn" with "[]").
  {
    iFrame "#".
    done.
  }
  iIntros (??) "[#Hnewstate_sl #Hreply_sl]".
  wp_pures.
  wp_storeField.

  iNamed "Hreply".
  wp_storeField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_pures.
  wp_apply (wp_allocStruct).
  { repeat econstructor. done. }
  iIntros (args_ptr) "Hargs".

  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_pures.
  wp_loadField.

  iMod (ghost_leader_propose with "HleaderOnly [] [Hupd]") as "(HleaderOnly & #Hprop_lb & #Hprop_facts)".
  { admit. } (* TODO: get lc *)
  {
    iMod "Hupd".
    iModIntro.
    iDestruct "Hupd" as (?) "[H1 Hupd]".
    iExists _. iFrame "H1".
    iIntros "%Heq Hghost".
    rewrite Heq.
    iMod ("Hupd" with "Hghost").
    iModIntro.
    done.
  }

  iMod (ghost_replica_accept_same_epoch with "Hghost Hprop_lb Hprop_facts") as "Hghost".
  { done. }

  wp_apply (release_spec with "[-HΦ Hreply_epoch Hreply_ret Hreply_ret_sl Hargs]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    iExists _, _, _, _, _, _.
    instantiate (1:=mkMPaxosState _ _ _).
    simpl.
    rewrite HaccEpochEq.
    iFrame "∗ HleaderOnly".
    iFrame "#%".
    iSplitL "HnextIndex".
    {
      iApply to_named.
      iExactEq "HnextIndex".
      f_equal.
      f_equal.
      rewrite app_length.
      simpl.

      (* TODO: pure overflow proof *)
      admit.
    }
    iSplitL; last done.
    iApply to_named.
    replace (default [] (last (st.(mp_log) ++ [(next_state (default [] (last st.(mp_log).*1)) op, Q)]).*1)) with
      (next_state (default [] (last st.(mp_log).*1)) op).
    { done. }

    (* pure list+next_state proof*)
    rewrite fmap_app.
    rewrite last_snoc.
    simpl.
    done.
  }

  set (newstate:=(next_state (default [] (last st.(mp_log).*1)) op)).
  iAssert (|={⊤}=> applyAsFollowerArgs.own args_ptr (applyAsFollowerArgs.mkC
                                               st.(mp_epoch)
                                               (U64 (length st.(mp_log)))
                                               newstate
          ))%I with "[Hargs]" as "Hargs".
  {
    iDestruct (struct_fields_split with "Hargs") as "HH".
    iNamed "HH".
    iExists _.
    iMod (readonly_alloc_1 with "epoch") as "$".
    simpl.
    iMod (readonly_alloc_1 with "nextIndex") as "$".
    iMod (readonly_alloc_1 with "state") as "$".
    iFrame "#".
    done.
  }
  iMod "Hargs" as "#Hargs".

  wp_pures.
  wp_apply (wp_ref_to).
  { eauto. }
  iIntros (numReplies_ptr) "HnumReplies".
  wp_pures.

  iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks_sl2".
  iDestruct (is_slice_small_sz with "Hclerks_sl2") as "%Hclerks_sz".
  iClear "Hclerks_sl2".
  clear q.

  wp_apply (wp_slice_len).
  wp_apply (wp_NewSlice).
  rewrite -Hclerks_sz.
  iIntros (replies_sl) "Hreplies_sl".
  simpl.

  wp_pures.
  set (replyInv:=(
                  ∃ (numReplies:u64) (reply_ptrs:list loc),
                    "HnumReplies" ∷ numReplies_ptr ↦[uint64T] #numReplies ∗
                    "Hreplies_sl" ∷ is_slice_small replies_sl ptrT 1 reply_ptrs ∗
                    "Hreplies" ∷ ([∗ list] i ↦ reply_ptr ; γsrv' ∈ reply_ptrs ; conf,
                    ⌜reply_ptr = null⌝ ∨ □(∃ reply, readonly (applyAsFollowerReply.own reply_ptr reply 1) ∗
                                                   if decide (reply.(applyAsFollowerReply.err) = (U64 0)) then
                                                     is_accepted_lb γsrv' st.(mp_epoch) (st.(mp_log) ++ [(newstate, Q)])
                                                   else
                                                     True
                                         ))
                )%I).
  wp_apply (newlock_spec _ _ replyInv with "[HnumReplies Hreplies_sl]").
  {
    iNext.
    iExists _, _.
    iDestruct (is_slice_to_small with "Hreplies_sl") as "$".
    iFrame "∗".
    iDestruct (big_sepL2_length with "Hclerks_rpc") as "%Hlen".
    iApply big_sepL2_forall.
    rewrite Hlen.
    iSplit.
    { rewrite replicate_length. done. }
    iIntros.
    iLeft.
    iPureIntro.
    rewrite lookup_replicate in H.
    naive_solver.
  }
  iIntros (replyMu) "#HreplyMuInv".
  wp_pures.
  wp_apply (wp_newCond with "HreplyMuInv").
  iIntros (numReplies_cond) "#HnumReplies_cond".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_pures.

  iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks_sl2".
  wp_apply (wp_forSlice (λ _, True%I) (V:=loc) with "[] [$Hclerks_sl2]").
  { (* loop iteration *)
    clear Φ.
    iIntros (?? Φ) "!# (_ & %Hi_le & %Hi_lookup) HΦ".
    wp_call.
    wp_apply (wp_fork with "[]").
    { (* make applyAsFollower RPC and put reply in the replies list *)
      iNext.
      wp_apply (wp_allocStruct).
      { repeat econstructor. }
      clear reply_ptr.
      iIntros (reply_ptr) "Hreply".
      wp_pures.

      (* establish is_singleClerk *)
      iDestruct (big_sepL2_lookup_1_some with "Hclerks_rpc") as (?) "%Hi_conf_lookup".
      { done. }
      iAssert (_) with "Hclerks_rpc" as "Hclerks_rpc2".
      iDestruct (big_sepL2_lookup_acc with "Hclerks_rpc2") as "[#His_ck _]".
      { done. }
      { done. }
      wp_apply (wp_singleClerk__applyAsFollower with "[$His_ck Hreply]").
      {
        iFrame.
        iFrame "Hargs".
        iDestruct (struct_fields_split with "Hreply") as "HH".
        iNamed "HH".
        simpl.
        iSplitL "err".
        {
          instantiate (1:=applyAsFollowerReply.mkC _).
          iFrame.
        }
        iFrame "Hprop_lb Hprop_facts".
        iPureIntro.
        assert ((length st.(mp_log)) = int.nat (length st.(mp_log))).
        { admit. } (* FIXME: maintain list no overflow fact *)
        assert (int.nat (length st.(mp_log)) < int.nat (u64_instance.u64.(word.add) (length st.(mp_log)) 1)) as Hno_overflow.
        { admit. } (* FIXME: overflow check *)
        split.
        { rewrite app_length. simpl. word. }
        split.
        { rewrite last_snoc. done. }
        word.
      }
      iIntros (reply) "Hreply".
      wp_pures.

      wp_apply (acquire_spec with "HreplyMuInv").
      iIntros "[Hlocked Hown]".
      iNamed "Hown".
      wp_pures.
      wp_load.
      wp_store.
      iDestruct (big_sepL2_lookup_2_some with "Hreplies") as (?) "%Hi_replies_lookup".
      { done. }
      wp_apply (wp_SliceSet with "[$Hreplies_sl]").
      {
        done.
      }
      iIntros "Hreplies_sl".
      wp_pures.
      wp_load.
      iDestruct "Hreply" as "[Hreply #Hpost]".
      iMod (readonly_alloc_1 with "Hreply") as "#Hreply".
      wp_apply (wp_If_optional _ _ (True%I)).
      {
        iIntros (?) "_ HΦ'".
        wp_apply (wp_condSignal with "HnumReplies_cond").
        wp_pures.
        by iApply "HΦ'".
      }
      wp_apply (release_spec with "[-]").
      {
        iFrame "# Hlocked".
        iNext.
        iExists _, _.
        iFrame "∗".
        iApply to_named.
        iDestruct (big_sepL2_insert_acc with "Hreplies")  as "[_ Hreplies]".
        { done. }
        { done. }
        iDestruct ("Hreplies" $! reply_ptr x2 with "[]") as "Hreplies".
        {
          iRight.
          iModIntro.
          iExists _.
          iFrame "#".
        }

        replace (<[int.nat i:=x2]> conf) with (conf) ; last first.
        {
          symmetry.
          by apply list_insert_id.
        }
        iFrame "Hreplies".
      }
      done.
    }
    iApply "HΦ".
    done.
  }
  iIntros "_".
  wp_pures.

  wp_apply (acquire_spec with "[$HreplyMuInv]").
  iIntros "[Hlocked Hown]".
  wp_pures.

  wp_forBreak_cond.
  wp_pures.
  iNamed "Hown".
  wp_load.
  wp_pures.
  wp_if_destruct.
  { (* not enough replies, wait for cond *)
    wp_pures.
    wp_apply (wp_condWait with "[-HΦ Hreply_epoch Hreply_ret Hreply_ret_sl]").
    {
      iFrame "#∗".
      iExists _, _.
      iFrame "∗".
    }
    iIntros "[Hlocked Hown]".
    wp_pures.
    iLeft.
    iModIntro.
    iSplitR; first done.
    iFrame.
  }
  (* got enough replies to stop waiting; now we need to count how many successes *)
  iRight.
  iModIntro.
  iSplitR; first done.

  wp_pures.
  wp_apply (wp_ref_to).
  { auto. }
  iIntros (numSuccesses_ptr) "HnumSuccesses".
  wp_pures.

  wp_apply (wp_forSlice (V:=loc) with "[] [$Hreplies_sl]").
  {
    clear Φ.
    iIntros (?? Φ) "!# (Hi & %Hi_lt & %Hi_lookup) HΦ".
    wp_pures.
    wp_if_destruct.
    {
      (* TODO: use Hreplies *)
      admit.
    }
    {
      admit.
    }
  }
  {
    admit.
  }

  iIntros "[Hi Hreplies_sl]".
  wp_pures.
  wp_load.
  wp_pures.
  wp_if_destruct.
  { (* enough acceptances to commit *)
    admit.
  }
  { (* error, too few successful applyAsFollower() RPCs *)
    wp_storeField.
    iApply "HΦ".
    admit.
  }
Admitted.

End definitions.
