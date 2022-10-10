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

Definition client_logR := dfrac_agreeR (leibnizO (list u8)).

Class mpG Σ := {
    mp_ghostG :> mp_ghostG (EntryType:=(list u8 * (list u8 → iProp Σ))%type) Σ ;
    mp_urpcG :> urpcregG Σ ;
    mp_wgG :> waitgroupG Σ ; (* for apply proof *)
    mp_logG :> inG Σ client_logR;
    mp_apply_escrow_tok :> ghost_varG Σ unit ;
}.

Context `{!heapGS Σ}.
Context `{!mpG Σ}.

Definition own_state γ ς := own γ (to_dfrac_agree (DfracOwn (1/2)) (ς : (leibnizO (list u8)))).

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

(* TODO: copied from pb_definitions.v *)
Definition appN := mpN .@ "app".
Definition escrowN := mpN .@ "escrow".

Definition get_state (σ:list (list u8 * (list u8 → iProp Σ))) := default [] (last (fst <$> σ)).

Definition is_inv γlog γsys :=
  inv appN (∃ log,
        own_state γlog (get_state log) ∗
        own_ghost γsys log ∗
        □(
          (* XXX: this is a bit different from pb_definitions.v *)
          (* This says that for all (log'prefix ++ [lastEnt]) ⪯ log,
             lastEnt.Q (state of log'prefix) is true.
           *)
          ∀ log' log'prefix lastEnt, ⌜prefix log' log⌝ -∗
                ⌜log' = log'prefix ++ [lastEnt]⌝ -∗
                (lastEnt.2 (get_state log'prefix))
        )
      ).

Definition apply_core_spec γ γlog op enc_op :=
  λ (Φ : applyReply.C -> iPropO Σ) ,
  (
  ⌜has_op_encoding enc_op op⌝ ∗
  is_inv γlog γ ∗
  □(|={⊤∖↑mpN,∅}=> ∃ ς, own_state γlog ς ∗ (own_state γlog (next_state ς op) ={∅,⊤∖↑mpN}=∗
            Φ (applyReply.mkC 0 (compute_reply ς op))
  )) ∗
  □(∀ (err:u64) ret, ⌜err ≠ 0⌝ -∗ Φ (applyReply.mkC err ret))
  )%I
.

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
        is_slice_small reply_sl byteT 1 (compute_reply state op)
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
  "%HnextIndex_nooverflow" ∷ ⌜length st.(mp_log) = int.nat (length st.(mp_log))⌝ ∗

  (* clerks *)
  "%Hconf_clerk_len" ∷ ⌜length clerks = length (conf)⌝ ∗
  "#Hclerks_sl" ∷ readonly (is_slice_small clerks_sl ptrT 1 clerks) ∗
  "#Hclerks_rpc" ∷ ([∗ list] ck ; γsrv' ∈ clerks ; conf, is_singleClerk ck γ γsrv') ∗

  (* applyFn callback spec *)
  "#HisApplyFn" ∷ is_applyFn applyFn ∗

  (* ghost-state *)
  "Hghost" ∷ own_replica_ghost conf γ γsrv st ∗
  "#Hinv" ∷ sys_inv conf γ ∗

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
            ⌜reply.(applyReply.ret) = compute_reply (get_state σ) op⌝ ∗
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
    wp_apply (release_spec with "[-HΦ Hreply]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _, _, _, _, _, _.
      iFrame  "∗#%".
    }
    wp_pure1_credit "Hcred1".
    wp_pures.
    iNamed "Hreply".
    wp_apply (wp_storeField with "[$Hreply_epoch]").
    { eauto. }
    iIntros "Hreply_epoch".
    wp_pure1_credit "Hcred2".
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iFrame.
    instantiate (1:=(applyReply.mkC _ _)).
    iSplitL.
    {
      iExists _. iFrame.
    }
    done.
  }
  wp_loadField.
  wp_loadField.
  wp_apply ("HisApplyFn" with "[]").
  {
    iFrame "#".
    done.
  }
  iIntros (??) "[#Hnewstate_sl Hret_sl]".
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
  wp_apply (std_proof.wp_SumAssumeNoOverflow).
  iIntros "%Hno_overflow".
  wp_storeField.
  wp_loadField.
  wp_pure1_credit "Hlc".
  wp_loadField.

  iMod (ghost_leader_propose with "HleaderOnly Hlc [Hupd]") as "(HleaderOnly & #Hprop_lb & #Hprop_facts)".
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

  wp_apply (release_spec with "[-HΦ Hreply_epoch Hreply_ret Hret_sl Hargs]").
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
      rewrite HnextIndex_nooverflow in Hno_overflow.
      replace (int.Z (U64 1)) with (1)%Z in Hno_overflow by word.
      admit.
    }
    iSplitL; last first.
    {
      iSplitL.
      {
        iPureIntro.
        rewrite app_length.
        simpl.
        word.
      }
      done.
    }
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
                    "#Hreplies" ∷ ([∗ list] i ↦ reply_ptr ; γsrv' ∈ reply_ptrs ; conf,
                    ⌜reply_ptr = null⌝ ∨ □(∃ reply, readonly (applyAsFollowerReply.own reply_ptr reply 1) ∗
                                                   if decide (reply.(applyAsFollowerReply.err) = (U64 0)) then
                                                     is_accepted_lb γsrv' st.(mp_epoch) (st.(mp_log) ++ [(newstate, Q)])
                                                   else
                                                     True
                                         ))
                )%I).
  wp_apply (newlock_spec mpN _ replyInv with "[HnumReplies Hreplies_sl]").
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
        iDestruct (big_sepL2_insert_acc with "Hreplies")  as "[_ Hreplies2]".
        { done. }
        { done. }
        iDestruct ("Hreplies2" $! reply_ptr x2 with "[]") as "Hreplies3".
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
        iFrame "Hreplies3".
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
    wp_apply (wp_condWait with "[-HΦ Hreply_epoch Hreply_ret Hret_sl]").
    {
      iFrame "#∗".
      iExists _, _.
      iFrame "∗#".
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

  set (I:=λ (i:u64), (
                 ∃ (W: gset nat),
                 "%HW_in_range" ∷ ⌜∀ s, s ∈ W → s < int.nat i⌝ ∗
                 "%HW_size_nooverflow" ∷ ⌜(size W) ≤ int.nat i⌝ ∗
                 "HnumSuccesses" ∷ numSuccesses_ptr ↦[uint64T] #(U64 (size W)) ∗
                 "#Hacc_lbs" ∷ ([∗ list] s ↦ γsrv' ∈ conf, ⌜s ∈ W⌝ → is_accepted_lb γsrv' st.(mp_epoch) (st.(mp_log) ++ [(newstate, Q)]))
      )%I).

  wp_apply (wp_forSlice (V:=loc) I _ _ _ _ _ reply_ptrs with "[] [HnumSuccesses Hreplies_sl]").
  2: {
    iFrame "Hreplies_sl".

    iExists ∅.
    rewrite size_empty.
    iFrame.
    iSplitL.
    { iPureIntro. done. }
    iSplitL.
    { iPureIntro. done. }
    iApply (big_sepL_forall).
    iIntros.
    exfalso.
    done.
  }
  {
    clear Φ.
    iIntros (?? Φ) "!# (Hi & %Hi_lt & %Hi_lookup) HΦ".
    iNamed "Hi".
    wp_pures.
    wp_if_destruct.
    {
      iDestruct (big_sepL2_lookup_1_some with "Hreplies") as (?) "%Hi_conf_lookup".
      { done. }
      iDestruct (big_sepL2_lookup_acc with "Hreplies") as "[#Hreply_post _]".
      { done. }
      { done. }
      iDestruct "Hreply_post" as "[%Hbad|#Hreply_post]".
      {
        exfalso. rewrite Hbad in Heqb0. done.
      }
      iDestruct "Hreply_post" as (?) "[#Hreply Hpost]".
      iMod (readonly_load with "Hreply") as (?) "Hreplyq".
      wp_loadField.
      wp_if_destruct.
      { (* increase size of W *)
        wp_load.
        wp_store.
        rewrite -Heqb1.
        iEval (rewrite decide_True) in "Hpost".
        iApply "HΦ".
        iModIntro.
        iExists (W ∪ {[ int.nat i ]}).
        iSplitR.
        { (* prove that the new set W is still in range *)
          replace (int.nat (word.add i (U64 1))) with (int.nat i + 1) by word.
          iPureIntro.
          intros ? Hin.
          rewrite elem_of_union in Hin.
          destruct Hin as [Hold|Hnew].
          {
            specialize (HW_in_range s0 Hold). word.
          }
          {
            rewrite elem_of_singleton in Hnew.
            rewrite Hnew.
            word.
          }
        }

        rewrite size_union; last first.
        {
          apply disjoint_singleton_r.
          destruct (decide (int.nat i ∈ W)).
          {
            exfalso.
            specialize (HW_in_range (int.nat i) e).
            word.
          }
          done.
        }
        rewrite size_singleton.

        iSplitL "".
        {
          iPureIntro.
          word.
        }

        iSplitL "HnumSuccesses".
        {
          iApply to_named.
          iExactEq "HnumSuccesses".
          f_equal.
          f_equal.

          apply lookup_lt_Some in Hi_conf_lookup.
          rewrite -Hconf_clerk_len Hclerks_sz in Hi_conf_lookup.
          assert (Z.of_nat (size W) < int.Z clerks_sl.(Slice.sz))%Z by word.
          (* TODO: overflow of size of W proof *)
          admit.
        }

        iApply (big_sepL_impl with "Hacc_lbs").
        iModIntro.
        iIntros (?? ?) "Hacc_wand".
        iIntros (Hin).
        rewrite elem_of_union in Hin.
        destruct Hin as [Hold|Hnew].
        {
          iApply "Hacc_wand".
          done.
        }
        {
          rewrite elem_of_singleton in Hnew.
          rewrite Hnew.
          replace (x0) with (x2).
          { done. }
          rewrite Hnew in H.
          rewrite Hi_conf_lookup in H.
          by injection H.
        }
      }
      { (* node i didn't accept, don't change W *)
        iModIntro.
        iApply "HΦ".
        iExists W.
        iFrame "HnumSuccesses".
        iFrame "Hacc_lbs".
        iPureIntro.
        replace (int.nat (word.add i (U64 1))) with (int.nat i + 1) by word.
        split.
        {
          intros.
          specialize (HW_in_range s0 H).
          word.
        }
        {
          word.
        }
      }
    }
    { (* node i didn't reply, don't change W *)
      iModIntro.
      iApply "HΦ".
      iExists W.
      iFrame "HnumSuccesses".
      iFrame "Hacc_lbs".
      iPureIntro.
      replace (int.nat (word.add i (U64 1))) with (int.nat i + 1) by word.
      split.
      {
        intros.
        specialize (HW_in_range s0 H).
        word.
      }
      {
        word.
      }
    }
  }

  iIntros "[Hi Hreplies_sl]".
  iDestruct (is_slice_small_sz with "Hreplies_sl") as "%Hreplies_sz".
  iNamed "Hi".
  wp_pure1_credit "Hcred1".
  wp_pure1_credit "Hcred2".
  wp_load.
  wp_pures.
  wp_if_destruct.
  { (* enough acceptances to commit *)
    wp_storeField.

    iDestruct (big_sepL2_length with "Hreplies") as "%Hreplies_len_eq_conf".
    replace (int.nat replies_sl.(Slice.sz)) with (length conf) in HW_in_range; last first.
    {
      word.
    }

    iDestruct (establish_committed_by with "Hacc_lbs") as "Hcom".
    {
      done.
    }
    {
      assert (2 * size W > int.Z (u64_instance.u64.(word.mul) 2 (size W)))%Z.
      { admit. } (* FIXME: check for multiplication overflow *)
      word.
    }
    iMod (ghost_commit with "Hinv Hcom Hprop_lb Hprop_facts") as "Hlb".
    iApply "HΦ".
    iModIntro.
    iFrame.
    instantiate (1:=(applyReply.mkC _ _)).
    iSplitL "Hreply_epoch Hreply_ret Hret_sl".
    {
      iExists _.
      iFrame.
    }
    simpl.
    destruct (decide _).
    {
      iExists _.
      iFrame "Hlb".
      done.
    }
    {
      done.
    }
  }
  { (* error, too few successful applyAsFollower() RPCs *)
    wp_storeField.
    iApply "HΦ".
    iModIntro.
    iFrame.
    instantiate (1:=(applyReply.mkC _ _)).
    iSplitL "Hreply_epoch Hreply_ret Hret_sl".
    {
      iExists _.
      iFrame.
    }
    done.
  }
Admitted.

(* TODO: copied from pb_apply_proof.v *)
Lemma prefix_app_cases {A} (σ σ':list A) e:
  σ' `prefix_of` σ ++ [e] →
  σ' `prefix_of` σ ∨ σ' = (σ++[e]).
Proof.
Admitted.

Lemma wp_Server__Apply (s:loc) γlog γ γsrv op_sl op (enc_op:list u8) init_reply reply_ptr Ψ (Φ: val → iProp Σ) :
  is_Server s γ γsrv -∗
  readonly (is_slice_small op_sl byteT 1 enc_op) -∗
  applyReply.own reply_ptr init_reply 1 -∗
  (∀ reply, Ψ reply -∗ applyReply.own reply_ptr reply 1 -∗ Φ #()) -∗
  apply_core_spec γ γlog op enc_op Ψ -∗
  WP (mpaxos.Server__apply #s (slice_val op_sl) #reply_ptr) {{ Φ }}
.
Proof using Type*.
  iIntros "#Hsrv #Hop_sl Hreply".
  iIntros "HΨ HΦ".
  iApply (wp_frame_wand with "HΨ").
  iDestruct "HΦ" as "(%Hop_enc & #Hinv & #Hupd & Hfail_Φ)".
  iMod (ghost_var_alloc (())) as (γtok) "Htok".
  iApply wp_fupd.
  wp_apply (wp_Server__apply_internal _ _ _ op _ _ _ _
      (λ ς, inv escrowN (
        Ψ (applyReply.mkC 0 (compute_reply ς op)) ∨
          ghost_var γtok 1 ()
        )%I)
             with "[$Hsrv $Hop_sl $Hreply Hupd]").
  {
    iSplitL ""; first done.
    iInv "Hinv" as "HH" "Hclose".
    iDestruct "HH" as (?) "(>Hstate & >Hghost & #HQs)".
    iMod (fupd_mask_subseteq (⊤∖↑mpN)) as "Hmask".
    {
      assert ((↑ghostN:coPset) ⊆ (↑mpN:coPset)).
      { apply nclose_subseteq. }
      assert ((↑appN:coPset) ⊆ (↑mpN:coPset)).
      { apply nclose_subseteq. }
      set_solver.
    }
    iMod "Hupd".
    iModIntro.
    iDestruct "Hupd" as (ς) "[Hstate2 Hupd]".
    iDestruct (own_valid_2 with "Hstate Hstate2") as %Hvalid.
    rewrite dfrac_agree_op_valid_L in Hvalid.
    destruct Hvalid as [_ Heq].
    rewrite Heq.
    iExists _; iFrame.
    iIntros "Hghost".

    iMod (own_update_2 with "Hstate Hstate2") as "Hstate".
    {
      apply (dfrac_agree_update_2 _ _ _ _ ((next_state ς op): leibnizO (list u8))).
      rewrite dfrac_op_own.
      rewrite Qp.half_half.
      done.
    }
    iDestruct "Hstate" as "[Hstate Hstate2]".
    iMod ("Hupd" with "Hstate2") as "Hupd".

    iAssert (|={↑escrowN}=> inv escrowN ((Ψ (applyReply.mkC 0 (compute_reply ς op)))
                                  ∨ ghost_var γtok 1 ()))%I
            with "[Hupd]" as "Hinv2".
    {
      iMod (inv_alloc with "[-]") as "$"; last done.
      iNext.
      iIntros.
      iLeft.
      iIntros.
      iApply "Hupd".
    }

    iMod "Hmask" as "_".
    iMod (fupd_mask_subseteq (↑escrowN)) as "Hmask".
    {
      assert ((↑escrowN:coPset) ## (↑ghostN:coPset)).
      { by apply ndot_ne_disjoint. }
      assert ((↑escrowN:coPset) ## (↑appN:coPset)).
      { by apply ndot_ne_disjoint. }
      set_solver.
    }
    iMod "Hinv2" as "#HΦ_inv".
    iMod "Hmask".

    iMod ("Hclose" with "[HQs Hghost Hstate]").
    {
      iNext.
      iExists _; iFrame.
      unfold get_state.
      rewrite fmap_app.
      rewrite last_snoc.
      simpl.
      rewrite -Heq.
      iFrame.

      iModIntro.
      iIntros.

      apply prefix_app_cases in H as [Hprefix_of_old|Hnew].
      {
        iApply "HQs".
        { done. }
        { done. }
      }
      {
        rewrite Hnew in H0.
        replace (log'prefix) with (log); last first.
        { (* TODO: list_solver *)
          apply (f_equal reverse) in H0.
          rewrite reverse_snoc in H0.
          rewrite reverse_snoc in H0.
          inversion H0.
          apply (f_equal reverse) in H2.
          rewrite reverse_involutive in H2.
          rewrite reverse_involutive in H2.
          done.
        }

        eassert (_ = lastEnt) as <-.
        { eapply (suffix_snoc_inv_1 _ _ _ log'prefix). rewrite -H0.
          done. }
        simpl.
        iFrame "HΦ_inv".
      }
    }
    iModIntro.
    done.
  }
  iIntros (reply).
  iIntros "(Hcred & Hcred2 & Hreply & Hpost)".

  destruct (decide (reply.(applyReply.err) = U64 0)).
  { (* no error *)
    iNamed "Hreply".
    rewrite e.
    iDestruct "Hpost" as (?) "[%Hrep #Hghost_lb]".
    rewrite Hrep.
    iInv "Hinv" as "HH" "Hclose".
    {
      iDestruct "HH" as (?) "(>Hlog & >Hghost & #HQs)".
      iMod (lc_fupd_elim_later with "Hcred HQs") as "#HQ".
      iDestruct (own_valid_2 with "Hghost Hghost_lb") as %Hvalid.
      rewrite mono_list_both_dfrac_valid_L in Hvalid.
      destruct Hvalid as [_ Hvalid].
      iSpecialize ("HQ" $! _ σ _ with "[] []").
      { done. }
      { done. }
      simpl.
      iMod ("Hclose" with "[Hghost Hlog]") as "_".
      {
        iNext.
        iExists _; iFrame "∗#".
      }

      iInv "HQ" as "Hescrow" "Hclose".
      iDestruct "Hescrow" as "[HΦ|>Hbad]"; last first.
      {
        iDestruct (ghost_var_valid_2 with "Htok Hbad") as %Hbad.
        exfalso. naive_solver.
      }
      iMod ("Hclose" with "[$Htok]").
      iMod (lc_fupd_elim_later with "Hcred2 HΦ") as "HΦ".
      iModIntro.
      iIntros "HΨ".
      iApply ("HΨ" with "HΦ").
      iExists _.
      simpl.
      iFrame.
    }
  }
  {
    iIntros.
    iNamed "Hreply".
    iModIntro.
    iIntros "HΨ".
    iApply ("HΨ" with "[Hfail_Φ]").
    {
      iApply "Hfail_Φ".
      done.
    }
    iExists _.
    iFrame.
  }
Qed.

End definitions.
