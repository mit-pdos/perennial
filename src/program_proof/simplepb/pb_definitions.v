From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.simplepb Require Export pb_ghost.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb Require Import pb_marshal_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section pb_definitions.

Record PBRecord :=
  {
    pb_OpType:Type ;
    pb_has_op_encoding : list u8 → pb_OpType → Prop ;
    pb_has_snap_encoding: list u8 → (list pb_OpType) → Prop ;
    pb_has_op_encoding_injective : ∀ o1 o2 l, pb_has_op_encoding l o1 → pb_has_op_encoding l o2 → o1 = o2 ;
    pb_compute_reply : list pb_OpType → pb_OpType → list u8 ;
  }.

Context {pb_record:PBRecord}.
Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_snap_encoding := (pb_has_snap_encoding pb_record).
Notation has_op_encoding_injective := (pb_has_op_encoding_injective pb_record).
Notation compute_reply := (pb_compute_reply pb_record).

Definition client_logR := mono_listR (leibnizO OpType).

Class pbG Σ := {
    pb_ghostG :> pb_ghostG (EntryType:=(OpType * (list OpType → iProp Σ))%type) Σ ;
    pb_urpcG :> urpcregG Σ ;
    (* pb_wgG :> waitgroupG Σ ; *)
    pb_logG :> inG Σ client_logR;
    pb_apply_escrow_tok :> ghost_varG Σ unit ;
}.

Context `{!heapGS Σ, !stagedG Σ}.
Context `{!pbG Σ}.

Definition own_log γ σ := own γ (●ML{#1/2} (σ : list (leibnizO OpType))).

(* RPC specs *)

Program Definition ApplyAsBackup_spec γ γsrv :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args σ op Q,
    ⌜ApplyArgs.has_encoding encoded_args args⌝ ∗
    ⌜length σ = int.nat args.(ApplyArgs.index)⌝ ∗
    ⌜has_op_encoding args.(ApplyArgs.op) op⌝∗
    ⌜last σ = Some (op, Q) ⌝ ∗
    is_proposal_lb γ args.(ApplyArgs.epoch) σ ∗
    is_proposal_facts γ args.(ApplyArgs.epoch) σ ∗
    (∀ error (reply:list u8),
        ⌜has_encoding_Error reply error⌝ -∗
        (if (decide (error = (U64 0))) then is_accepted_lb γsrv args.(ApplyArgs.epoch) σ else True) -∗
        Φ reply)
    )%I
.
Next Obligation.
  solve_proper.
Defined.

Definition SetState_core_spec γ γsrv args σ :=
  λ (Φ : u64 -> iPropO Σ) ,
  (
    ⌜has_snap_encoding args.(SetStateArgs.state) (fst <$> σ)⌝ ∗
    ⌜length σ = int.nat args.(SetStateArgs.nextIndex)⌝ ∗
    is_proposal_lb γ args.(SetStateArgs.epoch) σ ∗
    is_proposal_facts γ args.(SetStateArgs.epoch) σ ∗
    (
      (is_epoch_lb γsrv args.(SetStateArgs.epoch) -∗
       is_accepted_lb γsrv args.(SetStateArgs.epoch) σ -∗
       Φ 0) ∧
      (∀ err, ⌜err ≠ U64 0⌝ → Φ err))
    )%I
.

Program Definition SetState_spec γ γsrv :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args σ,
    ⌜SetStateArgs.has_encoding enc_args args⌝ ∗
    SetState_core_spec γ γsrv args σ (λ err, ∀ reply, ⌜reply = u64_le err⌝ -∗ Φ reply)
  )%I
.
Next Obligation.
  unfold SetState_core_spec.
  solve_proper.
Defined.

Definition GetState_core_spec γ γsrv (epoch:u64) ghost_epoch_lb :=
  λ (Φ : GetStateReply.C -> iPropO Σ) ,
  (
    ( is_epoch_lb γsrv ghost_epoch_lb ∗
      (
      (∀ epochacc σ snap,
            ⌜int.nat ghost_epoch_lb ≤ int.nat epochacc⌝ -∗
            ⌜int.nat epochacc ≤ int.nat epoch⌝ -∗
            is_accepted_ro γsrv epochacc σ -∗
            is_proposal_facts γ epochacc σ -∗
            is_proposal_lb γ epochacc σ -∗
            ⌜has_snap_encoding snap (fst <$> σ)⌝ -∗
            ⌜length σ = int.nat (U64 (length σ))⌝ -∗
                 Φ (GetStateReply.mkC 0 (length σ) snap)) ∧
      (∀ err, ⌜err ≠ U64 0⌝ → Φ (GetStateReply.mkC err 0 [])))
    )
    )%I
.

Program Definition GetState_spec γ γsrv :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args epoch_lb,
    ⌜GetStateArgs.has_encoding enc_args args⌝ ∗
    GetState_core_spec γ γsrv args.(GetStateArgs.epoch) epoch_lb (λ reply, ∀ enc_reply, ⌜GetStateReply.has_encoding enc_reply reply⌝ -∗ Φ enc_reply)
  )%I
.
Next Obligation.
  unfold GetState_core_spec.
  solve_proper.
Defined.

(* End RPC specs *)

Definition is_pb_host γ γsrv (host:u64) : iProp Σ :=
  handler_spec γsrv.(urpc_gn) host (U64 0) (ApplyAsBackup_spec γ γsrv) ∗
  handler_spec γsrv.(urpc_gn) host (U64 1) (SetState_spec γ γsrv) ∗
  handler_spec γsrv.(urpc_gn) host (U64 2) (GetState_spec γ γsrv) ∗
  handlers_dom γsrv.(urpc_gn) {[ (U64 0) ; (U64 1) ; (U64 2) ; (U64 3) ; (U64 4) ]}
.

Definition is_Clerk (ck:loc) γ γsrv : iProp Σ :=
  ∃ (cl:loc) srv,
  "#Hcl" ∷ readonly (ck ↦[pb.Clerk :: "cl"] #cl) ∗
  "#Hcl_rpc"  ∷ is_uRPCClient cl srv ∗
  "#Hsrv" ∷ is_pb_host γ γsrv srv
.
Lemma wp_MakeClerk host γ γsrv :
  {{{
        is_pb_host γ γsrv host
  }}}
    MakeClerk #host
  {{{
        ck, RET #ck; is_Clerk ck γ γsrv
  }}}.
Proof.
Admitted.

(* FIXME: these belong in a separate file. These will be proved from the RPC specs. *)
(* Clerk specs *)
Lemma wp_Clerk__Apply γ γsrv ck args_ptr (epoch index:u64) σ ghost_op op_sl op :
  {{{
        "#HisClerk" ∷ is_Clerk ck γ γsrv ∗
        "#HepochLb" ∷ is_epoch_lb γsrv epoch ∗
        "#Hprop_lb" ∷ is_proposal_lb γ epoch σ ∗
        "#Hprop_facts" ∷ is_proposal_facts γ epoch σ ∗
        "%Hghost_op_σ" ∷ ⌜last σ = Some ghost_op⌝ ∗
        "%Hghost_op_op" ∷ ⌜has_op_encoding op ghost_op.1⌝ ∗
        "%Hσ_index" ∷ ⌜length σ = ((int.nat index) + 1)%nat⌝ ∗
        "%HnoOverflow" ∷ ⌜int.nat index < int.nat (word.add index 1)⌝ ∗

        "#HargEpoch" ∷ readonly (args_ptr ↦[pb.ApplyArgs :: "epoch"] #epoch) ∗
        "#HargIndex" ∷ readonly (args_ptr ↦[pb.ApplyArgs :: "index"] #index) ∗
        "#HargOp" ∷ readonly (args_ptr ↦[pb.ApplyArgs :: "op"] (slice_val op_sl)) ∗
        "#HopSl" ∷ readonly (is_slice_small op_sl byteT 1 op)
  }}}
    Clerk__Apply #ck #args_ptr
  {{{
        (err:u64), RET #err; □ if (decide (err = 0)) then
                               is_accepted_lb γsrv epoch σ
                             else True
  }}}.
Proof.
Admitted.

(* XXX: GetState doesn't actually *need* to do any epoch comparison.
   It could simply return the state it has and the epoch for which it is the state.
   The issue is that an old epoch would then be able to seal future epochs,
   which might hurt liveness.
 *)
(* FIXME: rename to GetStateAndSeal *)
Lemma wp_Clerk__GetState γ γsrv ck args_ptr (epoch_lb:u64) (epoch:u64) :
  {{{
        "#Hck" ∷ is_Clerk ck γ γsrv ∗
        "#Hghost_epoch_lb" ∷ is_epoch_lb γsrv epoch_lb ∗
        "Hargs" ∷ GetStateArgs.own args_ptr (GetStateArgs.mkC epoch)
  }}}
    Clerk__GetState #ck #args_ptr
  {{{
        (reply:loc) (err:u64), RET #reply;
        if (decide (err = U64 0)) then
            ∃ epochacc σ enc,
            ⌜int.nat epoch_lb ≤ int.nat epochacc⌝ ∗
            ⌜int.nat epochacc ≤ int.nat epoch⌝ ∗
            is_accepted_ro γsrv epochacc σ ∗
            is_proposal_facts γ epochacc σ ∗
            is_proposal_lb γ epochacc σ ∗
            GetStateReply.own reply (GetStateReply.mkC 0 (length σ) enc) ∗
            ⌜has_snap_encoding enc (fst <$> σ)⌝ ∗
            ⌜length σ = int.nat (U64 (length σ))⌝
          else
            GetStateReply.own reply (GetStateReply.mkC err 0 [])
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep) "Hrep".
  wp_pures.
  iNamed "Hck".
  wp_apply (GetStateArgs.wp_Encode with "[$Hargs]").
  iIntros (enc_args enc_args_sl) "(%Henc_args & Henc_args_sl & Hargs)".
  wp_loadField.
  iDestruct (is_slice_to_small with "Henc_args_sl") as "Henc_args_sl".
  wp_apply (wp_frame_wand with "HΦ").
  wp_apply (wp_Client__Call2 with "Hcl_rpc [] Henc_args_sl Hrep").
  {
    iDestruct "Hsrv" as "[_ [_ [$ _]]]".
  }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold GetState_spec.
    iExists _, _.
    iSplitR; first done.
    simpl.
    unfold GetState_core_spec.
    iFrame "Hghost_epoch_lb".
    iSplit.
    { (* No error from RPC, state was returned *)
      iIntros (?????) "???".
      iIntros (??? Henc_reply) "Hargs_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      wp_apply (GetStateReply.wp_Decode with "[$Hrep_sl]").
      { done. }
      iIntros (reply_ptr) "Hreply".
      iIntros "HΦ".
      iApply ("HΦ" $! _ 0).
      iExists _, _, _.
      iFrame "Hreply".
      iSplitR; first done.
      iSplitR; first done.
      eauto with iFrame.
    }
    { (* GetState was rejected by the server (e.g. stale epoch number) *)
      iIntros (err) "%Herr_nz".
      iIntros.
      wp_pures.
      wp_load.
      wp_apply (GetStateReply.wp_Decode with "[-] []").
      { eauto. }
      iModIntro.
      iIntros (reply_ptr) "Hreply".

      iIntros "HΦ".
      iApply ("HΦ" $! _ err).
      destruct (decide _).
      {
        exfalso. done.
      }
      {
        done.
      }
    }
  }
  { (* RPC error *)
    iIntros.
    wp_pures.
    wp_if_destruct.
    {
      wp_apply (wp_allocStruct).
      { repeat econstructor. apply zero_val_ty'. done. }
      iIntros (reply_ptr) "Hreply".
      iDestruct (struct_fields_split with "Hreply") as "HH".
      iNamed "HH".
      iIntros "HΦ".
      iApply ("HΦ" $! _ 3).
      iExists _. simpl. iFrame.
      replace (zero_val (slice.T byteT)) with (slice_val Slice.nil) by done.
      iFrame.
      iApply is_slice_small_nil.
      done.
    }
    { exfalso. done. }
  }
Qed.

Lemma wp_Clerk__BecomePrimary γ γsrv ck args_ptr (epoch:u64) servers server_γs σ :
  {{{
        "#HisClerk" ∷ is_Clerk ck γ γsrv ∗
        "#Hconf" ∷ is_epoch_config γ epoch server_γs ∗
        "#Hhost" ∷ ([∗ list] γsrv;host ∈ server_γs;servers, is_pb_host γ γsrv host) ∗
        "#Hacc" ∷ is_accepted_lb γsrv epoch σ ∗
        "Hprop" ∷ own_proposal γ epoch σ ∗ (* FIXME: escrow this *)
        "Hargs" ∷ BecomePrimaryArgs.own args_ptr (BecomePrimaryArgs.mkC epoch servers)
  }}}
    Clerk__BecomePrimary #ck #args_ptr
  {{{
        (err:u64), RET #err; True
  }}}.
Proof.
Admitted.

(* End clerk specs *)

(* Server-side definitions *)

Implicit Type (own_StateMachine: u64 → list OpType → bool → (u64 → list OpType → bool → iProp Σ) → iProp Σ).
(* StateMachine *)
Definition is_ApplyFn own_StateMachine (applyFn:val) (P:u64 → list (OpType) → bool → iProp Σ) : iProp Σ :=
  ∀ op_sl (epoch:u64) (σ:list OpType) (op_bytes:list u8) (op:OpType) Q,
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        readonly (is_slice_small op_sl byteT 1 op_bytes) ∗
        (P epoch σ false ={⊤}=∗ P epoch (σ ++ [op]) false ∗ Q) ∗
        own_StateMachine epoch σ false P
  }}}
    applyFn (slice_val op_sl)
  {{{
        reply_sl,
        RET (slice_val reply_sl);
        is_slice reply_sl byteT 1 (compute_reply σ op) ∗
        own_StateMachine epoch (σ ++ [op]) false P ∗
        Q
  }}}
.

Definition is_SetStateAndUnseal_fn own_StateMachine (set_state_fn:val) P : iProp Σ :=
  ∀ σ_prev (epoch_prev:u64) σ epoch (snap:list u8) snap_sl sealed Q,
  {{{
        ⌜has_snap_encoding snap σ⌝ ∗
        is_slice snap_sl byteT 1 snap ∗
        (P epoch_prev σ_prev sealed ={⊤}=∗ P epoch σ false ∗ Q) ∗
        own_StateMachine epoch_prev σ_prev false P
  }}}
    set_state_fn (slice_val snap_sl) #epoch
  {{{
        RET #();
        own_StateMachine epoch σ false P ∗
        Q
  }}}
.

Definition is_GetStateAndSeal_fn own_StateMachine (get_state_fn:val) P : iProp Σ :=
  ∀ σ epoch sealed,
  {{{
        own_StateMachine epoch σ sealed P
  }}}
    get_state_fn #()
  {{{
        snap_sl snap,
        RET (slice_val snap_sl);
        ⌜has_snap_encoding snap σ⌝ ∗
        own_StateMachine epoch σ true P
  }}}
.

Definition accessP_fact own_StateMachine P : iProp Σ :=
  □ (∀ Φ E σ epoch sealed,
  (P epoch σ sealed ={E}=∗ P epoch σ sealed ∗ Φ) -∗
  own_StateMachine epoch σ sealed P ={E}=∗
  wpc_nval E (own_StateMachine epoch σ sealed P ∗ Φ))
  (* FIXME: this wpc_nval is there because P might be in a crash borrow in
     own_StateMachine. Joe said it imght be possible to get rid of wpc_nval by
     changing the model of crash_borrows by using later credits. *)
.

Definition is_StateMachine (sm:loc) own_StateMachine P : iProp Σ :=
  ∃ (applyFn:val) (getFn:val) (setFn:val),
  "#Happly" ∷ readonly (sm ↦[pb.StateMachine :: "Apply"] applyFn) ∗
  "#HapplySpec" ∷ is_ApplyFn own_StateMachine applyFn P ∗

  "#HsetState" ∷ readonly (sm ↦[pb.StateMachine :: "SetStateAndSeal"] setFn) ∗
  "#HsetStateSpec" ∷ is_SetStateAndUnseal_fn own_StateMachine setFn P ∗

  "#HgetState" ∷ readonly (sm ↦[pb.StateMachine :: "GetStateAndSeal"] getFn) ∗
  "#HgetStateSpec" ∷ is_GetStateAndSeal_fn own_StateMachine getFn P ∗

  "#HaccP" ∷ accessP_fact own_StateMachine P.

(* Hides the ghost part of the log; this is suitable for exposing as part of
   interfaces for users of the library. For now, it's only part of the crash
   obligation. *)
Definition own_Server_ghost γ γsrv epoch σphys sealed : iProp Σ :=
  ∃ σ, ⌜σphys = σ.*1⌝ ∗ (own_replica_ghost γ γsrv epoch σ sealed)
.

Definition own_Server (s:loc) γ γsrv own_StateMachine : iProp Σ :=
  ∃ (epoch:u64) σg (nextIndex:u64) (sealed:bool) (isPrimary:bool) (sm:loc) (clerks_sl:Slice.t),
  (* physical *)
  "Hepoch" ∷ s ↦[pb.Server :: "epoch"] #epoch ∗
  "HnextIndex" ∷ s ↦[pb.Server :: "nextIndex"] #nextIndex ∗
  "HisPrimary" ∷ s ↦[pb.Server :: "isPrimary"] #isPrimary ∗
  "Hsealed" ∷ s ↦[pb.Server :: "sealed"] #sealed ∗
  "Hsm" ∷ s ↦[pb.Server :: "sm"] #sm ∗
  "Hclerks" ∷ s ↦[pb.Server :: "clerks"] (slice_val clerks_sl) ∗

  (* state-machine callback specs *)
  "#HisSm" ∷ is_StateMachine sm own_StateMachine (own_Server_ghost γ γsrv) ∗

  (* ghost-state *)
  "Hstate" ∷ own_StateMachine epoch (fst<$>σg) sealed (own_Server_ghost γ γsrv) ∗
  "%Hσ_nextIndex" ∷ ⌜length σg = int.nat nextIndex⌝ ∗
  (* ghost witnesses for convenience; we could insist on extracting them from own_Server_ghost *)
  "#Hs_acc_lb" ∷ is_accepted_lb γsrv epoch σg ∗
  "#Hs_prop_lb" ∷ is_proposal_lb γ epoch σg ∗
  "#Hs_prop_facts" ∷ is_proposal_facts γ epoch σg ∗

  (* primary-only *)
  "HprimaryOnly" ∷ if isPrimary then (
            ∃ (clerks:list loc) (backups:list pb_server_names),
            "%Hconf_clerk_len" ∷ ⌜length clerks = length (γsrv :: backups)⌝ ∗
            "#Hconf" ∷ is_epoch_config γ epoch (γsrv :: backups) ∗
                     (* FIXME: ptrT vs refT (struct.t Clerk) *)
            "#Hclerks_sl" ∷ readonly (is_slice_small clerks_sl ptrT 1 clerks) ∗
            "#Hclerks_rpc" ∷ ([∗ list] ck ; γsrv' ∈ clerks ; backups, is_Clerk ck γ γsrv' ∗
                                                                      is_epoch_lb γsrv' epoch
                             ) ∗
            "#Hprop_facts" ∷ is_proposal_facts γ epoch σg ∗
            "Hproposal" ∷ own_proposal γ epoch σg
        )
                   else True
.

Definition is_Server (s:loc) γ γsrv : iProp Σ :=
  ∃ (mu:val) own_StateMachine,
  "#Hmu" ∷ readonly (s ↦[pb.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock pbN mu (own_Server s γ γsrv own_StateMachine) ∗
  "#Hsys_inv" ∷ sys_inv γ.

Lemma wp_Server__isEpochStale {stk} (s:loc) γ γsrv (currEpoch epoch:u64) σ sealed own_StateMachine:
  {{{
        is_epoch_lb γsrv epoch ∗
        s ↦[pb.Server :: "epoch"] #currEpoch ∗
        accessP_fact own_StateMachine (own_Server_ghost γ γsrv) ∗
        own_StateMachine currEpoch σ sealed (own_Server_ghost γ γsrv)
  }}}
    pb.Server__isEpochStale #s #epoch @ stk
  {{{
        RET #(bool_decide (int.Z epoch < int.Z currEpoch));
        ⌜int.nat currEpoch ≥ int.nat epoch⌝ ∗
        s ↦[pb.Server :: "epoch"] #currEpoch ∗
        own_StateMachine currEpoch σ sealed (own_Server_ghost γ γsrv)
  }}}
.
Proof.
  iIntros (Φ) "(#Hlb & HcurrEpoch & #HaccP & Hstate) HΦ".
  wp_call.
  iMod ("HaccP" $! (⌜int.nat currEpoch ≥ int.nat epoch⌝)%I with "[] Hstate") as "HH".
  {
    iIntros "H".
    iDestruct "H" as (?) "[%Hre H]".
    iNamed "H".
    iDestruct (mono_nat_lb_own_valid with "Hepoch_ghost Hlb") as %[_ Hineq].
    iModIntro.
    iSplitL; last done.
    iExists _; iFrame "∗#%".
  }
  unfold wpc_nval.
  wp_bind (struct.loadF _ _ _).
  iApply (wpc_wp _ _ _ _ (True%I)).
  wpc_apply "HH".
  { done. }
  { done. }
  iCache with "".
  { done. }
  wpc_loadField.
  iIntros "[Hstate %Hineq]".
  wp_pures.
  iModIntro.
  iApply ("HΦ").
  iFrame "∗%".
Qed.

End pb_definitions.
