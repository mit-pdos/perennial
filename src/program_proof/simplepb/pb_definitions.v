From Perennial.base_logic Require Import lib.saved_prop.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Export pb_ghost.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb Require Import pb_marshal_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.reconnectclient Require Import proof.

Record PBRecord :=
  {
    pb_OpType:Type ;
    pb_OpType_EqDecision:EqDecision pb_OpType;
    pb_has_op_encoding : list u8 → pb_OpType → Prop ;
    pb_has_snap_encoding: list u8 → (list pb_OpType) → Prop ;
    pb_compute_reply : list pb_OpType → pb_OpType → list u8 ;
  }.

Section pb_global_definitions.

Context {pb_record:PBRecord}.
Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_snap_encoding := (pb_has_snap_encoding pb_record).
Notation compute_reply := (pb_compute_reply pb_record).

Inductive GhostOpType :=
  | rw_op : OpType → GhostOpType
  | ro_op : OpType → GhostOpType.

(* opsfull has all the ghost ops (RO and RW) in it as well as the gname for the
   Q for that op. get_rwops returns the RW ops only with the gnames removed.
   Generalizing it to an arbitrary extra type A instead of gname
   specifically, because sometimes we want to use get_rwops on a list that has
   an iProp predicate instead of the gname (see is_inv). *)
Definition get_rwops {A} (opsfull:list (GhostOpType * A)) : list OpType :=
  concat (map (λ opfull, match opfull with
                         | (rw_op op, γ) => [op]
                         | (ro_op _, _) => []
                         end) opsfull).

Definition client_logR := mono_listR (leibnizO OpType).

Class pbG Σ := {
    (*
    pb_ghostG :> pb_ghostG (EntryType:=(OpType * (list OpType → iProp Σ))%type) Σ ;
     *)
    pb_ghostG :> pb_ghostG (EntryType:=(GhostOpType * gname)) Σ ;
    pb_savedG :> savedPredG Σ (list OpType);
    pb_urpcG :> urpcregG Σ ;
    pb_wgG :> waitgroupG Σ ; (* for apply proof *)
    pb_logG :> inG Σ client_logR;
    pb_apply_escrow_tok :> ghost_varG Σ unit ;
}.

Definition pbΣ :=
  #[pb_ghostΣ (EntryType:=(GhostOpType * gname)); savedPredΣ (list OpType) ; urpcregΣ ; waitgroupΣ ;
    GFunctor (client_logR) ; ghost_varΣ unit].
Global Instance subG_pbΣ {Σ} : subG (pbΣ) Σ → (pbG Σ).
Proof. solve_inG. Qed.

Context `{!gooseGlobalGS Σ}.
Context `{!pbG Σ}.

Definition own_log γ σ := own γ (●ML{#1/2} (σ : list (leibnizO OpType))).

(* RPC specs *)

Definition ApplyAsBackup_core_spec γ γsrv args opsfull op Q (Φ : u64 -> iProp Σ) : iProp Σ :=
  ("%Hσ_index" ∷ ⌜length (get_rwops opsfull) = (int.nat args.(ApplyAsBackupArgs.index) + 1)%nat⌝ ∗
   "%Hhas_encoding" ∷ ⌜has_op_encoding args.(ApplyAsBackupArgs.op) op⌝ ∗
   "%Hghost_op_σ" ∷ ⌜last opsfull = Some (rw_op op, Q)⌝ ∗
   "%Hno_overflow" ∷ ⌜int.nat args.(ApplyAsBackupArgs.index) < int.nat (word.add args.(ApplyAsBackupArgs.index) 1)⌝ ∗
   "#Hepoch_lb" ∷ is_epoch_lb γsrv args.(ApplyAsBackupArgs.epoch) ∗
   "#Hprop_lb" ∷ is_proposal_lb γ args.(ApplyAsBackupArgs.epoch) opsfull ∗
   "#Hprop_facts" ∷ is_proposal_facts γ args.(ApplyAsBackupArgs.epoch) opsfull ∗
   "HΨ" ∷ ((is_accepted_lb γsrv args.(ApplyAsBackupArgs.epoch) opsfull -∗ Φ (U64 0)) ∧
           (∀ (err:u64), ⌜err ≠ 0⌝ -∗ Φ err))
    )%I
.

Program Definition ApplyAsBackup_spec γ γsrv :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args σ op Q,
    ⌜ApplyAsBackupArgs.has_encoding encoded_args args⌝ ∗
    ApplyAsBackup_core_spec γ γsrv args σ op Q (λ err, ∀ reply, ⌜reply = u64_le err⌝ -∗ Φ reply)
    )%I
.
Next Obligation.
  unfold ApplyAsBackup_core_spec.
  solve_proper.
Defined.

Definition SetState_core_spec γ γsrv args opsfull :=
  λ (Φ : u64 -> iPropO Σ) ,
  (
    ⌜has_snap_encoding args.(SetStateArgs.state) (get_rwops opsfull)⌝ ∗
    ⌜length (get_rwops opsfull) = int.nat args.(SetStateArgs.nextIndex)⌝ ∗
    is_proposal_lb γ args.(SetStateArgs.epoch) opsfull ∗
    is_proposal_facts γ args.(SetStateArgs.epoch) opsfull ∗
    (
      (is_epoch_lb γsrv args.(SetStateArgs.epoch) -∗
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
    (is_epoch_lb γsrv ghost_epoch_lb ∗
      (
      (∀ epochacc opsfull snap,
            ⌜int.nat ghost_epoch_lb ≤ int.nat epochacc⌝ -∗
            ⌜int.nat epochacc ≤ int.nat epoch⌝ -∗
            is_accepted_ro γsrv epochacc opsfull -∗
            is_proposal_facts γ epochacc opsfull -∗
            is_proposal_lb γ epochacc opsfull -∗
            ⌜has_snap_encoding snap (get_rwops opsfull)⌝ -∗
            ⌜length (get_rwops opsfull) = int.nat (U64 (length (get_rwops opsfull)))⌝ -∗
                 Φ (GetStateReply.mkC 0 (length (get_rwops opsfull)) snap)) ∧
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

Definition BecomePrimary_core_spec γ γsrv args σ backupγ (ρ:u64 -d> pb_system_names -d> pb_server_names -d> iPropO Σ) :=
  λ (Φ : u64 -> iPropO Σ) ,
  (
    is_epoch_lb γsrv args.(BecomePrimaryArgs.epoch) ∗
    is_epoch_config γ args.(BecomePrimaryArgs.epoch) (γsrv :: backupγ) ∗
    (* FIXME: want this to be "is_pb_host", but that will require recursion *)
    ([∗ list] host ; γsrv' ∈ args.(BecomePrimaryArgs.replicas) ; γsrv :: backupγ, (ρ host γ γsrv') ∗ is_epoch_lb γsrv' args.(BecomePrimaryArgs.epoch)) ∗
    become_primary_escrow γ γsrv args.(BecomePrimaryArgs.epoch) σ ∗
    is_proposal_lb γ args.(BecomePrimaryArgs.epoch) σ ∗
    is_proposal_facts γ args.(BecomePrimaryArgs.epoch) σ ∗
    (∀ err, Φ err)
    )%I
.

Program Definition BecomePrimary_spec_pre γ γsrv ρ :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args σ confγ,
    ⌜BecomePrimaryArgs.has_encoding enc_args args⌝ ∗
    BecomePrimary_core_spec γ γsrv args σ confγ ρ (λ err, ∀ reply, ⌜reply = u64_le err⌝ -∗ Φ reply)
  )%I
.
Next Obligation.
  unfold BecomePrimary_core_spec.
  solve_proper.
Defined.

Definition appN := pbN .@ "app".
Definition escrowN := pbN .@ "escrow".

Definition own_ghost' γsys (opsfullQ : list (GhostOpType * (list OpType → iProp Σ))) : iProp Σ :=
  ∃ ops_gnames: list (GhostOpType * gname),
    own_ghost γsys ops_gnames ∗
    ⌜opsfullQ.*1 = ops_gnames.*1 ⌝ ∗
    [∗ list] k↦Φ;γ ∈ snd <$> opsfullQ; snd <$> ops_gnames, saved_pred_own γ DfracDiscarded Φ.

Definition is_inv γlog γsys :=
  inv appN (∃ opsfullQ,
      own_ghost' γsys opsfullQ ∗
      own_log γlog (get_rwops opsfullQ) ∗
      □(
        ∀ opsPre opsPrePre lastEnt,
        ⌜prefix opsPre opsfullQ⌝ -∗ ⌜opsPre = opsPrePre ++ [lastEnt]⌝ -∗
        (lastEnt.2 (get_rwops opsPrePre))
      )
      ).

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

Definition RoApplyAsBackup_core_spec γ γsrv args opsfull (Φ : u64 -> iProp Σ) : iProp Σ :=
  ("%Hσ_index" ∷ ⌜length (get_rwops opsfull) = (int.nat args.(RoApplyAsBackupArgs.nextIndex))%nat⌝ ∗
   "#Hepoch_lb" ∷ is_epoch_lb γsrv args.(RoApplyAsBackupArgs.epoch) ∗
   "#Hprop_lb" ∷ is_proposal_lb γ args.(RoApplyAsBackupArgs.epoch) opsfull ∗
   "#Hprop_facts" ∷ is_proposal_facts γ args.(RoApplyAsBackupArgs.epoch) opsfull ∗
   "HΨ" ∷ ((is_accepted_lb γsrv args.(RoApplyAsBackupArgs.epoch) opsfull -∗ Φ (U64 0)) ∧
           (∀ (err:u64), ⌜err ≠ 0⌝ -∗ Φ err))
    )%I
.

Program Definition RoApplyAsBackup_spec γ γsrv :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args opsfull,
    ⌜RoApplyAsBackupArgs.has_encoding encoded_args args⌝ ∗
    RoApplyAsBackup_core_spec γ γsrv args opsfull (λ err, ∀ reply, ⌜reply = u64_le err⌝ -∗ Φ reply)
    )%I
.
Next Obligation.
  unfold RoApplyAsBackup_core_spec.
  solve_proper.
Defined.

Definition RoApply_core_spec γ γlog op enc_op :=
  λ (Φ : ApplyReply.C -> iPropO Σ) ,
  (
  ⌜has_op_encoding enc_op op⌝ ∗
  is_inv γlog γ ∗
  □(|={⊤∖↑pbN,∅}=> ∃ σ, own_log γlog σ ∗ (own_log γlog σ ={∅,⊤∖↑pbN}=∗
            Φ (ApplyReply.mkC 0 (compute_reply σ op))
  )) ∗
  □(∀ (err:u64) ret, ⌜err ≠ 0⌝ -∗ Φ (ApplyReply.mkC err ret))
  )%I
.

Program Definition RoApply_spec γ :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ op γlog, RoApply_core_spec γ γlog op enc_args
                      (λ reply, ∀ enc_reply, ⌜ApplyReply.has_encoding enc_reply reply⌝ -∗ Φ enc_reply)
  )%I
.
Next Obligation.
  unfold RoApply_core_spec.
  solve_proper.
Defined.



Definition is_pb_host_pre ρ : (u64 -d> pb_system_names -d> pb_server_names -d> iPropO Σ) :=
  (λ host γ γsrv,
  ∃ γrpc,
  handler_spec γrpc host (U64 0) (ApplyAsBackup_spec γ γsrv) ∗
  handler_spec γrpc host (U64 1) (SetState_spec γ γsrv) ∗
  handler_spec γrpc host (U64 2) (GetState_spec γ γsrv) ∗
  handler_spec γrpc host (U64 3) (BecomePrimary_spec_pre γ γsrv ρ) ∗
  handler_spec γrpc host (U64 4) (Apply_spec γ) ∗
  handler_spec γrpc host (U64 5) (RoApplyAsBackup_spec γ γsrv) ∗
  handler_spec γrpc host (U64 6) (RoApply_spec γ) ∗
  handlers_dom γrpc {[ (U64 0) ; (U64 1) ; (U64 2) ; (U64 3) ; (U64 4) ; (U64 5) ; (U64 6) ]})%I
.

Instance is_pb_host_pre_contr : Contractive is_pb_host_pre.
Proof.
  intros n ?? Hρ. rewrite /is_pb_host_pre.
  intros ???. f_equiv. intros ?.
  do 5 (f_contractive || f_equiv).
  rewrite /BecomePrimary_spec_pre /BecomePrimary_core_spec.
  intros args Φ. simpl. repeat f_equiv. apply Hρ.
Qed.

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

(* End RPC specs *)

Definition own_ephemeral_proposal γeph (epoch:u64) (opsfull:list (GhostOpType * gname)) : iProp Σ :=
  own γeph {[ epoch := (●ML (opsfull : list (leibnizO _)))]}.

Definition is_ephemeral_proposal_lb γeph (epoch:u64) (opsfull:list (GhostOpType * gname)) : iProp Σ :=
  own γeph {[ epoch := (◯ML (opsfull : list (leibnizO _)))]}.

Definition is_ephemeral_proposal_sealed γeph (epoch:u64) : iProp Σ :=
  ∃ opsfull, own γeph {[ epoch := (●ML□ (opsfull : list (leibnizO _)))]}.

Definition own_unused_ephemeral_proposals γeph (epoch:u64) : iProp Σ :=
  [∗ set] epoch' ∈ (fin_to_set u64), ⌜int.nat epoch' <= int.nat epoch⌝ ∨ own_ephemeral_proposal γeph epoch' []
.

(* Encapsulates the protocol-level ghost resources of a replica server; this is
   suitable for exposing as part of interfaces for users of the library. For
   now, it's only part of the crash obligation. *)
Definition own_Server_ghost γ γsrv γeph epoch ops sealed : iProp Σ :=
  ∃ opsfull,
  "%Hre" ∷ ⌜ops = get_rwops opsfull⌝ ∗
  "#Heph_lb" ∷ is_ephemeral_proposal_lb γeph epoch opsfull ∗
  (* XXX: this ephemeral_proposal is really only used on the primary. The
     invariant could maintain this only in the case that the server is primary,
     but then we would need to prove that a server is definitely not primary
     when it gets an ApplyAsBackup RPC. To avoid that annoyance, the proof keeps
     this everywhere *)
  "Hghost" ∷ (own_replica_ghost γ γsrv epoch opsfull sealed) ∗
  "Hprim" ∷ (own_primary_ghost γ γsrv epoch opsfull) ∗
  "#Heph_sealed" ∷ □(if sealed then is_ephemeral_proposal_sealed γeph epoch else True)
.

End pb_global_definitions.

Section pb_local_definitions.
(* definitions that refer to a particular node *)

Context {pb_record:PBRecord}.
Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_snap_encoding := (pb_has_snap_encoding pb_record).
Notation compute_reply := (pb_compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).

Context `{!heapGS Σ}.
Context `{!pbG Σ}.

Definition is_Clerk (ck:loc) γ γsrv : iProp Σ :=
  ∃ (cl:loc) srv,
  "#Hcl" ∷ readonly (ck ↦[pb.Clerk :: "cl"] #cl) ∗
  "#Hcl_rpc"  ∷ is_ReconnectingClient cl srv ∗
  "#Hsrv" ∷ is_pb_host srv γ γsrv 
.

(* End clerk specs *)

(* Server-side definitions *)

Implicit Type (own_StateMachine: u64 → list OpType → bool → (u64 → list OpType → bool → iProp Σ) → iProp Σ).
(* StateMachine *)
Definition is_ApplyFn own_StateMachine (startApplyFn:val) (P:u64 → list (OpType) → bool → iProp Σ) : iProp Σ :=
  ∀ op_sl (epoch:u64) (σ:list OpType) (op_bytes:list u8) (op:OpType) Q,
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        readonly (is_slice_small op_sl byteT 1 op_bytes) ∗
        (* XXX: This is the weakest mask that the pb library is compatible with.
           By making the mask weak, we allow for more possible implementations
           of startApplyFn, so we give a stronger spec to the client. The chain
           of callbacks had made it confusing which way is weaker and which way
           stronger.
         *)
        (P epoch σ false ={↑pbN}=∗ P epoch (σ ++ [op]) false ∗ Q) ∗
        own_StateMachine epoch σ false P
  }}}
    startApplyFn (slice_val op_sl)
  {{{
        reply_sl q (waitFn:goose_lang.val),
        RET (slice_val reply_sl, waitFn);
        is_slice_small reply_sl byteT q (compute_reply σ op) ∗
        own_StateMachine epoch (σ ++ [op]) false P ∗
        (∀ Ψ, (Q -∗ Ψ #()) -∗ WP waitFn #() {{ Ψ }})
  }}}
.

Definition is_SetStateAndUnseal_fn own_StateMachine (set_state_fn:val) P : iProp Σ :=
  ∀ σ_prev (epoch_prev:u64) σ epoch (snap:list u8) snap_sl sealed Q,
  {{{
        ⌜ (length σ < 2 ^ 64)%Z ⌝ ∗
        ⌜has_snap_encoding snap σ⌝ ∗
        readonly (is_slice_small snap_sl byteT 1 snap) ∗
        (P epoch_prev σ_prev sealed ={↑pbN}=∗ P epoch σ false ∗ Q) ∗
        own_StateMachine epoch_prev σ_prev sealed P
  }}}
    set_state_fn (slice_val snap_sl) #(U64 (length σ)) #epoch
  {{{
        RET #();
        own_StateMachine epoch σ false P ∗
        Q
  }}}
.

Definition is_GetStateAndSeal_fn own_StateMachine (get_state_fn:val) P : iProp Σ :=
  ∀ σ epoch sealed Q,
  {{{
        own_StateMachine epoch σ sealed P ∗
        (P epoch σ sealed ={↑pbN}=∗ P epoch σ true ∗ Q)
  }}}
    get_state_fn #()
  {{{
        snap_sl snap,
        RET (slice_val snap_sl);
        readonly (is_slice_small snap_sl byteT 1 snap) ∗
        ⌜has_snap_encoding snap σ⌝ ∗
        own_StateMachine epoch σ true P ∗
        Q
  }}}
.

Definition is_ApplyReadonlyFn own_StateMachine (startApplyFn:val) (P:u64 → list (OpType) → bool → iProp Σ) : iProp Σ :=
  ∀ op_sl (epoch:u64) (σ:list OpType) (op_bytes:list u8) (op:OpType),
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        readonly (is_slice_small op_sl byteT 1 op_bytes) ∗
        own_StateMachine epoch σ false P
  }}}
    startApplyFn (slice_val op_sl)
  {{{
        reply_sl q,
        RET (slice_val reply_sl);
        is_slice_small reply_sl byteT q (compute_reply σ op) ∗
        own_StateMachine epoch σ false P
  }}}
.

Definition accessP_fact own_StateMachine P : iProp Σ :=
  □ (£ 1 -∗ (∀ Φ σ epoch sealed,
     (∀ σold sealedold E, P epoch σold sealedold ={E}=∗ P epoch σold sealedold ∗ Φ) -∗
  own_StateMachine epoch σ sealed P -∗ |NC={⊤}=>
  wpc_nval ⊤ (own_StateMachine epoch σ sealed P ∗ Φ)))
  (* FIXME: this wpc_nval is there because P might be in a crash borrow in
     own_StateMachine. Joe said it imght be possible to get rid of wpc_nval by
     changing the model of crash_borrows by using later credits. *)
.

Definition is_StateMachine (sm:loc) own_StateMachine P : iProp Σ :=
  tc_opaque (
  ∃ (applyFn:val) (applyRoFn:val) (getFn:val) (setFn:val),
  "#Happly" ∷ readonly (sm ↦[pb.StateMachine :: "StartApply"] applyFn) ∗
  "#HapplySpec" ∷ is_ApplyFn own_StateMachine applyFn P ∗

  "#HsetState" ∷ readonly (sm ↦[pb.StateMachine :: "SetStateAndUnseal"] setFn) ∗
  "#HsetStateSpec" ∷ is_SetStateAndUnseal_fn own_StateMachine setFn P ∗

  "#HgetState" ∷ readonly (sm ↦[pb.StateMachine :: "GetStateAndSeal"] getFn) ∗
  "#HgetStateSpec" ∷ is_GetStateAndSeal_fn own_StateMachine getFn P ∗

  "#HapplyReadonly" ∷ readonly (sm ↦[pb.StateMachine :: "ApplyReadonly"] applyRoFn) ∗
  "#HapplyReadonlySpec" ∷ is_ApplyReadonlyFn own_StateMachine applyRoFn P ∗

  "#HaccP" ∷ accessP_fact own_StateMachine P)%I
.

Global Instance is_StateMachine_pers sm own_StateMachine P :
  Persistent (is_StateMachine sm own_StateMachine P).
Proof.
unfold is_StateMachine. unfold tc_opaque. apply _.
Qed.

Definition numClerks : nat := 32.

Notation GhostOpType := (GhostOpType (pb_record:=pb_record)).

Definition is_possible_Primary (isPrimary:bool) γ γeph γsrv clerks_sl epoch
           (nextIndex committedNextIndex committedNextRoIndex nextRoIndex:u64)
           (opsfull_ephemeral: list (GhostOpType * gname)): iProp Σ:=
  tc_opaque (if isPrimary then (
            ∃ (clerkss:list Slice.t) (backups:list pb_server_names) (ops_commit_full:list (GhostOpType * gname)),
            "#Htok_used_witness" ∷ is_tok γsrv epoch ∗
            "%Hclerkss_len" ∷ ⌜length clerkss = numClerks⌝ ∗
            "#Hconf" ∷ is_epoch_config γ epoch (γsrv :: backups) ∗
                     (* FIXME: ptrT vs refT (struct.t Clerk) *)
            "#Hclerkss_sl" ∷ readonly (is_slice_small clerks_sl (slice.T ptrT) 1 clerkss) ∗

            "#Hclerkss_rpc" ∷ ([∗ list] clerks_sl ∈ clerkss,
                                  ∃ clerks,
                                  "#Hclerks_sl" ∷ readonly (is_slice_small clerks_sl ptrT 1 clerks) ∗
                                  "%Hclerks_conf" ∷ ⌜length clerks = length backups⌝ ∗
                                  "#Hclerks_rpc" ∷ ([∗ list] ck ; γsrv' ∈ clerks ; backups, is_Clerk ck γ γsrv' ∗ is_epoch_lb γsrv' epoch)
                             ) ∗
            (* committed witness for committed state *)
            "#Hcommit_lb" ∷ is_ghost_lb γ ops_commit_full ∗
            "#Heph_commit_lb" ∷ is_ephemeral_proposal_lb γeph epoch ops_commit_full ∗
            "%HcommitLen" ∷ ⌜int.nat committedNextIndex ≤ int.nat nextIndex⌝ ∗
            "%HcommitRoNz" ∷ ⌜int.nat committedNextIndex < int.nat nextIndex → int.nat committedNextRoIndex = 0⌝ ∗
            (* opsfull_eph has `nextRoIndex` RO ops as its tail. *)
            "%HcommitLen" ∷ ⌜length (get_rwops ops_commit_full) = int.nat committedNextIndex⌝ ∗
            "%Heph_proposal" ∷ ⌜∃ opsfull_eph_ro,
                                suffix opsfull_eph_ro opsfull_ephemeral ∧
                                length opsfull_eph_ro = int.nat nextRoIndex ∧
                                get_rwops opsfull_eph_ro = []⌝ ∗
            "%HcommitRoLen" ∷ ⌜ ∃ ops_commit_ro,
                                suffix ops_commit_ro ops_commit_full ∧
                                length ops_commit_ro = int.nat committedNextRoIndex ∧
                                get_rwops ops_commit_ro = []⌝
      )%I
      else True%I)
.

Global Instance is_possible_Primary_pers (isPrimary:bool) γ γeph γsrv clerks_sl epoch
           (nextIndex committedNextIndex committedNextRoIndex nextRoIndex:u64)
           (opsfull_ephemeral: list (GhostOpType * gname)):
Persistent (is_possible_Primary isPrimary γ γeph γsrv clerks_sl epoch
           nextIndex committedNextIndex committedNextRoIndex nextRoIndex
           opsfull_ephemeral).
Proof.
unfold is_possible_Primary. unfold tc_opaque. destruct isPrimary; apply _.
Qed.

Definition own_Server (s:loc) γ γsrv γeph own_StateMachine mu : iProp Σ :=
  ∃ (epoch:u64) (nextIndex durableNextIndex:u64) ops_durable_full (sealed:bool) (isPrimary:bool)
    (sm:loc) (clerks_sl:Slice.t) (opAppliedConds_loc:loc) (opAppliedConds:gmap u64 loc)
    (durableNextIndex_cond:loc)
    (* read-only operation state: *)
    (committedNextIndex nextRoIndex committedNextRoIndex:u64)
    (roOpsToPropose_cond committedNextRoIndex_cond:loc)
    opsfull_ephemeral
  ,
  let ops:=(get_rwops opsfull_ephemeral) in
  (* non-persistent physical *)
  "Hepoch" ∷ s ↦[pb.Server :: "epoch"] #epoch ∗
  "HnextIndex" ∷ s ↦[pb.Server :: "nextIndex"] #nextIndex ∗
  "HisPrimary" ∷ s ↦[pb.Server :: "isPrimary"] #isPrimary ∗
  "Hsealed" ∷ s ↦[pb.Server :: "sealed"] #sealed ∗
  "Hsm" ∷ s ↦[pb.Server :: "sm"] #sm ∗
  "Hclerks" ∷ s ↦[pb.Server :: "clerks"] (slice_val clerks_sl) ∗
  "HdurableNextIndex" ∷ s ↦[pb.Server :: "durableNextIndex"] #durableNextIndex ∗
  "HdurableNextIndex_cond" ∷ s ↦[pb.Server :: "durableNextIndex_cond"] #durableNextIndex_cond ∗
  "HcommittedNextIndex" ∷ s ↦[pb.Server :: "committedNextIndex"] #committedNextIndex ∗
  "HnextRoIndex" ∷ s ↦[pb.Server :: "nextRoIndex"] #nextRoIndex ∗
  "HcommittedNextRoIndex" ∷ s ↦[pb.Server :: "committedNextRoIndex"] #committedNextRoIndex ∗
  "HroOpsToPropose_cond" ∷ s ↦[pb.Server :: "roOpsToPropose_cond"] #roOpsToPropose_cond ∗
  "HcommittedNextRoIndex_cond" ∷ s ↦[pb.Server :: "committedNextRoIndex_cond"] #committedNextRoIndex_cond ∗
  (* backup sequencer *)
  "HopAppliedConds" ∷ s ↦[pb.Server :: "opAppliedConds"] #opAppliedConds_loc ∗
  "HopAppliedConds_map" ∷ is_map opAppliedConds_loc 1 opAppliedConds ∗

  (* non-persistent ghost state *)
  "Heph" ∷ (if sealed then True else own_ephemeral_proposal γeph epoch opsfull_ephemeral) ∗
  "Heph_unused" ∷ own_unused_ephemeral_proposals γeph epoch ∗
  "Hstate" ∷ own_StateMachine epoch ops sealed (own_Server_ghost γ γsrv γeph) ∗

  (* persistent physical state *)
  "#HopAppliedConds_conds" ∷ ([∗ map] i ↦ cond ∈ opAppliedConds, is_cond cond mu) ∗
  "#HdurableNextIndex_is_cond" ∷ is_cond durableNextIndex_cond mu ∗
  "#HroOpsToPropose_is_cond" ∷ is_cond roOpsToPropose_cond mu ∗
  "#HcommittedNextRoIndex_is_cond" ∷ is_cond committedNextRoIndex_cond mu ∗

  (* state-machine callback specs *)
  "#HisSm" ∷ is_StateMachine sm own_StateMachine (own_Server_ghost γ γsrv γeph) ∗

  (* epoch lower bound *)
  "#Hs_epoch_lb" ∷ is_epoch_lb γsrv epoch ∗

  (* persistent ghost-state *)
  "#Heph_prop_lb" ∷ □(if isPrimary then True else is_proposal_lb γ epoch opsfull_ephemeral) ∗
  (* accepted witness for durable state *)
  "#Hdurable_lb" ∷ is_accepted_lb γsrv epoch ops_durable_full ∗
  "#Heph_valid" ∷ is_proposal_valid γ opsfull_ephemeral ∗

  "%Hσ_nextIndex" ∷ ⌜length ops = int.nat nextIndex⌝ ∗
  "%HdurableLen" ∷ ⌜length (get_rwops ops_durable_full) = int.nat durableNextIndex⌝ ∗

  (* `committedRoNextIndex` read-only ops have been committed *)

  (* Want to add pure invariant: nextIndex ≠ committedNextIndex → committedNextRoIndex = 0.
     Q: Is this invariant true?
     A: No. ApplyRoThread increases committedNextRoIndex without increasing
     committedNextIndex (even though it provably could also increase that).
     Let's suppose we don't change the impl to make this part of the proof
     easier.

     Here's what *is* true. The first (committedNextRoIndex) ops of the
     (nextRoIndex) ro ops are committed. To maintain that, need another
     committed list. This list has an ephemeral_lb (so it agres with
     opsfull_eph), has all the same RW ops as opsfull_eph, and has
     committedNextRoIndex RO ops as suffix.
   *)

  (* primary-only *)
  "#HprimaryOnly" ∷ is_possible_Primary isPrimary γ γeph γsrv clerks_sl epoch
                                        nextIndex committedNextIndex committedNextRoIndex
                                        nextRoIndex opsfull_ephemeral
.

Definition is_Server (s:loc) γ γsrv : iProp Σ :=
  ∃ (mu:val) own_StateMachine γeph,
  "#Hmu" ∷ readonly (s ↦[pb.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock pbN mu (own_Server s γ γsrv γeph own_StateMachine mu) ∗
  "#Hsys_inv" ∷ sys_inv γ.

Lemma wp_Server__isEpochStale {stk} (s:loc) (currEpoch epoch:u64) :
  {{{
        s ↦[pb.Server :: "epoch"] #currEpoch
  }}}
    pb.Server__isEpochStale #s #epoch @ stk
  {{{
        RET #(negb (bool_decide (int.Z epoch = int.Z currEpoch)));
        s ↦[pb.Server :: "epoch"] #currEpoch
  }}}
.
Proof.
  iIntros (Φ) "HcurrEpoch HΦ".
  wp_call.
  wp_loadField.
  wp_pures.
  iModIntro.
  iSpecialize ("HΦ" with "HcurrEpoch").
  iExactEq "HΦ".
  repeat f_equal.
  apply bool_decide_ext.
  naive_solver.
Qed.

End pb_local_definitions.
