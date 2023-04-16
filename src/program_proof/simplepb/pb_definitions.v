From Perennial.base_logic Require Import lib.saved_prop.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Export pb_protocol primary_protocol pb_preread_protocol renewable_lease.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb Require Import pb_marshal_proof fmlist_map.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.reconnectclient Require Import proof.
From RecordUpdate Require Import RecordSet.
From Perennial.program_proof.simplepb Require Import config_proof.
From Perennial.program_proof.aof Require Import proof.

(* State-machine record. An instance of Sm.t defines how to compute the reply
   for an op applied to some state and how to encode ops into bytes. *)
Module Sm.
Record t :=
  {
    OpType:Type ;
    OpType_EqDecision:EqDecision OpType;
    has_op_encoding : list u8 → OpType → Prop ;
    has_snap_encoding: list u8 → (list OpType) → Prop ;
    compute_reply : list OpType → OpType → list u8 ;
    is_readonly_op : OpType → Prop ;
  }.
End Sm.

(* FIXME: is there really no better way than prefixing all of the projections
   with something to make them unique?  *)
Record simplepb_system_names :=
  {
    s_log : gname ;
    s_internal_log : gname ;
    s_pb : pb_system_names ;
    s_prim : primary_system_names ;
    s_prelog : gname ;
    s_reads : gname ;
  }.

Record simplepb_server_names :=
  {
    r_pb : pb_server_names ;
    r_prim :primary_server_names ;
  }.

Implicit Type (γ : simplepb_system_names) (γsrv:simplepb_server_names).

Section pb_global_definitions.

Context {pb_record:Sm.t}.
Notation OpType := (pb_record.(Sm.OpType)).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).
Notation is_readonly_op := (Sm.is_readonly_op pb_record).

(* opsfull has all the ghost ops (RO and RW) in it as well as the gname for the
   Q for that op. get_rwops returns the RW ops only with the gnames removed.
   Generalizing it to an arbitrary extra type A instead of gname
   specifically, because sometimes we want to use get_rwops on a list that has
   an iProp predicate instead of the gname (see is_helping_inv). *)
Definition get_rwops {A} (opsfull:list (OpType * A)) : list OpType :=
  fst <$> opsfull.

Definition client_logR := mono_listR (leibnizO OpType).

Class pbG Σ := {
    (*
    pb_ghostG :> pb_ghostG (EntryType:=(OpType * (list OpType → iProp Σ))%type) Σ ;
     *)
    (* pb_ghostG :> pb_ghostG (EntryType:=(OpType * gname)) Σ ; *)
    pb_prereadG :> pb_prereadG (EntryType:=(OpType * gname)) Σ ;
    pb_primaryG :> primary_ghostG (EntryType:=(OpType * gname)) Σ ;
    pb_savedG :> savedPredG Σ (list OpType);
    pb_configG :> configG Σ ;
    (* pb_urpcG :> urpcregG Σ ; *)
    pb_wgG :> waitgroupG Σ ; (* for apply proof *)
    pb_logG :> inG Σ client_logR;
    pb_apply_escrow_tok :> ghost_varG Σ unit ;
    pb_prophread_escrow :> inG Σ dfracR ;
}.

Definition pbΣ :=
  #[pb_ghostΣ (EntryType:=(OpType * gname)); savedPredΣ (list OpType) ; urpcregΣ ; waitgroupΣ ;
    GFunctor (client_logR) ; ghost_varΣ unit ;
    pb_prereadΣ (EntryType:=(OpType * gname));
    primary_ghostΣ (EntryType:=(OpType * gname)) ;
    configΣ ;
    GFunctor dfracR
    ].
Global Instance subG_pbΣ {Σ} : subG (pbΣ) Σ → (pbG Σ).
Proof. solve_inG. Qed.

Context `{!gooseGlobalGS Σ}.
Context `{!pbG Σ}.

(* This is the log of RW operations, exposed to the client of this library. *)
Definition own_op_log γ σ := own γ.(s_log) (●ML{#1/2} (σ : list (leibnizO OpType))).

Definition own_int_log γ σ := own γ.(s_internal_log) (●ML{#1/2} (σ : list (leibnizO OpType))).

(* RPC specs *)

Definition ApplyAsBackup_core_spec γ γsrv args opsfull op Q (Φ : u64 -> iProp Σ) : iProp Σ :=
  ("%Hσ_index" ∷ ⌜length (get_rwops opsfull) = (int.nat args.(ApplyAsBackupArgs.index) + 1)%nat⌝ ∗
   "%Hhas_encoding" ∷ ⌜has_op_encoding args.(ApplyAsBackupArgs.op) op⌝ ∗
   "%Hghost_op_σ" ∷ ⌜last opsfull = Some (op, Q)⌝ ∗
   "%Hno_overflow" ∷ ⌜int.nat args.(ApplyAsBackupArgs.index) < int.nat (word.add args.(ApplyAsBackupArgs.index) 1)⌝ ∗
   "#Hepoch_lb" ∷ is_epoch_lb γsrv.(r_pb) args.(ApplyAsBackupArgs.epoch) ∗
   "#Hprop_lb" ∷ is_proposal_lb γ.(s_pb) args.(ApplyAsBackupArgs.epoch) opsfull ∗
   "#Hprop_facts" ∷ is_proposal_facts γ.(s_pb) args.(ApplyAsBackupArgs.epoch) opsfull ∗
   "#Hprim_facts" ∷ is_proposal_facts_prim γ.(s_prim) args.(ApplyAsBackupArgs.epoch) opsfull ∗
   "HΨ" ∷ ((is_accepted_lb γsrv.(r_pb) args.(ApplyAsBackupArgs.epoch) opsfull -∗ Φ (U64 0)) ∧
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

Definition is_in_config γ γsrv epoch : iProp Σ :=
  ∃ confγ, is_epoch_config_proposal γ.(s_pb) epoch confγ ∗ ⌜γsrv.(r_pb) ∈ confγ⌝
.

Definition SetState_core_spec γ γsrv args opsfull :=
  λ (Φ : u64 -> iPropO Σ) ,
  (
    ⌜has_snap_encoding args.(SetStateArgs.state) (get_rwops opsfull)⌝ ∗
    ⌜length (get_rwops opsfull) = int.nat args.(SetStateArgs.nextIndex)⌝ ∗
    is_proposal_lb γ.(s_pb) args.(SetStateArgs.epoch) opsfull ∗
    is_proposal_facts γ.(s_pb) args.(SetStateArgs.epoch) opsfull ∗
    is_proposal_facts_prim γ.(s_prim) args.(SetStateArgs.epoch) opsfull ∗
    is_in_config γ γsrv args.(SetStateArgs.epoch) ∗
    (
      (is_epoch_lb γsrv.(r_pb) args.(SetStateArgs.epoch) -∗
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
    (is_epoch_lb γsrv.(r_pb) ghost_epoch_lb ∗
      (
      (∀ epochacc opsfull snap,
            ⌜int.nat ghost_epoch_lb ≤ int.nat epochacc⌝ -∗
            ⌜int.nat epochacc ≤ int.nat epoch⌝ -∗
            is_accepted_ro γsrv.(r_pb) epochacc opsfull -∗
            is_proposal_facts γ.(s_pb) epochacc opsfull -∗
            is_proposal_facts_prim γ.(s_prim) epochacc opsfull -∗
            is_proposal_lb γ.(s_pb) epochacc opsfull -∗
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

Definition BecomePrimary_core_spec γ γsrv args σ backupγ (ρ:u64 -d> simplepb_system_names -d> simplepb_server_names -d> iPropO Σ) :=
  λ (Φ : u64 -> iPropO Σ) ,
  (
    is_epoch_lb γsrv.(r_pb) args.(BecomePrimaryArgs.epoch) ∗
    is_epoch_config γ.(s_pb) args.(BecomePrimaryArgs.epoch) (r_pb <$> (γsrv :: backupγ)) ∗
    ([∗ list] host ; γsrv' ∈ args.(BecomePrimaryArgs.replicas) ; γsrv :: backupγ,
     (ρ host γ γsrv') ∗ is_epoch_lb γsrv'.(r_pb) args.(BecomePrimaryArgs.epoch)) ∗
    is_proposal_facts_prim γ.(s_prim) args.(BecomePrimaryArgs.epoch) σ ∗
    become_primary_escrow γ.(s_prim) γsrv.(r_prim) args.(BecomePrimaryArgs.epoch) σ (own_primary_ghost γ.(s_pb) args.(BecomePrimaryArgs.epoch) σ) ∗
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

Definition Apply_core_spec γ op enc_op :=
  λ (Φ : ApplyReply.C -> iPropO Σ) ,
  (
  ⌜has_op_encoding enc_op op⌝ ∗
  (* is_helping_inv γ.(s_log) γ.(s_prim) ∗ *)
  □(|={⊤∖↑pbN,∅}=> ∃ σ, own_int_log γ σ ∗ (own_int_log γ (σ ++ [op]) ={∅,⊤∖↑pbN}=∗
            Φ (ApplyReply.mkC 0 (compute_reply σ op))
  )) ∗
  □(∀ (err:u64) ret, ⌜err ≠ 0⌝ -∗ Φ (ApplyReply.mkC err ret))
  )%I
.

Program Definition Apply_spec γ :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ op, Apply_core_spec γ op enc_args
                      (λ reply, ∀ enc_reply, ⌜ApplyReply.has_encoding enc_reply reply⌝ -∗ Φ enc_reply)
  )%I
.
Next Obligation.
  unfold Apply_core_spec.
  solve_proper.
Defined.

Definition ApplyRo_core_spec γ  op enc_op :=
  λ (Φ : ApplyReply.C -> iPropO Σ) ,
  (
  ⌜has_op_encoding enc_op op⌝ ∗
  ⌜is_readonly_op op⌝ ∗
  □(|={⊤∖↑pbN,∅}=> ∃ σ, own_int_log γ σ ∗ (own_int_log γ σ ={∅,⊤∖↑pbN}=∗
            □ Φ (ApplyReply.mkC 0 (compute_reply σ op))
   (* XXX: the □Φ is OK because this is read-only. Technically, we could prove
      a stronger spec without the box, but we'll end up using prophecy anyways
      so it won't likely matter. *)
  )) ∗
  □(∀ (err:u64) ret, ⌜err ≠ 0⌝ -∗ Φ (ApplyReply.mkC err ret))
  )%I
.

Program Definition ApplyRo_spec γ :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ op, ApplyRo_core_spec γ op enc_args
                      (λ reply, ∀ enc_reply, ⌜ApplyReply.has_encoding enc_reply reply⌝ -∗ Φ enc_reply)
  )%I
.
Next Obligation.
  unfold ApplyRo_core_spec.
  solve_proper.
Defined.

Definition committed_log_fact γ (epoch:u64) ops_commit_full : iProp Σ :=
  (∀ σ' epoch', ⌜int.nat epoch <= int.nat epoch'⌝ -∗
                ⌜length ops_commit_full <= length σ' ∨ int.nat epoch < int.nat epoch'⌝ -∗
                is_proposal_lb γ.(s_pb) epoch' σ' -∗
                is_proposal_facts γ.(s_pb) epoch' σ' -∗
                ⌜prefix ops_commit_full σ'⌝)
.


Definition IncreaseCommit_core_spec γ γsrv (newCommitIndex:u64)  :=
  λ (Φ : iPropO Σ) ,
  ( ∃ σ epoch,
    ⌜int.nat newCommitIndex = length σ⌝ ∗
    is_epoch_lb γsrv.(r_pb) epoch ∗
    is_pb_log_lb γ.(s_pb) σ ∗
    is_proposal_lb γ.(s_pb) epoch σ ∗
    □ committed_log_fact γ epoch σ ∗
    Φ
  )%I
.

Program Definition IncreaseCommit_spec γ γsrv :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ newCommitIndex,
    ⌜enc_args = u64_le newCommitIndex⌝ ∗
    IncreaseCommit_core_spec γ γsrv newCommitIndex (Φ [])
  )%I
.
Next Obligation.
  unfold IncreaseCommit_core_spec.
  solve_proper.
Defined.

Definition is_pb_host_pre ρ : (u64 -d> simplepb_system_names -d> simplepb_server_names -d> iPropO Σ) :=
  (λ host γ γsrv,
  ∃ γrpc,
  handler_spec γrpc host (U64 0) (ApplyAsBackup_spec γ γsrv) ∗
  handler_spec γrpc host (U64 1) (SetState_spec γ γsrv) ∗
  handler_spec γrpc host (U64 2) (GetState_spec γ γsrv) ∗
  handler_spec γrpc host (U64 3) (BecomePrimary_spec_pre γ γsrv ρ) ∗
  handler_spec γrpc host (U64 4) (Apply_spec γ) ∗
  handler_spec γrpc host (U64 6) (ApplyRo_spec γ) ∗
  handler_spec γrpc host (U64 7) (IncreaseCommit_spec γ γsrv) ∗
  handlers_dom γrpc {[ (U64 0) ; (U64 1) ; (U64 2) ; (U64 3) ; (U64 4) ; (U64 6) ; (U64 7) ]})%I
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

(* Begin config client-side protocol. *)
Definition is_conf_inv γ γconf : iProp Σ :=
  inv configN (∃ epoch conf confγs epoch_lb,
      "Hepoch" ∷ own_latest_epoch γconf epoch ∗
      "Hconf" ∷ own_config γconf conf ∗
      "#His_conf" ∷ is_epoch_config γ.(s_pb) epoch_lb (r_pb <$> confγs) ∗
      "#His_hosts" ∷ ([∗ list] γsrv ; host ∈ confγs ; conf, is_pb_host host γ γsrv) ∗
      "#His_lbs" ∷ (∀ (γsrv:pb_server_names), ⌜γsrv ∈ r_pb <$> confγs⌝ → is_epoch_lb γsrv epoch_lb) ∗
      "Hunused" ∷ ([∗ set] epoch' ∈ (fin_to_set u64), ⌜int.nat epoch < int.nat epoch'⌝ → config_proposal_unset γ.(s_pb) epoch' ∗ config_unset γ.(s_pb) epoch' ∗ own_proposal_unused γ.(s_pb) epoch' ∗ own_init_proposal_unused γ.(s_prim) epoch') ∗
      "Hunset_or_set" ∷ (config_unset γ.(s_pb) epoch ∨ ⌜int.nat epoch_lb = int.nat epoch⌝) ∗
      "#His_skip" ∷ (∀ epoch_skip, ⌜int.nat epoch_lb < int.nat epoch_skip⌝ → ⌜int.nat epoch_skip < int.nat epoch⌝ → is_epoch_skipped γ.(s_pb) epoch_skip)
      )
.
(* End config client-side protocol. *)

(* Encapsulates the protocol-level ghost resources of a replica server; this is
   suitable for exposing as part of interfaces for users of the library. For
   now, it's only part of the crash obligation. *)
(* should not be unfolded in proof *)
Definition own_Server_ghost_f γ γsrv epoch ops sealed : iProp Σ :=
  ∃ opsfull,
  "%Hre" ∷ ⌜ops = get_rwops opsfull⌝ ∗
  "Hghost" ∷ (own_replica_ghost γ.(s_pb) γsrv.(r_pb) epoch opsfull sealed) ∗
  "Hprim_escrow" ∷ own_primary_escrow_ghost γsrv.(r_prim) epoch ∗
  "#Hprim_facts" ∷ is_proposal_facts_prim γ.(s_prim) epoch opsfull ∗
  "#Hin_conf" ∷ is_in_config γ γsrv epoch
.

Definition escrowN := pbN .@ "escrow".
Definition appN := pbN .@ "app".
Definition own_ghost_log' γ (opsfullQ : list (OpType * (list OpType → iProp Σ))) : iProp Σ :=
  ∃ ops_gnames: list (OpType * gname),
    own_pre_log γ.(s_prelog) ops_gnames ∗
    ⌜opsfullQ.*1 = ops_gnames.*1 ⌝ ∗
    [∗ list] k↦Φ;γprop ∈ snd <$> opsfullQ; snd <$> ops_gnames, saved_pred_own γprop DfracDiscarded Φ.

Definition is_helping_inv γ :=
  inv appN (∃ opsfullQ,
      own_ghost_log' γ opsfullQ ∗
      own_int_log γ (get_rwops opsfullQ) ∗
      □(
        ∀ opsPre opsPrePre lastEnt,
        ⌜prefix opsPre opsfullQ⌝ -∗ ⌜opsPre = opsPrePre ++ [lastEnt]⌝ -∗
        (lastEnt.2 (get_rwops opsPrePre))
      )
      ).

(* These are the server-side invs that must be al *)
Definition is_pb_system_invs γsys : iProp Σ :=
  "#Hsys" ∷ is_repl_inv γsys.(s_pb) ∗
  "#Hhelping" ∷ is_helping_inv γsys ∗
  "#HpreInv" ∷ is_preread_inv γsys.(s_pb) γsys.(s_prelog) γsys.(s_reads)
.

End pb_global_definitions.

Module server.
Record t {pb_record:Sm.t} :=
  mkC {
    epoch : u64 ;
    sealed : bool ;
    ops_full_eph: list (pb_record.(Sm.OpType) * gname) ;
    isPrimary : bool ;
    canBecomePrimary : bool ;

    (* read-only optimization-related *)
    committedNextIndex : u64 ;
    leaseValid : bool;
    leaseExpiration : u64 ;
  }.

Global Instance etaServer {pb_record:Sm.t} : Settable _ :=
  settable! (mkC pb_record) <epoch; sealed; ops_full_eph; isPrimary;
        canBecomePrimary; committedNextIndex; leaseValid; leaseExpiration>.
End server.

Section pb_local_definitions.
(* definitions that refer to a particular node *)

Context {pb_record:Sm.t}.
Notation OpType := (pb_record.(Sm.OpType)).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).
Notation is_readonly_op := (Sm.is_readonly_op pb_record).

Notation pbG := (pbG (pb_record:=pb_record)).
Notation "server.t" := (server.t (pb_record:=pb_record)).

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

Definition pbAofN := pbN .@ "pbAofN".
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
        (P epoch σ false ={⊤∖↑pbAofN}=∗ P epoch (σ ++ [op]) false ∗ Q) ∗
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
        (P epoch_prev σ_prev sealed ={⊤∖↑pbAofN}=∗ P epoch σ false ∗ Q) ∗
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
        (P epoch σ sealed ={⊤∖↑pbAofN}=∗ P epoch σ true ∗ Q)
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

Definition is_ApplyReadonlyFn own_StateMachine (applyRoFn:val) (P:u64 → list (OpType) → bool → iProp Σ) : iProp Σ :=
  ∀ op_sl (epoch:u64) (σ:list OpType) (op_bytes:list u8) (op:OpType) (sealed:bool),
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        ⌜is_readonly_op op⌝ ∗
        readonly (is_slice_small op_sl byteT 1 op_bytes) ∗
        own_StateMachine epoch σ sealed P
  }}}
    applyRoFn (slice_val op_sl)
  {{{
        reply_sl q (lastModifiedIndex:u64),
        RET (#lastModifiedIndex, slice_val reply_sl);
        ⌜int.nat lastModifiedIndex <= length σ ⌝ ∗
        ⌜∀ σ', prefix σ' σ → int.nat lastModifiedIndex <= length σ' →
               (compute_reply σ op = compute_reply σ' op)⌝ ∗
        is_slice_small reply_sl byteT q (compute_reply σ op) ∗
        own_StateMachine epoch σ sealed P
  }}}
.

Definition accessP_fact own_StateMachine P : iProp Σ :=
  □ (£ 1 -∗ (∀ Φ σ epoch sealed,
     (∀ σold sealedold,
       ⌜prefix σold σ⌝ -∗ P epoch σold sealedold ={⊤∖↑pbAofN}=∗ P epoch σold sealedold ∗ Φ) -∗
  own_StateMachine epoch σ sealed P -∗ |NC={⊤}=>
  own_StateMachine epoch σ sealed P ∗ Φ))
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

Notation get_rwops := (get_rwops (pb_record:=pb_record)).

(* this is meant to be unfolded in the code proof *)
Definition is_Primary γ γsrv (s:server.t) clerks_sl : iProp Σ:=
  ∃ (clerkss:list Slice.t) backups,
  "%Hclerkss_len" ∷ ⌜length clerkss = numClerks⌝ ∗
  "#Hconf" ∷ is_epoch_config γ.(s_pb) s.(server.epoch) (r_pb <$> (γsrv :: backups)) ∗
            (* FIXME: ptrT vs refT (struct.t Clerk) *)
  "#Hclerkss_sl" ∷ readonly (is_slice_small clerks_sl (slice.T ptrT) 1 clerkss) ∗
  "#Hclerkss_rpc" ∷ ([∗ list] clerks_sl ∈ clerkss,
                        ∃ clerks,
                        "#Hclerks_sl" ∷ readonly (is_slice_small clerks_sl ptrT 1 clerks) ∗
                        "%Hclerks_conf" ∷ ⌜length clerks = length backups⌝ ∗
                        "#Hclerks_rpc" ∷ ([∗ list] ck ; γsrv' ∈ clerks ; backups, is_Clerk ck γ γsrv' ∗ is_epoch_lb γsrv'.(r_pb) s.(server.epoch))
                    )
.

Definition no_overflow (x:nat) : Prop := int.nat (U64 x) = x.
Hint Unfold no_overflow : arith.

(* physical (volatile) state; meant to be unfolded in code proof *)
Definition own_Server (s:loc) (st:server.t) γ γsrv mu : iProp Σ :=
  ∃ own_StateMachine (sm:loc) clerks_sl
    (committedNextIndex_cond isPrimary_cond:loc) (opAppliedConds_loc:loc) (opAppliedConds:gmap u64 loc),
  (* non-persistent physical *)
  "Hepoch" ∷ s ↦[pb.Server :: "epoch"] #st.(server.epoch) ∗
  "HnextIndex" ∷ s ↦[pb.Server :: "nextIndex"] #(U64 (length (get_rwops st.(server.ops_full_eph)))) ∗
  "HisPrimary" ∷ s ↦[pb.Server :: "isPrimary"] #st.(server.isPrimary) ∗
  "HcanBecomePrimary" ∷ s ↦[pb.Server :: "canBecomePrimary"] #st.(server.canBecomePrimary) ∗
  "Hsealed" ∷ s ↦[pb.Server :: "sealed"] #st.(server.sealed) ∗
  "Hsm" ∷ s ↦[pb.Server :: "sm"] #sm ∗
  "Hclerks" ∷ s ↦[pb.Server :: "clerks"] (slice_val clerks_sl) ∗
  "HcommittedNextIndex" ∷ s ↦[pb.Server :: "committedNextIndex"] #st.(server.committedNextIndex) ∗
  "HcommittedNextIndex_cond" ∷ s ↦[pb.Server :: "committedNextIndex_cond"] #committedNextIndex_cond ∗
  "HisPrimary_cond" ∷ s ↦[pb.Server :: "isPrimary_cond"] #isPrimary_cond ∗
  "HleaseValid" ∷ s ↦[pb.Server :: "leaseValid"] #st.(server.leaseValid) ∗
  "HleaseExpiration" ∷ s ↦[pb.Server :: "leaseExpiration"] #st.(server.leaseExpiration) ∗
  (* backup sequencer *)
  "HopAppliedConds" ∷ s ↦[pb.Server :: "opAppliedConds"] #opAppliedConds_loc ∗
  "HopAppliedConds_map" ∷ is_map opAppliedConds_loc 1 opAppliedConds ∗

  (* ownership of the statemachine *)
  "Hstate" ∷ own_StateMachine st.(server.epoch) (get_rwops st.(server.ops_full_eph)) st.(server.sealed) (own_Server_ghost_f γ γsrv) ∗

  (* persistent physical state *)
  "#HopAppliedConds_conds" ∷ ([∗ map] i ↦ cond ∈ opAppliedConds, is_cond cond mu) ∗
  "#HcommittedNextIndex_is_cond" ∷ is_cond committedNextIndex_cond mu ∗
  "#HisPrimary_is_cond" ∷ is_cond isPrimary_cond mu ∗

  (* witnesses for primary; the exclusive state is in own_Server_ghost *)
  "#Hprimary" ∷ (⌜st.(server.isPrimary) = false⌝ ∨ is_Primary γ γsrv st clerks_sl) ∗

  (* state-machine callback specs *)
  "#HisSm" ∷ is_StateMachine sm own_StateMachine (own_Server_ghost_f γ γsrv) ∗

  (* overflow *)
  "%HnextIndexNoOverflow" ∷ ⌜no_overflow (length (get_rwops (st.(server.ops_full_eph))))⌝
.

Definition is_Server_lease_resource γ (epoch:u64) (leaseValid:bool) (leaseExpiration:u64) : iProp Σ :=
  "#HprereadInv" ∷ is_preread_inv γ.(s_pb) γ.(s_prelog) γ.(s_reads) ∗
  "#Hlease" ∷ □(if leaseValid then
                ∃ γl γconf,
                is_conf_inv γ γconf ∗
                is_lease config_proof.epochLeaseN γl (own_latest_epoch γconf epoch) ∗
                is_lease_valid_lb γl leaseExpiration
              else
                True)
.

(* this should never be unfolded in the proof of code *)
Definition own_Primary_ghost_f γ γsrv (canBecomePrimary isPrimary:bool) epoch (committedNextIndex:u64) opsfull : iProp Σ:=
  tc_opaque (
            "Htok" ∷ (if canBecomePrimary then own_tok γsrv.(r_prim) epoch else True) ∗
            "#Hprim_facts" ∷ is_proposal_facts_prim γ.(s_prim) epoch opsfull  ∗

            "Hprim" ∷ if isPrimary then
              own_primary_ghost γ.(s_pb) epoch opsfull
            else
              True
      )%I
.

(* should not be unfolded in proof *)
Definition own_Server_ghost_eph_f (st:server.t) γ γsrv: iProp Σ :=
  tc_opaque (
  let ops:=(get_rwops st.(server.ops_full_eph)) in
   ∃ (ops_commit_full:list (OpType * gname)),
  "Hprimary" ∷ own_Primary_ghost_f γ γsrv st.(server.canBecomePrimary) st.(server.isPrimary) st.(server.epoch) st.(server.committedNextIndex) st.(server.ops_full_eph) ∗
  (* epoch lower bound *)
  "#Hs_epoch_lb" ∷ is_epoch_lb γsrv.(r_pb) st.(server.epoch) ∗


  "#Hs_prop_lb" ∷ is_proposal_lb γ.(s_pb) st.(server.epoch) st.(server.ops_full_eph) ∗
  "#Hs_prop_facts" ∷ is_proposal_facts γ.(s_pb) st.(server.epoch) st.(server.ops_full_eph) ∗
  "#Hlease" ∷ is_Server_lease_resource γ st.(server.epoch) st.(server.leaseValid) st.(server.leaseExpiration) ∗

  "#Hin_conf" ∷ is_in_config γ γsrv st.(server.epoch) ∗

  (* witness for committed state *)
  "#Hcommit_lb" ∷ is_pb_log_lb γ.(s_pb) ops_commit_full ∗
  "#Hcommit_fact" ∷ □ committed_log_fact γ st.(server.epoch) ops_commit_full ∗
  "#Hcommit_prop_lb" ∷ is_proposal_lb γ.(s_pb) st.(server.epoch) ops_commit_full ∗
  "%HcommitLen" ∷ ⌜length (get_rwops ops_commit_full) = int.nat st.(server.committedNextIndex)⌝
  )%I
.

Definition mu_inv (s:loc) γ γsrv mu: iProp Σ :=
  ∃ st,
  "Hvol" ∷ own_Server s st γ γsrv mu ∗
  "HghostEph" ∷ own_Server_ghost_eph_f st γ γsrv
.

Definition is_Server (s:loc) γ γsrv : iProp Σ :=
  ∃ (mu:val) (confCk:loc) γconf,
  "#Hmu" ∷ readonly (s ↦[pb.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock pbN mu (mu_inv s γ γsrv mu) ∗
  "#His_repl_inv" ∷ is_repl_inv γ.(s_pb) ∗
  "#HconfCk" ∷ readonly (s ↦[pb.Server :: "confCk"] #confCk) ∗
  "#Hconf_inv" ∷ is_conf_inv γ γconf ∗
  "#HconfCk_is" ∷ config_proof.is_Clerk confCk γconf ∗
  "#HhelpingInv" ∷ is_helping_inv γ ∗
  "#HprereadInv" ∷ is_preread_inv γ.(s_pb) γ.(s_prelog) γ.(s_reads)
.

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
