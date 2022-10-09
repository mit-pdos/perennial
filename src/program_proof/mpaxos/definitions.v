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
    mp_compute_reply : list u8 → mp_OpType → list u8 ;
  }.

Context {mp_record:MPRecord}.
Notation OpType := (mp_OpType mp_record).
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

Program Definition ApplyAsBackup_spec γ γsrv :=
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

Definition is_Clerk (ck:loc) γ γsrv : iProp Σ :=
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
        (* ⌜has_op_encoding op_bytes op⌝ ∗ *)
        readonly (is_slice_small op_sl byteT 1 op_bytes) ∗
        readonly (is_slice_small state_sl byteT 1 state)
  }}}
    applyFn (slice_val state_sl) (slice_val op_sl)
  {{{
        newstate_sl (newstate:list u8) reply_sl,
        RET (slice_val newstate_sl, slice_val reply_sl);
        readonly (is_slice_small newstate_sl byteT 1 newstate) ∗
        readonly (is_slice_small reply_sl byteT 1 (compute_reply state op))
  }}}
.

(* Hides the ghost part of the log; this is suitable for exposing as part of
   interfaces for users of the library.
   . *)
Definition own_Server (s:loc) γ γsrv : iProp Σ :=
  ∃ st (sealed:bool) (isLeader:bool) (sm:loc) (clerks_sl:Slice.t)
    state_sl (state:list u8) applyFn clerks,
    let nextIndex := U64 (length st.(mp_log)) in
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
  "#Hclerks_rpc" ∷ ([∗ list] ck ; γsrv' ∈ clerks ; conf, is_Clerk ck γ γsrv') ∗

  (* applyFn callback spec *)
  "#HisApplyFn" ∷ is_applyFn applyFn ∗

  (* ghost-state *)
  "Hghost" ∷ own_replica_ghost conf γ γsrv st ∗

  (* leader-only *)
  "HprimaryOnly" ∷ if isLeader then own_leader_ghost conf γ γsrv st else True
.

Definition is_Server (s:loc) γ γsrv : iProp Σ :=
  ∃ (mu:val),
  "#Hmu" ∷ readonly (s ↦[mpaxos.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock mpN mu (own_Server s γ γsrv)
  (* "#Hsys_inv" ∷ sys_inv γ *).

Lemma wp_Server__apply_internal s γ γsrv (op:list u8) op_sl ghost_op reply_ptr init_reply:
  {{{
        is_Server s γ γsrv ∗
        readonly (is_slice_small op_sl byteT 1 op) ∗
        (|={⊤∖↑ghostN,∅}=> ∃ σ, own_ghost γ σ ∗ (own_ghost γ (σ ++ [ghost_op]) ={∅,⊤∖↑ghostN}=∗ True)) ∗
        applyReply.own reply_ptr init_reply 1
  }}}
    mpaxos.Server__apply #s (slice_val op_sl) #reply_ptr
  {{{
        reply, RET #reply_ptr; £ 1 ∗ £ 1 ∗ applyReply.own reply_ptr reply 1 ∗
        if (decide (reply.(applyReply.err) = 0%Z)) then
          ∃ σ,
            let σphys := (λ x, x.1) <$> σ in
            (* ⌜reply.(applyReply.ret) = compute_reply σphys ghost_op.1⌝ ∗ *)
            is_ghost_lb γ (σ ++ [ghost_op])
        else
          True
  }}}.
Proof.
  iIntros (Φ) "(#Hsrv & #Hop & Hupd & Hreply) HΦ".
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
  }
  iIntros (???) "[#Hnewstate_sl #Hreply_sl]".
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
  iIntros (args) "Hargs".

  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_pures.
  wp_loadField.

  wp_apply (release_spec with "[-HΦ]").
  {
    admit.
  }
Admitted.

End definitions.
