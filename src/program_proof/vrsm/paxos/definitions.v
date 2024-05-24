From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.vrsm Require paxos.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial Require Export paxos.protocol_proof paxos.marshal_proof.
From Perennial.program_proof.reconnectclient Require Export proof.
From Perennial.program_proof.asyncfile Require Export proof.
From Perennial.base_logic Require Import saved_prop.

Record paxos_system_names :=
  {
    s_st: gname ;
    s_mp : mp_system_names ;
    s_hosts: list mp_server_names ;
  }.

Definition paxos_server_names := mp_server_names.

Implicit Type γ : paxos_system_names.

Definition client_logR := dfrac_agreeR (leibnizO (list u8)).

Class paxosG Σ := {
    (* mp_ghostG :> mp_ghostG (EntryType:=(list u8 * iProp Σ)%type) Σ ; *)
    paxos_ghostG :> mpaxosG (EntryType:=(list u8 * gname)%type) Σ ;
    paxos_urpcG :> urpcregG Σ ;
    paxos_wgG :> waitgroupG Σ ; (* for apply proof *)
    paxos_logG :> inG Σ client_logR;
    paxos_apply_escrow_tok :> ghost_varG Σ unit ;
    paxos_asyncfile :> asyncfileG Σ ;
}.

Definition paxosΣ :=
  #[mpaxosΣ (EntryType:=(list u8 * gname)); savedPropΣ ; urpcregΣ ; waitgroupΣ ;
    GFunctor (client_logR) ; ghost_varΣ unit ;
    asyncfileΣ ;
    GFunctor dfracR
    ].
Global Instance subG_pbΣ {Σ} : subG (paxosΣ) Σ → (paxosG Σ).
Proof. solve_inG. Qed.

Module paxosParams.
Class t Σ := mk {
    initstate: list u8 ;
    Pwf : list u8 → iProp Σ ;
    N : namespace ;
  }
.

End paxosParams.

Import paxosParams.
Section global_definitions.
Context `{!gooseGlobalGS Σ}.
Context `{!paxosG Σ}.
Context `{!paxosParams.t Σ}.

Definition own_state γ ς := own γ.(s_st) (to_dfrac_agree (DfracOwn (1/2)) (ς : (leibnizO (list u8)))).

(* RPC specs *)

Definition get_state {A} (σ:list (list u8 * A)) := default initstate (last (fst <$> σ)).

Definition applyAsFollower_core_spec γ γsrv args σ (Φ : applyAsFollowerReply.C -> iProp Σ) : iProp Σ :=
  (
   "%Hstate" ∷ ⌜ args.(applyAsFollowerArgs.state) = get_state σ ⌝ ∗
   "%Hσ_index" ∷ ⌜ length σ = (uint.nat args.(applyAsFollowerArgs.nextIndex))%nat ⌝ ∗
   "%Hghost_op_σ" ∷ ⌜ last σ.*1 = Some args.(applyAsFollowerArgs.state) ⌝ ∗
   "#HP" ∷ □ Pwf args.(applyAsFollowerArgs.state) ∗
   (* "%Hno_overflow" ∷ ⌜uint.nat args.(applyAsFollowerArgs.nextIndex) < uint.nat (word.add args.(applyAsFollowerArgs.nextIndex) 1) ⌝ ∗ *)
   "#Hprop" ∷ is_proposal (config:=γ.(s_hosts)) (N:=N) γ.(s_mp) args.(applyAsFollowerArgs.epoch) σ ∗
   "HΨ" ∷ ((is_accepted_lb γsrv args.(applyAsFollowerArgs.epoch) σ -∗ Φ (applyAsFollowerReply.mkC (W64 0))) ∧
           (∀ (err:u64), ⌜err ≠ 0⌝ -∗ Φ (applyAsFollowerReply.mkC err)))
    )%I
.

Program Definition applyAsFollower_spec γ γsrv :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args σ,
    ⌜applyAsFollowerArgs.has_encoding encoded_args args⌝ ∗
    applyAsFollower_core_spec γ γsrv args σ (λ reply, ∀ enc_reply,
                                                ⌜applyAsFollowerReply.has_encoding enc_reply reply⌝ -∗ Φ enc_reply)
    )%I
.
Next Obligation.
  rewrite /applyAsFollower_core_spec.
  solve_proper.
Defined.

Definition enterNewEpoch_post γ γsrv reply (epoch:u64) : iProp Σ:=
 ∃ log,
  ⌜uint.nat reply.(enterNewEpochReply.acceptedEpoch) < uint.nat epoch⌝ ∗
  ⌜reply.(enterNewEpochReply.state) = get_state log⌝ ∗
  ⌜uint.nat reply.(enterNewEpochReply.nextIndex) = length log⌝ ∗
  is_accepted_upper_bound γsrv log reply.(enterNewEpochReply.acceptedEpoch) epoch ∗
  is_proposal (config:=γ.(s_hosts)) (N:=N) γ.(s_mp) reply.(enterNewEpochReply.acceptedEpoch) log ∗
  □ Pwf reply.(enterNewEpochReply.state) ∗
  own_vote_tok γsrv epoch
.

Definition enterNewEpoch_core_spec γ γsrv args (Φ : enterNewEpochReply.C -> iProp Σ) : iProp Σ :=
  (
   "HΦ" ∷ (∀ reply, enterNewEpoch_post γ γsrv reply args.(enterNewEpochArgs.epoch) -∗ Φ reply) ∧
           (∀ reply, ⌜reply.(enterNewEpochReply.err) ≠ 0⌝ -∗ Φ reply)
    )%I
.

Program Definition enterNewEpoch_spec γ γsrv :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args,
    ⌜enterNewEpochArgs.has_encoding encoded_args args⌝ ∗
    enterNewEpoch_core_spec γ γsrv args (λ reply, ∀ enc_reply,
                                                ⌜enterNewEpochReply.has_encoding enc_reply reply⌝ -∗ Φ enc_reply)
    )%I
.
Next Obligation.
  rewrite /enterNewEpoch_core_spec.
  solve_proper.
Defined.

Definition appN := N .@ "app".
Definition escrowN := N .@ "escrow".

Definition own_log' γ (opsfullQ : list ((list u8) * iProp Σ)) : iProp Σ :=
  ∃ ops_gnames: list ((list u8) * gname),
    own_log γ.(s_mp) ops_gnames ∗
    ⌜ opsfullQ.*1 = ops_gnames.*1 ⌝ ∗
    [∗ list] k↦Φ;γprop ∈ snd <$> opsfullQ; snd <$> ops_gnames, saved_prop_own γprop DfracDiscarded Φ.

Definition is_helping_inv γsys :=
  inv appN (∃ log,
        own_state γsys (get_state log) ∗
        own_log' γsys log ∗
        □(
          (* XXX: this is a bit different from pb_definitions.v *)
          (* This says that for all (log'prefix ++ [lastEnt]) ⪯ log,
             lastEnt.Q is true.
           *)
          ∀ log' log'prefix lastEnt, ⌜prefix log' log⌝ -∗
                ⌜log' = log'prefix ++ [lastEnt]⌝ -∗
                lastEnt.2
        )
      ).

Definition becomeLeader_core_spec :=
  λ (Φ : iPropO Σ), (Φ)%I
.

Program Definition becomeLeader_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  becomeLeader_core_spec (∀ enc_reply, Φ enc_reply)%I
.
Next Obligation.
  unfold becomeLeader_core_spec.
  solve_proper.
Defined.

(* End RPC specs *)

Definition is_paxos_host (host:u64) γ (γsrv:mp_server_names) : iProp Σ :=
  ∃ γrpc,
  "#Hdom" ∷ is_urpc_dom γrpc {[ (W64 0); (W64 1); (W64 2) ]} ∗
  "#H0" ∷ is_urpc_spec_pred γrpc host (W64 0) (applyAsFollower_spec γ γsrv) ∗
  "#H1" ∷ is_urpc_spec_pred γrpc host (W64 1) (enterNewEpoch_spec γ γsrv) ∗
  "#H2" ∷ is_urpc_spec_pred γrpc host (W64 2) (becomeLeader_spec)
.

Global Instance is_paxos_host_pers host γ γsrv: Persistent (is_paxos_host host γ γsrv) := _.

Definition own_paxosState_ghost γ γsrv (st:paxosState.t) : iProp Σ :=
  ∃ (log:list (list u8 * gname)),
  "Hghost" ∷ own_replica_ghost (config:=γ.(s_hosts)) (N:=N) γ.(s_mp) γsrv
           (mkMPaxosState st.(paxosState.epoch) st.(paxosState.acceptedEpoch) log) ∗
  "%HlogLen" ∷ ⌜ length log = uint.nat st.(paxosState.nextIndex) ⌝ ∗
  "%Hlog" ∷ ⌜ default initstate (last log.*1) = st.(paxosState.state) ⌝ ∗
  "#Hinv" ∷ is_repl_inv (config:=γ.(s_hosts)) (N:=N) γ.(s_mp) ∗
  "#Hvote_inv" ∷ is_vote_inv (config:=γ.(s_hosts)) (N:=N) γ.(s_mp) ∗
  "#Hpwf" ∷ (□ Pwf st.(paxosState.state)) ∗

  "HleaderOnly" ∷ (if st.(paxosState.isLeader) then
                     own_leader_ghost (config:=γ.(s_hosts)) (N:=N) γ.(s_mp) (mkMPaxosState st.(paxosState.epoch) st.(paxosState.acceptedEpoch) log)
                   else True) ∗
  "%HnextIndex_nooverflow" ∷ ⌜ length log = uint.nat (length log) ⌝ ∗
  "%HaccEpochEq" ∷ ⌜ if st.(paxosState.isLeader) then st.(paxosState.acceptedEpoch) = st.(paxosState.epoch) else True ⌝
.

Definition encodes_paxosState st data : Prop :=
  paxosState.encode st = data ∨ (data = [] ∧ st = paxosState.mk 0 0 0 initstate false)
.

Definition own_file_inv γ γsrv (data:list u8) : iProp Σ :=
  ∃ pst,
  "%Henc" ∷ ⌜ encodes_paxosState pst data ⌝ ∗
  "Hghost" ∷ own_paxosState_ghost γ γsrv pst
.

Definition is_paxos_server_host (host:u64) γ (γsrv:mp_server_names) : iProp Σ :=
  "Hhost" ∷ is_paxos_host host γ γsrv  ∗
  "Hinv" ∷ is_helping_inv γ.

Definition is_paxos_hosts hosts γ : iProp Σ :=
  "#Hhosts" ∷ ([∗ list] _ ↦ host ; γsrv' ∈ hosts ; γ.(s_hosts), is_paxos_host host γ γsrv')
.

End global_definitions.

Section local_definitions.
Context `{!heapGS Σ}.
Context `{!paxosG Σ}.
Context `{!paxosParams.t Σ}.

Definition is_singleClerk (ck:loc) γ γsrv : iProp Σ :=
  ∃ (cl:loc) srv,
  "#Hcl" ∷ readonly (ck ↦[singleClerk :: "cl"] #cl) ∗
  "#Hcl_rpc"  ∷ is_ReconnectingClient cl srv ∗
  "#Hsrv" ∷ is_paxos_host srv γ γsrv
.

(* End clerk specs *)

(* Server-side definitions *)

Definition fileN := N .@ "file".

(* The P is a validity predicate for any proposed state *)
Definition own_Server (s:loc) γ γsrv : iProp Σ :=
  ∃ (f:loc) (ps:loc) pst γf data,
  "Hps" ∷ s ↦[Server :: "ps"] #ps ∗
  "Hstorage" ∷ s ↦[Server :: "storage"] #f ∗
  "Hfile" ∷ own_AsyncFile fileN f γf (own_file_inv γ γsrv) data ∗
  "Hvol" ∷ paxosState.own_vol ps pst ∗
  "#HP" ∷ □ Pwf pst.(paxosState.state) ∗
  "%HencPaxos" ∷ ⌜ encodes_paxosState pst data ⌝
.

Definition is_Server (s:loc) γ γsrv : iProp Σ :=
  ∃ (mu:val) (clerks_sl:Slice.t) clerks,
  "#Hmu" ∷ readonly (s ↦[Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock N mu (own_Server s γ γsrv) ∗

  "#Hclerks" ∷ readonly (s ↦[Server :: "clerks"] (slice_val clerks_sl)) ∗

  (* clerks *)
  "#Hclerks_sl" ∷ readonly (own_slice_small clerks_sl ptrT (DfracOwn 1) clerks) ∗
  "#Hclerks_rpc" ∷ ([∗ list] ck ; γsrv' ∈ clerks ; γ.(s_hosts), is_singleClerk ck γ γsrv') ∗
  "#HhelpingInv" ∷ is_helping_inv γ
.

End local_definitions.
