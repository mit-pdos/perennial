From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require mpaxos.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.mpaxos Require Export protocol_proof marshal_proof.
From Perennial.program_proof.reconnectclient Require Export proof.
From Perennial.program_proof.asyncfile Require Export proof.

Definition client_logR := dfrac_agreeR (leibnizO (list u8)).

Class mpG Σ := {
    mp_ghostG :> mp_ghostG (EntryType:=(list u8 * iProp Σ)%type) Σ ;
    mp_urpcG :> urpcregG Σ ;
    mp_wgG :> waitgroupG Σ ; (* for apply proof *)
    mp_logG :> inG Σ client_logR;
    mp_apply_escrow_tok :> ghost_varG Σ unit ;
    mp_asyncfile :> asyncfileG Σ ;
}.

Module mpaxosParams.
Class t Σ := {
    config: list mp_server_names ;
    Pwf : list u8 → iProp Σ ;
    N : namespace ;
  }
.
Global Instance mpaxos_to_protocol_params Σ :
  t Σ → protocol_params.t :=
  λ p, protocol_params.mk config (N .@ "protocol").

End mpaxosParams.

Import mpaxosParams.
Section global_definitions.
Context `{!gooseGlobalGS Σ}.
Context `{!mpG Σ}.
Context `{!mpaxosParams.t Σ}.

Definition own_state γ ς := own γ (to_dfrac_agree (DfracOwn (1/2)) (ς : (leibnizO (list u8)))).

(* RPC specs *)

Definition get_state (σ:list (list u8 * iProp Σ)) := default [] (last (fst <$> σ)).

Definition applyAsFollower_core_spec γ γsrv args σ (Φ : applyAsFollowerReply.C -> iProp Σ) : iProp Σ :=
  (
   "%Hstate" ∷ ⌜ args.(applyAsFollowerArgs.state) = get_state σ ⌝ ∗
   "%Hσ_index" ∷ ⌜ length σ = (int.nat args.(applyAsFollowerArgs.nextIndex))%nat ⌝ ∗
   "%Hghost_op_σ" ∷ ⌜ last σ.*1 = Some args.(applyAsFollowerArgs.state) ⌝ ∗
   "#HP" ∷ □ Pwf args.(applyAsFollowerArgs.state) ∗
   (* "%Hno_overflow" ∷ ⌜int.nat args.(applyAsFollowerArgs.nextIndex) < int.nat (word.add args.(applyAsFollowerArgs.nextIndex) 1) ⌝ ∗ *)
   "#Hprop" ∷ is_proposal γ args.(applyAsFollowerArgs.epoch) σ ∗
   "HΨ" ∷ ((is_accepted_lb γsrv args.(applyAsFollowerArgs.epoch) σ -∗ Φ (applyAsFollowerReply.mkC (U64 0))) ∧
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
  ⌜int.nat reply.(enterNewEpochReply.acceptedEpoch) < int.nat epoch⌝ ∗
  ⌜reply.(enterNewEpochReply.state) = get_state log⌝ ∗
  ⌜int.nat reply.(enterNewEpochReply.nextIndex) = length log⌝ ∗
  is_accepted_upper_bound γsrv log reply.(enterNewEpochReply.acceptedEpoch) epoch ∗
  is_proposal γ reply.(enterNewEpochReply.acceptedEpoch) log ∗
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

Definition is_state_inv γlog γsys :=
  inv appN (∃ log,
        own_state γlog (get_state log) ∗
        own_ghost γsys log ∗
        □(
          (* XXX: this is a bit different from pb_definitions.v *)
          (* This says that for all (log'prefix ++ [lastEnt]) ⪯ log,
             lastEnt.Q is true.
           *)
          ∀ log' log'prefix lastEnt, ⌜prefix log' log⌝ -∗
                ⌜log' = log'prefix ++ [lastEnt]⌝ -∗
                (* FIXME: use gnames and saved_pred insted of direct higher-order state *)
                lastEnt.2
        )
      ).

Definition becomeleader_core_spec :=
  λ (Φ : iPropO Σ), (Φ)%I
.

Program Definition becomeleader_spec :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  becomeleader_core_spec (∀ enc_reply, Φ enc_reply)%I
.
Next Obligation.
  unfold becomeleader_core_spec.
  solve_proper.
Defined.

(* End RPC specs *)

Definition is_mpaxos_host (host:u64) (γ:mp_system_names) (γsrv:mp_server_names) : iProp Σ :=
  "#Hdom" ∷ is_urpc_dom γsrv.(mp_urpc_gn) {[ (U64 0); (U64 1); (U64 2); (U64 2) ]} ∗
  "#H0" ∷ is_urpc_spec_pred γsrv.(mp_urpc_gn) host (U64 0) (applyAsFollower_spec γ γsrv) ∗
  "#H1" ∷ is_urpc_spec_pred γsrv.(mp_urpc_gn) host (U64 1) (enterNewEpoch_spec γ γsrv) ∗
  "#H2" ∷ is_urpc_spec_pred γsrv.(mp_urpc_gn) host (U64 2) (becomeleader_spec)
.

Global Instance is_mpaxos_host_pers host γ γsrv: Persistent (is_mpaxos_host host γ γsrv) := _.

End global_definitions.

Module paxosState.
Section paxosState.
Record t :=
  mk {
      epoch : u64;
      acceptedEpoch : u64 ;
      nextIndex : u64 ;
      state : list u8 ;
      isLeader : bool ;
    }.

Definition encode (st:t) : list u8.
Admitted.

#[global]
Instance encode_inj : Inj (=) (=) encode.
Proof. intros ???. Admitted.

Context `{!heapGS Σ}.
Definition own_vol (s:loc) (st: paxosState.t) : iProp Σ :=
  ∃ state_sl,
  "Hepoch" ∷ s ↦[paxosState :: "epoch"] #st.(epoch) ∗
  "HaccEpoch" ∷ s ↦[paxosState :: "acceptedEpoch"] #st.(acceptedEpoch) ∗
  "HnextIndex" ∷ s ↦[paxosState :: "nextIndex"] #st.(nextIndex) ∗
  "Hstate" ∷ s ↦[paxosState :: "state"] (slice_val state_sl) ∗
  "#Hstate_sl" ∷ readonly (own_slice_small state_sl byteT 1 st.(state)) ∗
  "HisLeader" ∷ s ↦[paxosState :: "isLeader"] #st.(isLeader)
.

Lemma wp_encode s st :
  {{{
        own_vol s st
  }}}
    encodePaxosState #s
  {{{
        sl, RET (slice_val sl);
        own_vol s st ∗
        own_slice sl byteT 1 (encode st)
  }}}
.
Proof.
Admitted.


Context `{!mpG Σ}.
Context `{!mpaxosParams.t Σ}.

Definition own_ghost γ γsrv (st:paxosState.t) : iProp Σ :=
  ∃ (log:list (list u8 * iProp Σ)),
  "Hghost" ∷ own_replica_ghost γ γsrv
           (mkMPaxosState st.(epoch) st.(acceptedEpoch) log) ∗
  "%Hlog" ∷ ⌜ length log = int.nat st.(nextIndex) ⌝ ∗
  "%Hlog" ∷ ⌜ default [] (last log.*1) = st.(state) ⌝ ∗
  "#Hinv" ∷ is_repl_inv γ ∗
  "#Hvote_inv" ∷ is_vote_inv γ ∗

  "HleaderOnly" ∷ (if st.(isLeader) then
                     own_leader_ghost γ (mkMPaxosState st.(epoch) st.(acceptedEpoch) log)
                   else True) ∗
  "%HnextIndex_nooverflow" ∷ ⌜ length log = int.nat (length log) ⌝ ∗
  "%HaccEpochEq" ∷ ⌜ if st.(isLeader) then st.(acceptedEpoch) = st.(epoch) else True ⌝
.

End paxosState.
End paxosState.

Section local_definitions.
Context `{!heapGS Σ}.
Context `{!mpG Σ}.
Context `{!mpaxosParams.t Σ}.

Definition is_singleClerk (ck:loc) γ γsrv : iProp Σ :=
  ∃ (cl:loc) srv,
  "#Hcl" ∷ readonly (ck ↦[mpaxos.singleClerk :: "cl"] #cl) ∗
  "#Hcl_rpc"  ∷ is_ReconnectingClient cl srv ∗
  "#Hsrv" ∷ is_mpaxos_host srv γ γsrv
.

(* End clerk specs *)

(* Server-side definitions *)

Definition fileN := N .@ "file".

Definition own_file_inv γ γsrv (data:list u8) : iProp Σ :=
  ∃ pst,
  "%Henc" ∷ ⌜ paxosState.encode pst = data ⌝ ∗
  "Hghost" ∷ paxosState.own_ghost γ γsrv pst
.

(* The P is a validity predicate for any proposed state *)
Definition own_Server (s:loc) γ γsrv : iProp Σ :=
  ∃ (f:loc) (ps:loc) pst γf,
  "Hps" ∷ s ↦[mpaxos.Server :: "ps"] #ps ∗
  "Hstorage" ∷ s ↦[mpaxos.Server :: "storage"] #f ∗
  "Hfile" ∷ own_AsyncFile fileN f γf (own_file_inv γ γsrv) (paxosState.encode pst) ∗
  "Hvol" ∷ paxosState.own_vol ps pst ∗
  "#HP" ∷ □ Pwf pst.(paxosState.state)
.

Definition is_Server (s:loc) γ γsrv : iProp Σ :=
  ∃ (mu:val) (clerks_sl:Slice.t) clerks,
  "#Hmu" ∷ readonly (s ↦[mpaxos.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock N mu (own_Server s γ γsrv) ∗

  "#Hclerks" ∷ readonly (s ↦[mpaxos.Server :: "clerks"] (slice_val clerks_sl)) ∗

  (* clerks *)
  "%Hconf_clerk_len" ∷ ⌜length clerks = length config⌝ ∗
  "#Hclerks_sl" ∷ readonly (own_slice_small clerks_sl ptrT 1 clerks) ∗
  "#Hclerks_rpc" ∷ ([∗ list] ck ; γsrv' ∈ clerks ; config, is_singleClerk ck γ γsrv')
.

End local_definitions.
