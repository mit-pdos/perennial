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
From Perennial.program_proof.grove_shared Require Import monotonic_pred.
From Perennial.base_logic Require Import lib.saved_spec.

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
    apply_postcond : list OpType → OpType → Prop ;
    (* need decision because we need to make an early case distinction based on this *)
    apply_postcond_dec : (∀ ops o, Decision (apply_postcond ops o)) ;
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
Notation apply_postcond := (Sm.apply_postcond pb_record).

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

(* FIXME: no new universe constraint introduced here *)
Definition bad1 γx : iProp Σ:=
  is_epoch_lb γx (U64 0).
Print Universes Subgraph (prod.u0 prod.u1 universes.Logic).

End pb_global_definitions.

Section pb_local_definitions.
(* definitions that refer to a particular node *)
Context {pb_record:Sm.t}.
Context `{!gooseGlobalGS Σ}.
Context `{!pbG (pb_record:=pb_record) Σ}.

(* FIXME: new universe constraint introduced here for some reason. *)
Print Universes Subgraph (prod.u0 prod.u1 universes.Logic).
Definition bad2 γx : iProp Σ:=
  is_epoch_lb γx (U64 0).
Print Universes Subgraph (prod.u0 prod.u1 universes.Logic).
Lemma test γx :
  bad1 γx = bad2 γx.
Proof. reflexivity. Qed.
Set Printing Universes.
End pb_local_definitions.
Set Printing All.
Print bad1.
Print bad2.
Print Coq.Init.Datatypes.
Print Universes.

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
        readonly (own_slice_small op_sl byteT 1 op_bytes) ∗
        (* XXX: This is the weakest mask that the pb library is compatible with.
           By making the mask weak, we allow for more possible implementations
           of startApplyFn, so we give a stronger spec to the client. The chain
           of callbacks had made it confusing which way is weaker and which way
           stronger.
         *)
        (⌜apply_postcond σ op⌝ -∗ P epoch σ false ={⊤∖↑pbAofN}=∗ P epoch (σ ++ [op]) false ∗ Q) ∗
        own_StateMachine epoch σ false P
  }}}
    startApplyFn (slice_val op_sl)
  {{{
        reply_sl q (waitFn:goose_lang.val),
        RET (slice_val reply_sl, waitFn);
        ⌜apply_postcond σ op⌝ ∗
        own_slice_small reply_sl byteT q (compute_reply σ op) ∗
        own_StateMachine epoch (σ ++ [op]) false P ∗
        (∀ Ψ, (Q -∗ Ψ #()) -∗ WP waitFn #() {{ Ψ }})
  }}}
.

Definition is_SetStateAndUnseal_fn own_StateMachine (set_state_fn:val) P : iProp Σ :=
  ∀ σ_prev (epoch_prev:u64) σ epoch (snap:list u8) snap_sl sealed Q,
  {{{
        ⌜ (length σ < 2 ^ 64)%Z ⌝ ∗
        ⌜has_snap_encoding snap σ⌝ ∗
        readonly (own_slice_small snap_sl byteT 1 snap) ∗
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
        readonly (own_slice_small snap_sl byteT 1 snap) ∗
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
        readonly (own_slice_small op_sl byteT 1 op_bytes) ∗
        own_StateMachine epoch σ sealed P
  }}}
    applyRoFn (slice_val op_sl)
  {{{
        reply_sl q (lastModifiedIndex:u64),
        RET (#lastModifiedIndex, slice_val reply_sl);
        ⌜int.nat lastModifiedIndex <= length σ ⌝ ∗
        ⌜∀ σ', prefix σ' σ → int.nat lastModifiedIndex <= length σ' →
               (compute_reply σ op = compute_reply σ' op)⌝ ∗
        own_slice_small reply_sl byteT q (compute_reply σ op) ∗
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

Print Universes.
Print Universes Subgraph (prod.u0 prod.u1 universes.Logic).
Set Printing Universes.
Set Typeclasses Debug Verbosity 2.
Set Debug "universes".
Definition is_Primary γx : iProp Σ:=
  is_epoch_lb γx (U64 0).
Print Universes Subgraph (prod.u0 prod.u1 universes.Logic).
Print Coq.Init.Datatypes.
Print Universes.


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
  "HopAppliedConds_map" ∷ own_map opAppliedConds_loc 1 opAppliedConds ∗

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
