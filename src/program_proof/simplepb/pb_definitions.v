From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.simplepb Require Export pb_ghost.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb Require Import pb_marshal_proof.

Section pb_definitions.

Record PBRecord :=
  {
    pb_OpType:Type ;
    pb_has_op_encoding : list u8 → pb_OpType → Prop ;
    pb_has_snap_encoding: list u8 → u64 → (list pb_OpType) → Prop ;
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

(* End RPC specs *)

Definition is_pb_host γ γsrv (host:chan) :=
  handler_spec γsrv.(urpc_gn) host (U64 0) (ApplyAsBackup_spec γ γsrv).

Definition is_Clerk (ck:loc) γ γsrv : iProp Σ :=
  ∃ (cl:loc) srv,
  "#Hcl" ∷ readonly (ck ↦[pb.Clerk :: "cl"] #cl) ∗
  "#Hcl_rpc"  ∷ is_uRPCClient cl srv ∗
  "#Hsrv" ∷ is_pb_host γ γsrv srv
.

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

(* Server-side definitions *)

(* StateMachine *)
Definition is_ApplyFn (applyFn:val) (P:u64 → list (OpType) → bool → iProp Σ) Pcrash : iProp Σ :=
  ∀ op_sl (epoch:u64) (σ:list OpType) sealed (op_bytes:list u8) (op:OpType) Q R1 R2 Rcrash,
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        (R1 ={↑pbN}=∗ R2 ∗ Q) ∗
        □(R2 -∗ Rcrash epoch (σ++[op]) sealed) ∗
        crash_borrow (R1 ∗ P epoch σ sealed)
            (∃ (epoch':u64) (σ':list OpType) sealed, (Rcrash epoch' σ' sealed ∗ Pcrash epoch' σ' sealed)) ∗
        readonly (is_slice_small op_sl byteT 1 op_bytes)
  }}}
    applyFn (slice_val op_sl)
  {{{
        reply_sl,
        RET (slice_val reply_sl);
        crash_borrow (R2 ∗ P epoch (σ ++ [op]) sealed)
            (∃ epoch' σ' sealed, (Rcrash epoch' σ' sealed ∗ Pcrash epoch' σ' sealed)) ∗
        is_slice reply_sl byteT 1 (compute_reply σ op) ∗
        Q
  }}}
.

Definition is_SetState_fn (set_state_fn:val) P Pcrash : iProp Σ :=
  ∀ σ_prev (epoch_prev:u64) σ epoch (snap:list u8) snap_sl R1 R2 Rcrash,
  {{{
        ⌜has_snap_encoding snap epoch σ⌝ ∗
        is_slice snap_sl byteT 1 snap ∗
        (R1 ={↑pbN}=∗ R2) ∗
        □(R2 -∗ ∃ epoch σ, Rcrash epoch σ) ∗
        crash_borrow (R1 ∗ P epoch_prev σ_prev) (
          ∃ (epoch':u64) (σ':list OpType), (Rcrash epoch' σ' ∗ Pcrash epoch' σ')
        )
  }}}
    set_state_fn (slice_val snap_sl) #epoch
  {{{
        RET #();
        crash_borrow (R2 ∗ P epoch σ) (
          ∃ epoch' σ', (Rcrash epoch' σ' ∗ Pcrash epoch' σ')
        )
  }}}
.

Definition is_GetState_fn (get_state_fn:val) P Pcrash : iProp Σ :=
  ∀ σ epoch R Rcrash,
  {{{
        crash_borrow (R ∗ P epoch σ) (
          ∃ (epoch':u64) (σ':list OpType), (Rcrash epoch' σ' ∗ Pcrash epoch' σ')
        )
  }}}
    get_state_fn #()
  {{{
        snap_sl snap,
        RET (slice_val snap_sl);
        ⌜has_snap_encoding snap epoch σ⌝ ∗
        crash_borrow (R ∗ P epoch σ) (
          ∃ epoch' σ', (Rcrash epoch' σ' ∗ Pcrash epoch' σ')
        )
  }}}
.

Definition is_StateMachine (sm:loc) P Pcrash : iProp Σ :=
  ∃ (applyFn:val),
  "#Happly" ∷ readonly (sm ↦[pb.StateMachine :: "Apply"] applyFn) ∗
  "#HapplySpec" ∷ is_ApplyFn applyFn P Pcrash
.

(* Hides the ghost part of the log; this is suitable for exposing as part of
   interfaces for users of the library. For now, it's only part of the crash
   obligation. *)
Definition own_Server_ghost γ γsrv epoch σphys sealed : iProp Σ :=
  ∃ σ, ⌜σphys = σ.*1⌝ ∗ (own_replica_ghost γ γsrv epoch σ sealed)
.

Definition own_Server (s:loc) γ γsrv P Pcrash: iProp Σ :=
  ∃ (epoch:u64) σg (nextIndex:u64) (sealed:bool) (isPrimary:bool) (sm:loc) (clerks_sl:Slice.t),
  (* physical *)
  "Hepoch" ∷ s ↦[pb.Server :: "epoch"] #epoch ∗
  "HnextIndex" ∷ s ↦[pb.Server :: "nextIndex"] #nextIndex ∗
  "HisPrimary" ∷ s ↦[pb.Server :: "isPrimary"] #isPrimary ∗
  "Hsealed" ∷ s ↦[pb.Server :: "sealed"] #sealed ∗
  "Hsm" ∷ s ↦[pb.Server :: "sm"] #sm ∗
  "Hclerks" ∷ s ↦[pb.Server :: "clerks"] (slice_val clerks_sl) ∗

  (* state-machine *)
  "#HisSm" ∷ is_StateMachine sm P Pcrash ∗

  (* ghost-state *)
  "Hstate" ∷ crash_borrow (own_replica_ghost γ γsrv epoch σg sealed ∗ P epoch σg.*1 sealed) (
    ∃ epoch σ' sealed, own_Server_ghost γ γsrv epoch σ' sealed ∗ Pcrash epoch σ' sealed
  ) ∗
  "%Hσ_nextIndex" ∷ ⌜length σg = int.nat nextIndex⌝ ∗

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
  ∃ (mu:val) P Pcrash,
  "#Hmu" ∷ readonly (s ↦[pb.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock pbN mu (own_Server s γ γsrv P Pcrash) ∗
  "#Hsys_inv" ∷ sys_inv γ.

Lemma wpc_Server__isEpochStale {stk} (s:loc) γ (currEpoch epoch:u64) :
  {{{
        is_epoch_lb γ epoch ∗
        s ↦[pb.Server :: "epoch"] #currEpoch ∗
        own_epoch γ currEpoch
  }}}
    pb.Server__isEpochStale #s #epoch @ stk
  {{{
        RET #(bool_decide (int.Z epoch < int.Z currEpoch));
        ⌜int.nat currEpoch ≥ int.nat epoch⌝ ∗
        s ↦[pb.Server :: "epoch"] #currEpoch ∗ own_epoch γ currEpoch
  }}}
  {{{
        own_epoch γ currEpoch
  }}}
.
Proof.
  iIntros (Φ Φc) "(#Hlb & HcurrEpoch & Hepoch) HΦ".
  wpc_call.
  { iFrame. }
  { iFrame. }
  iCache with "Hepoch HΦ".
  { iLeft in "HΦ". iApply "HΦ". iFrame. }

  wpc_pures.
  wpc_loadField.
  wpc_pures.
  iDestruct (mono_nat_lb_own_valid with "Hepoch Hlb") as %[_ Hineq].

  iRight in "HΦ".
  iModIntro.
  iApply ("HΦ").
  iFrame "∗%".
Qed.

End pb_definitions.
