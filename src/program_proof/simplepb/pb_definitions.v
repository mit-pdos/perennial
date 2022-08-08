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

Record OpRecord :=
  {
    or_OpType:Type ;
    or_has_op_encoding : or_OpType → list u8 → Prop ;
    or_has_op_encoding_injective : ∀ o1 o2 l, or_has_op_encoding o1 l → or_has_op_encoding o2 l → o1 = o2 ;
  }.

Context {op_record:OpRecord}.
Notation OpType := (or_OpType op_record).
Notation has_op_encoding := (or_has_op_encoding op_record).
Notation has_op_encoding_injective := (or_has_op_encoding_injective op_record).

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
    ⌜has_op_encoding op args.(ApplyArgs.op)⌝∗
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
        "%Hghost_op_op" ∷ ⌜has_op_encoding ghost_op.1 op⌝ ∗
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

Definition replyFn (σ:list OpType) (op:OpType) : (list u8).
Admitted.

Definition is_ApplyFn (applyFn:val) γ γsrv P : iProp Σ :=
  ∀ op_sl (epoch:u64) σ op ghost_op Q,
  {{{
        ⌜has_op_encoding ghost_op.1 op⌝ ∗
        (own_Server_ghost γ γsrv epoch σ ={⊤}=∗ own_Server_ghost γ γsrv epoch (σ++[ghost_op]) ∗ Q) ∗
        crash_borrow (own_Server_ghost γ γsrv epoch σ ∗ P epoch σ) (
          ∃ epoch' σ', (own_Server_ghost γ γsrv epoch' σ' ∗ P epoch' σ')
        )
        ∗
        readonly (is_slice_small op_sl byteT 1 op)
  }}}
    applyFn (slice_val op_sl)
  {{{
        reply_sl,
        RET (slice_val reply_sl);
        crash_borrow (own_Server_ghost γ γsrv epoch (σ ++ [ghost_op]) ∗ P epoch (σ ++ [ghost_op])) (
          ∃ epoch' σ',
          (own_Server_ghost γ γsrv epoch' σ' ∗ P epoch' σ')
        ) ∗
        is_slice reply_sl byteT 1 (replyFn ((λ x, x.1) <$> σ) ghost_op.1) ∗
        Q
  }}}
.

Definition is_StateMachine (sm:loc) γ γsrv P : iProp Σ :=
  ∃ (applyFn:val),
  "#Happly" ∷ readonly (sm ↦[pb.StateMachine :: "Apply"] applyFn) ∗
  "#HapplySpec" ∷ is_ApplyFn applyFn γ γsrv P
.

Definition own_Server (s:loc) γ γsrv P : iProp Σ :=
  ∃ (epoch:u64) σ (nextIndex:u64) (isPrimary:bool) (sm:loc) (clerks_sl:Slice.t),
  (* physical *)
  "Hepoch" ∷ s ↦[pb.Server :: "epoch"] #epoch ∗
  "HnextIndex" ∷ s ↦[pb.Server :: "nextIndex"] #nextIndex ∗
  "HisPrimary" ∷ s ↦[pb.Server :: "isPrimary"] #isPrimary ∗
  "Hsm" ∷ s ↦[pb.Server :: "sm"] #sm ∗
  "Hclerks" ∷ s ↦[pb.Server :: "clerks"] (slice_val clerks_sl) ∗

  (* state-machine *)
  "#HisSm" ∷ is_StateMachine sm γ γsrv P ∗

  (* ghost-state *)
  "Hstate" ∷ crash_borrow (own_Server_ghost γ γsrv epoch σ ∗ P epoch σ) (
    ∃ epoch σ, own_Server_ghost γ γsrv epoch σ ∗ P epoch σ
  ) ∗
  "%Hσ_nextIndex" ∷ ⌜length σ = int.nat nextIndex⌝ ∗

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
            "#Hprop_facts" ∷ is_proposal_facts γ epoch σ ∗
            "Hproposal" ∷ own_proposal γ epoch σ
        )
                   else True
.

Definition is_Server (s:loc) γ γsrv : iProp Σ :=
  ∃ (mu:val) P,
  "#Hmu" ∷ readonly (s ↦[pb.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock pbN mu (own_Server s γ γsrv P) ∗
  "#Hsys_inv" ∷ sys_inv γ.

Lemma wpc_Server__epochFence {stk} (s:loc) γ (currEpoch epoch:u64) :
  {{{
        is_epoch_lb γ epoch ∗
        s ↦[pb.Server :: "epoch"] #currEpoch ∗
        own_epoch γ currEpoch
  }}}
    pb.Server__epochFence #s #epoch @ stk
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

  destruct (bool_decide (int.Z currEpoch < int.Z epoch)%Z) as [] eqn:Hineq2.
  {
    apply bool_decide_eq_true in Hineq2.
    exfalso.
    word.
  }
  wpc_pures.
  wpc_loadField.
  wpc_pures.
  iRight in "HΦ".
  iModIntro.
  iApply ("HΦ").
  iFrame "∗%".
Qed.

End pb_definitions.
