From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Import pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From iris.base_logic Require Export lib.ghost_var.
From iris.base_logic Require Export mono_nat.

Section pb_definitions.

Context `{!heapGS Σ}.

Record pb_server_names :=
{
  urpc_gn: server_chan_gnames ;
  epoch_gn: gname ;
}.

Implicit Type γ : pb_server_names.

Implicit Type σ : list (list u8).
Implicit Type epoch : u64.

Definition proposal_ptsto γ (epoch:u64) (σ:list (list u8)) : iProp Σ.
Admitted.

Definition accepted_lb γ (epoch:u64) (σ:list (list u8)) : iProp Σ.
Admitted.

Context `{!mono_natG Σ}.

Definition own_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(epoch_gn) 1 (int.nat epoch).

Definition is_epoch_lb γ (epoch:u64) : iProp Σ :=
  mono_nat_lb_own γ.(epoch_gn) (int.nat epoch).

Definition own_Server_ghost γ epoch σ : iProp Σ.
Admitted.

Definition is_ApplyFn (applyFn:val) γ P : iProp Σ :=
  ∀ op_sl (epoch:u64) σ op,
  {{{
        (own_Server_ghost γ epoch σ ={⊤}=∗ own_Server_ghost γ epoch (σ++[op])) ∗ P epoch σ ∗ is_slice op_sl byteT 1 op
  }}}
    applyFn (slice_val op_sl)
  {{{
        RET #(); P epoch (σ ++ [op])
  }}}
.

Definition is_StateMachine (sm:loc) γ P : iProp Σ :=
  ∃ (applyFn:val),
  "#Happly" ∷ sm ↦[pb.StateMachine :: "Apply"] applyFn ∗
  "#HapplySpec" ∷ is_ApplyFn applyFn γ P
.

Definition own_Server (s:loc) γ P : iProp Σ :=
  ∃ (epoch:u64) σ (nextIndex:u64) (isPrimary:bool) (sm:loc) (clerks:Slice.t),
  (* physical *)
  "Hepoch" ∷ s ↦[pb.Server :: "epoch"] #epoch ∗
  "HnextIndex" ∷ s ↦[pb.Server :: "nextIndex"] #nextIndex ∗
  "HisPrimary" ∷ s ↦[pb.Server :: "isPrimary"] #isPrimary ∗
  "Hsm" ∷ s ↦[pb.Server :: "sm"] #sm ∗
  "Hclerks" ∷ s ↦[pb.Server :: "clerks"] (slice_val clerks) ∗

  (* state-machine *)
  "#HisSm" ∷ is_StateMachine sm γ P ∗

  "Hstate" ∷ P epoch σ ∗

  (* primary-only *)
  "#Hclerks_rpc" ∷ True
.

Definition pbN := nroot .@ "pb".

Definition is_Server (s:loc) γ : iProp Σ :=
  ∃ (mu:val) P,
  "#Hmu" ∷ readonly (s ↦[pb.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock pbN mu (own_Server s γ P).

Record ApplyArgsC :=
{
  epoch : u64 ;
  index : u64 ;
  op : list u8 ;
}.

Definition has_encoding_ApplyArgs (encoded:list u8) (args:ApplyArgsC) : Prop.
Admitted.

Definition has_encoding_Error (encoded:list u8) (error:u64) : Prop.
Admitted.

Program Definition ApplyAsBackup_spec γ :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args σ,
    ⌜has_encoding_ApplyArgs encoded_args args⌝ ∗
    ⌜length σ = int.nat args.(index)⌝ ∗
    ⌜last σ = Some args.(op)⌝ ∗
    proposal_ptsto γ args.(epoch) σ ∗
    (∀ error (reply:list u8),
        ⌜has_encoding_Error reply error⌝ -∗
        (if (decide (error = 0)) then accepted_lb γ args.(epoch) σ else True) -∗
        Φ reply)
    )%I
.
Next Obligation.
  solve_proper.
Defined.

Context `{!urpcregG Σ}.

Definition is_pb_host γ (host:chan) :=
  handler_spec γ.(urpc_gn) host (U64 0) (ApplyAsBackup_spec γ).

Definition is_Clerk (ck:loc) γ : iProp Σ :=
  ∃ (cl:loc) srv,
  "#Hcl" ∷ readonly (ck ↦[pb.Clerk :: "cl"] #cl) ∗
  "#Hcl_rpc"  ∷ is_uRPCClient cl srv ∗
  "#Hsrv" ∷ is_pb_host γ srv
.

Lemma wp_Server__epochFence (s:loc) γ (currEpoch epoch:u64) :
  {{{
        is_epoch_lb γ epoch ∗
        s ↦[pb.Server :: "epoch"] #currEpoch ∗
        own_epoch γ currEpoch
  }}}
    pb.Server__epochFence #s #epoch
  {{{
        RET #(negb (bool_decide (int.nat currEpoch = int.nat epoch))); s ↦[pb.Server :: "epoch"] #currEpoch ∗ own_epoch γ currEpoch
  }}}
.
Proof.
Admitted.

Lemma wp_Server__ApplyAsBackup (s:loc) (args_ptr:loc) γ (epoch index:u64) (op:list u8) op_sl :
  is_Server s γ -∗
  {{{
        "HargEpoch" ∷ args_ptr ↦[pb.ApplyArgs :: "epoch"] #epoch ∗
        "HargIndex" ∷ args_ptr ↦[pb.ApplyArgs :: "index"] #index ∗
        "HargOp" ∷ args_ptr ↦[pb.ApplyArgs :: "op"] (slice_val op_sl) ∗
        "HopSl" ∷ is_slice op_sl byteT 1 op ∗
        "#HepochLb" ∷ is_epoch_lb γ epoch
  }}}
    pb.Server__ApplyAsBackup #s #args_ptr
  {{{
        RET #(); True
  }}}
  .
Proof.
  iIntros "#HisSrv" (Φ) "!# Hpre HΦ".
  iNamed "Hpre".
  iNamed "HisSrv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Server__epochFence with "[$Hepoch $HepochGhost $HepochLb]").
  iIntros "Hepoch".
  wp_if_destruct.
  { (* return error: stale *)
    admit.
  }
  replace (epoch0) with (epoch) by word.

  wp_loadField.
  wp_loadField.
  wp_if_destruct.
  { (* return errror: out-of-order *)
    admit.
  }

  wp_loadField.
  wp_loadField.
Admitted.

Lemma wp_Server__Apply (s:loc) γ op_sl:
  {{{
        is_Server s γ
  }}}
    pb.Server__Apply #s (slice_val op_sl)
  {{{
        RET #(); True
  }}}
  .
Proof.
  iIntros (Φ) "#Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_if_destruct.
  { (* return error "not primary" *)
    admit.
  }
  wp_loadField.
Admitted.

End pb_definitions.
