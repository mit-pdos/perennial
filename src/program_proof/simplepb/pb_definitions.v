From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Import pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.

Section pb_definitions.

Context `{!heapGS Σ}.

Record pb_system_names :=
{

}.

Implicit Type γ : pb_system_names.

Implicit Type σ : list (list u8).

Definition own_Server (s:loc) γ : iProp Σ :=
  ∃ (epoch:u64) (nextIndex:u64) (isPrimary:bool) (sm:loc) (clerks:Slice.t),
  (* physical *)
  "Hepoch" ∷ s ↦[pb.Server :: "epoch"] #epoch ∗
  "HnextIndex" ∷ s ↦[pb.Server :: "nextIndex"] #nextIndex ∗
  "HisPrimary" ∷ s ↦[pb.Server :: "isPrimary"] #isPrimary ∗
  "Hsm" ∷ s ↦[pb.Server :: "sm"] #sm ∗
  "Hclerks" ∷ s ↦[pb.Server :: "clerks"] (slice_val clerks) ∗

  (* ghost *)

  (* durable *)

  (* primary-only *)
  "#HareClerks" ∷ True
.

Definition pbN := nroot .@ "pb".

Definition is_Server (s:loc) γ : iProp Σ :=
  ∃ (mu:val),
  "#Hmu" ∷ readonly (s ↦[pb.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock pbN mu (own_Server s γ).

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

Definition proposal_ptsto (epoch:u64) (σ:list (list u8)) : iProp Σ.
Admitted.

Definition accepted_lb (epoch:u64) (σ:list (list u8)) : iProp Σ.
Admitted.

Definition ApplyAsBackup_spec (encoded_args:list u8) Φ : iProp Σ :=
  ∃ args σ,
    ⌜has_encoding_ApplyArgs encoded_args args⌝ ∗
    ⌜length σ = int.nat args.(index)⌝ ∗
    ⌜last σ = Some args.(op)⌝ ∗
    proposal_ptsto args.(epoch) σ ∗
    (∀ error (reply:list u8),
        ⌜has_encoding_Error reply error⌝ -∗
        (if (decide (error = 0)) then accepted_lb args.(epoch) σ else True) -∗
        Φ reply)
.

Lemma wp_Server__ApplyAsBackup (s:loc) (args_ptr:loc) γ (epoch index:u64) (op:list u8) op_sl :
  is_Server s γ -∗
  {{{
        "HargEpoch" ∷ args_ptr ↦[pb.ApplyArgs :: "epoch"] #epoch ∗
        "HargIndex" ∷ args_ptr ↦[pb.ApplyArgs :: "index"] #index ∗
        "HargOp" ∷ args_ptr ↦[pb.ApplyArgs :: "op"] (slice_val op_sl) ∗
        "HopSl" ∷ is_slice op_sl byteT 1 op
        (* TODO:
           ∗ epoch lower bound
           ∗ (epoch, index) ↦ blah
           ∗
         *)
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
Admitted.

End pb_definitions.
