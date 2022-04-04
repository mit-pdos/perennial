From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import frontend.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export urpc_lib urpc_proof urpc_spec.
From Perennial.program_proof.fencing Require Export ctr_proof.
From Perennial.program_proof Require Export marshal_proof.
From iris.base_logic Require Import mono_nat.

Module config.
Section config_proof.
Context `{!heapGS Σ}.

Record names :=
  {
    urpc_gn:server_chan_gnames
  }.

Context (γ:names).

Program Definition Get_spec host_inv :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∀ v l, ⌜has_encoding l [EncUInt64 v]⌝ -∗ host_inv v -∗ Φ l)%I
.
Next Obligation.
  solve_proper.
Defined.

Program Definition AcquireEpoch_spec epoch_tok host_inv :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∃ newhost, ⌜has_encoding reqData [EncUInt64 newhost]⌝ ∗
  host_inv newhost ∗
  (∀ l epoch, ⌜has_encoding l [EncUInt64 epoch]⌝ -∗ epoch_tok epoch -∗ Φ l))%I
.
Next Obligation.
  solve_proper.
Defined.

Program Definition trivial_spec :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∀ (l:list u8), True -∗ Φ l)%I
.
Next Obligation.
  solve_proper.
Defined.

Context `{!rpcregG Σ}.

Definition is_host (host:u64) (epoch_tok : u64 → iProp Σ) (host_inv:u64 → iProp Σ): iProp Σ :=
  handler_spec γ.(urpc_gn) host (U64 0) (AcquireEpoch_spec epoch_tok host_inv) ∗
  handler_spec γ.(urpc_gn) host (U64 1) (Get_spec host_inv) ∗
  handler_spec γ.(urpc_gn) host (U64 2) trivial_spec ∗
  handlers_dom γ.(urpc_gn) {[ (U64 0) ; (U64 1) ; (U64 2)]}
.

Definition is_Clerk (ck:loc) (host:u64): iProp Σ :=
  ∃ (cl:loc),
    "#Hcl" ∷ readonly (ck ↦[Clerk :: "cl"] #cl) ∗
    "#His_cl" ∷ is_RPCClient cl host
.

Lemma wp_MakeClerk host epoch_tok host_inv :
  is_host host epoch_tok host_inv -∗
  {{{
        True
  }}}
    config.MakeClerk #host
  {{{
        (ck:loc), RET #ck; is_Clerk ck host
  }}}.
Proof.
  iIntros "#Hhost !#" (Φ) "_ HΦ".
  wp_lam.
  wp_apply (wp_allocStruct).
  { naive_solver. }
  iIntros (ck) "Hck".
  wp_pures.
  iDestruct (struct_fields_split with "Hck") as "HH".
  iNamed "HH".
  wp_apply (wp_MakeClient).
  iIntros (?) "#His_cl".
  wp_storeField.
  iMod (readonly_alloc_1 with "cl") as "#Hcl".
  iApply "HΦ".
  iModIntro.
  iExists _.
  iFrame "#".
Qed.

Lemma wp_Clerk__AcquireEpoch ck host newHost epoch_tok host_inv :
  is_host host epoch_tok host_inv -∗
  is_Clerk ck host -∗
  {{{
        True
  }}}
    config.Clerk__AcquireEpoch #ck #newHost
  {{{
        (epoch:u64), RET #epoch; epoch_tok epoch
  }}}.
Proof.
Admitted.

Lemma wp_Clerk__Get ck host epoch_tok host_inv :
  is_host host epoch_tok host_inv -∗
  is_Clerk ck host -∗
  {{{
        True
  }}}
    config.Clerk__Get #ck
  {{{
        (v:u64), RET #host; host_inv v
  }}}.
Proof.
Admitted.

End config_proof.
End config.
