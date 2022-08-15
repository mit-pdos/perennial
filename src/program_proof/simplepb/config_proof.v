From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export config.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.

Section config_proof.

Record config_names :=
{
  epoch_gn:gname ;
  config_val_gn:gname;
}.

Class configG Σ := {
    config_epochG :> mono_natG Σ ;
    config_configG :> inG Σ (dfrac_agreeR (leibnizO (list u64)));
}.

Implicit Type γ : config_names.

Context `{!heapGS Σ}.
Context `{!configG Σ}.

Definition own_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(epoch_gn) (1/2) (int.nat epoch).
Definition is_epoch_lb γ (epoch:u64) : iProp Σ :=
  mono_nat_lb_own γ.(epoch_gn) (int.nat epoch).

Definition own_config γ (conf:list u64) : iProp Σ :=
  own γ.(config_val_gn) (to_dfrac_agree (DfracOwn (1/2)) (conf: (leibnizO _)))
.

Definition is_host (configHost:u64) γ : iProp Σ := True.

Definition is_Clerk (ck:loc) γ : iProp Σ := True.

Lemma wp_MakeClerk configHost γ:
  {{{
      is_host configHost γ
  }}}
    config.MakeClerk #configHost
  {{{
      ck, RET #ck; is_Clerk ck γ
  }}}
.
Proof.
Admitted.

Lemma wp_Clerk__GetEpochAndConfig (ck:loc) γ Φ :
  is_Clerk ck γ -∗
  □ (£ 1 ={⊤,∅}=∗ ∃ epoch conf, own_epoch γ epoch ∗
                                    own_config γ conf ∗
    (⌜int.nat epoch < int.nat (word.add epoch (U64 1))⌝ -∗ own_epoch γ (word.add epoch (U64 1)) -∗ own_config γ conf ={∅,⊤}=∗
      (∀ conf_sl, is_slice conf_sl uint64T 1 conf -∗ Φ (#(LitInt (word.add epoch (U64 1))), slice_val conf_sl)%V)
                                )
  ) -∗
  WP config.Clerk__GetEpochAndConfig #ck {{ Φ }}
.
Proof.
Admitted.

Lemma wp_Clerk__WriteConfig (ck:loc) new_conf new_conf_sl epoch γ Φ :
  is_Clerk ck γ -∗
  is_slice new_conf_sl uint64T 1 new_conf ∗
  is_epoch_lb γ epoch -∗
  □ (|={⊤,∅}=> ∃ latest_epoch, own_epoch γ latest_epoch ∗
      if (decide (latest_epoch = epoch)) then
        ∃ conf, own_config γ conf ∗ (own_config γ new_conf -∗ own_epoch γ epoch ={∅,⊤}=∗ Φ #0)
      else
        (own_epoch γ latest_epoch ={∅,⊤}=∗ (∀ (err:u64), ⌜err ≠ 0⌝ → Φ #err))
  ) -∗
  WP config.Clerk__WriteConfig #ck #epoch
  {{ Φ }}
.
Proof.
Admitted.

End config_proof.
