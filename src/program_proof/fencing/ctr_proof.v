From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import ctr.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export rpc_lib rpc_proof rpc_spec.
From iris.algebra Require Import cmra.
From iris.base_logic Require Import mono_nat.

From Perennial.program_proof.fencing Require Export map.

Section ctr_definitions.

Context `{!gooseGlobalGS Σ}.
Context `{!heapGS Σ}.

Record ctr_names :=
{
  epoch_gn : gname ;
  epoch_token_gn : gname ;
  val_gn : gname ;
}.

Implicit Type γ : ctr_names.

Context `{!mono_natG Σ}.
Context `{!mapG Σ u64 u64}.
Context `{!mapG Σ u64 unit}.

Definition own_latest_epoch γ (e:u64) (q:Qp) : iProp Σ :=
  mono_nat_auth_own γ.(epoch_gn) q (int.nat e).

Definition is_latest_epoch_lb γ (e:u64) : iProp Σ :=
  mono_nat_lb_own γ.(epoch_gn) (int.nat e).

Definition own_unused_epoch γ (e:u64) : iProp Σ :=
  e ⤳[γ.(epoch_token_gn)] ().

Definition own_val γ (e:u64) (v:u64) (q:Qp): iProp Σ :=
  e ⤳[γ.(val_gn)]{# q } v.

Definition own_Clerk (ck:loc) : iProp Σ.
Admitted.

(* NOTE: consider lt_eq_lt_dec: ∀ n m : nat, {n < m} + {n = m} + {m < n} *)
Lemma wp_Clerk__Get γ ck (e:u64) :
  ∀ Φ,
  own_Clerk ck -∗
  (|={⊤,∅}=> ∃ latestEpoch, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
    if decide (int.Z latestEpoch < int.Z e)%Z then
      own_unused_epoch γ e ∗
                            (∀ v, own_val γ e v (1/2)%Qp ∗
                                           own_val γ latestEpoch v (1/2)%Qp ∗
                                           own_latest_epoch γ e (1/2)%Qp
                                           ={∅,⊤}=∗ (own_Clerk ck -∗ Φ #v))
   else if decide (latestEpoch = e) then
   ∃ v, own_val γ e v (1/2)%Qp ∗
    (own_val γ e v (1/2)%Qp ∗ own_latest_epoch γ e (1/2)%Qp ={∅,⊤}=∗ (own_Clerk ck -∗ Φ #v))
   else
     True) -∗
    WP Clerk__Get #ck #e {{ Φ }}.
Proof.
Admitted.

Lemma wp_Clerk__Put γ ck (e v:u64) :
  ∀ Φ,
  own_Clerk ck -∗
  (|={⊤,∅}=> ∃ latestEpoch, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
    if decide (int.Z latestEpoch < int.Z e)%Z then
      own_unused_epoch γ e ∗
                            (∀ oldv, own_val γ e v (1/2)%Qp ∗
                                           own_val γ latestEpoch oldv (1/2)%Qp ∗
                                           own_latest_epoch γ e (1/2)%Qp
                                           ={∅,⊤}=∗ (own_Clerk ck -∗ Φ #v))
   else if decide (latestEpoch = e) then
   ∃ oldv, own_val γ e oldv (1/2)%Qp ∗
    (own_val γ e v (1/2)%Qp ∗ own_latest_epoch γ e (1/2)%Qp ={∅,⊤}=∗ (own_Clerk ck -∗ Φ #v))
   else
     True) -∗
    WP Clerk__Put #ck #e #v {{ Φ }}.
Proof.
Admitted.

Lemma wp_Clerk__Get' γ ck (e:u64) :
  ∀ Φ,
  own_Clerk ck -∗
  (|={⊤,∅}=> ∃ latestEpoch, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
   ∃ v, own_val γ e v (1/2)%Qp ∗
  ( own_val γ e v (1/2)%Qp ∗
    own_latest_epoch γ e (1/2)%Qp ∗
    if decide (int.Z latestEpoch < int.Z e)%Z then
      own_val γ latestEpoch v (1/2)%Qp
    else ⌜latestEpoch = e⌝
    ={∅,⊤}=∗ (own_Clerk ck -∗ Φ #v))) -∗
    WP Clerk__Get #ck #e {{ Φ }}.
Proof.
Admitted.

Lemma wp_Clerk__Get'' γ ck (e:u64) :
  ∀ Φ,
  own_Clerk ck -∗
  (|={⊤,∅}=>
     (own_unused_epoch γ e ∗ (∃ v, own_val γ e v (1/2)%Qp
           ={∅,⊤}=∗ (own_Clerk ck -∗ Φ #v))) ∨
     (∃ v, own_val γ e v (1/2) ∗ (own_val γ e v (1/2) ={∅,⊤}=∗ (own_Clerk ck -∗ Φ #v)))) -∗
    WP Clerk__Get #ck #e {{ Φ }}.
Proof.
Admitted.

End ctr_definitions.
