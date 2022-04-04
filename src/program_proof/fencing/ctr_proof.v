From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import ctr.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export urpc_lib urpc_proof urpc_spec.
From iris.algebra Require Import cmra.
From iris.base_logic Require Export mono_nat.

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
Context `{!mapG Σ u64 bool}.

Definition own_latest_epoch γ (e:u64) (q:Qp) : iProp Σ :=
  mono_nat_auth_own γ.(epoch_gn) q (int.nat e).

Definition is_latest_epoch_lb γ (e:u64) : iProp Σ :=
  mono_nat_lb_own γ.(epoch_gn) (int.nat e).

Definition own_unused_epoch γ (e:u64) : iProp Σ :=
  e ⤳[γ.(epoch_token_gn)] false.

Definition own_val γ (e:u64) (v:u64) (q:Qp): iProp Σ :=
  e ⤳[γ.(val_gn)]{# q } v ∗
  e ⤳[γ.(epoch_token_gn)]□ true.

(* If someone has own_val, that means the ctr sever saw that epoch number, which
   means the own_unused_epoch was given up. *)
Lemma unused_own_val_false γ e v q :
  own_unused_epoch γ e -∗ own_val γ e v q -∗ False.
Proof.
Admitted.

Lemma own_val_combine γ e v1 q1 v2 q2 :
  own_val γ e v1 q1 -∗ own_val γ e v2 q2 -∗ own_val γ e v1 (q1 + q2) ∗ ⌜v1 = v2⌝.
Proof.
Admitted.

Lemma own_val_split γ e v q1 q2 :
  own_val γ e v (q1 + q2) -∗ own_val γ e v q1 ∗ own_val γ e v q2.
Proof.
Admitted.

Definition own_Clerk (ck:loc) : iProp Σ.
Admitted.

(* NOTE: consider lt_eq_lt_dec: ∀ n m : nat, {n < m} + {n = m} + {m < n} *)
Lemma wp_Clerk__Get γ ck (e:u64) :
  ∀ Φ,
  own_Clerk ck -∗
  (|={⊤,∅}=> ∃ latestEpoch, if decide (int.Z latestEpoch < int.Z e)%Z then
      own_latest_epoch γ latestEpoch (1/2)%Qp ∗
      own_unused_epoch γ e ∗
                            (∀ v, own_val γ e v (1/2)%Qp ∗
                                           own_val γ latestEpoch v (1/2)%Qp ∗
                                           own_latest_epoch γ e (1/2)%Qp
                                           ={∅,⊤}=∗ (own_Clerk ck -∗ Φ #v))
   else if decide (int.Z latestEpoch = int.Z e) then
    ∃ v, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
     own_val γ e v (1/2)%Qp ∗
    (own_val γ e v (1/2)%Qp ∗ own_latest_epoch γ e (1/2)%Qp ={∅,⊤}=∗ (own_Clerk ck -∗ Φ #v))
   else
     True) -∗
    WP Clerk__Get #ck #e {{ Φ }}.
Proof.
Admitted.

Lemma wp_Clerk__Put γ ck (e v:u64) :
  ∀ Φ,
  own_Clerk ck -∗
  (|={⊤,∅}=> ∃ latestEpoch, if decide (int.Z latestEpoch < int.Z e)%Z then
      own_latest_epoch γ latestEpoch (1/2)%Qp ∗
      own_unused_epoch γ e ∗
                            (own_val γ e v (1/2)%Qp ∗
                             (∃ oldv, own_val γ latestEpoch oldv (1/2)%Qp) ∗
                                           own_latest_epoch γ e (1/2)%Qp
                                           ={∅,⊤}=∗ (own_Clerk ck -∗ Φ #()))
   else if decide (int.Z latestEpoch = int.Z e) then
    ∃ oldv, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
     own_val γ e oldv (1/2)%Qp ∗
    (own_val γ e v (1/2)%Qp ∗ own_latest_epoch γ e (1/2)%Qp ={∅,⊤}=∗ (own_Clerk ck -∗ Φ #()))
   else
     True) -∗
    WP Clerk__Put #ck #v #e {{ Φ }}.
Proof.
Admitted.

End ctr_definitions.
