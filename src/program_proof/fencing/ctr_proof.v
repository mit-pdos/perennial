From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import ctr.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export rpc_lib rpc_proof rpc_spec.

Section ctr_definitions.
Context `{!gooseGlobalGS Σ}.
Context `{!heapGS Σ}.

Record ctr_names :=
  {}.

Definition own_epoch (e:u64) (q:Qp): iProp Σ.
Admitted.

Definition own_val (e:u64) (v:option u64) (q:Qp): iProp Σ.
Admitted.

Global Instance own_epoch_timeless e q : Timeless (own_epoch e q).
Admitted.

Global Instance own_val_timeless e v q : Timeless (own_val e v q).
Admitted.

Definition own_Clerk (ck:loc) : iProp Σ.
Admitted.

Lemma wp_Clerk__Get {Eo Ei Ei2:coPset} ck (e:u64) :
  ∀ Φ,
  own_Clerk ck -∗
  (|={Eo,Ei}=> ∃ latestEpoch, own_epoch latestEpoch (1/2)%Qp ∗
    (*(⌜int.Z latestEpoch > int.Z e⌝ → epoch_ptsto latestEpoch ={Ei, Eo}=∗ Φ #EStale) ∗*) (* XXX: program exits in this case *)
    (⌜int.Z latestEpoch ≤ int.Z e⌝ → own_epoch e (1/2)%Qp ={Ei}=∗ (* XXX: one inner mask is probably enough, thhough we could have multiple invariants *)
     (∃ oldv, own_val e oldv (1/2)%Qp ∗ (∃ v, ⌜is_Some oldv → oldv = Some v⌝ →
                                               own_val e (Some v) (1/2)%Qp ={Ei2,Eo}=∗
                                                              (own_Clerk ck -∗ Φ #v))))) -∗
    WP Clerk__Get #ck #e @ Eo {{ Φ }}.
Proof.
Admitted.

Lemma wp_Clerk__Put {Eo Ei Ei2:coPset} ck (k e v:u64) :
  ∀ Φ,
  own_Clerk ck -∗
  (|={Eo,Ei}=> ∃ latestEpoch, own_epoch latestEpoch (1/2)%Qp ∗
    (*(⌜int.Z latestEpoch > int.Z e⌝ → epoch_ptsto latestEpoch ={Ei, Eo}=∗ Φ #EStale) ∗*) (* XXX: program exits in this case *)
    (⌜int.Z latestEpoch ≤ int.Z e⌝ → own_epoch e (1/2)%Qp ={Ei}=∗ (* XXX: one inner mask is probably enough, thhough we could have multiple invariants *)
     (∃ oldv, own_val e oldv (1/2)%Qp ∗ (own_val e (Some v) (1/2)%Qp ={Ei2,Eo}=∗ (own_Clerk ck -∗ Φ #v))))) -∗
    WP Clerk__Get #ck #e @ Eo {{ Φ }}.
Proof.
Admitted.

End ctr_definitions.
