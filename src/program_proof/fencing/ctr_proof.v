From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import ctr.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export rpc_lib rpc_proof rpc_spec.

Section ctr_definitions.
Context `{!gooseGlobalGS Σ}.
Context `{!heapGS Σ}.

Record ctr_names :=
  {}.

Definition epoch_ptsto (e:u64) : iProp Σ.
Admitted.

Definition kv_epoch_ptsto (k e:u64) (v:option u64) : iProp Σ.
Admitted.

Definition kv_ptsto (k v:u64) : iProp Σ.
Admitted.

Definition own_Clerk (ck:loc) : iProp Σ.
Admitted.


(* |={Eo,Ei}=> ∃ vold, kv_ptsto k vold ∗ (kv_ptsto k vnew ={Ei,Eo}=∗ Q) *)

(* XXX: the current Clerk is a sequential clerk: can only do one operation at a
   time with it. Will need to have multiple CIDs to do multiple operations. *)

Lemma wp_Clerk__Put_typical {Eo Ei:coPset} Φ (k v:u64):
  (|={Eo,Ei}=> ∃ vold, kv_ptsto k vold ∗ (kv_ptsto k v ={Ei,Eo}=∗ Φ #v)) -∗
    WP Clerk__Put #() @ Eo {{ Φ }}.
Proof.
Admitted.

(*
Lemma wp_Clerk__Put {Eo Ei:coPset} Φ (k e v:u64):
  (|={Eo,Ei}=> ∃ vold, kv_ptsto k vold ∗ kv_epoch_ptsto k e vold ∗
    (kv_ptsto k v ∗ kv_epoch_ptsto k e v ={Ei,Eo}=∗ Φ #v)) -∗
    WP Clerk__Put #() @ Eo {{ Φ }}.
Proof.
Admitted.

Lemma wp_Clerk__Put_unknown {Eo Ei:coPset} Φ (k e v:u64):
  (|={Eo,Ei}=> ∃ vold, kv_ptsto k vold ∗ kv_epoch_unknown k e ∗
    (kv_ptsto k v ∗ kv_epoch_ptsto k e v ={Ei,Eo}=∗ Φ #v)) -∗
    WP Clerk__Put #() @ Eo {{ Φ }}.
Proof.
Admitted.
*)

Lemma wp_Clerk__Get {Eo Ei Ei2:coPset} ck (k e:u64) :
  ∀ Φ,
  own_Clerk ck -∗
  (|={Eo,Ei}=> ∃ latestEpoch, epoch_ptsto latestEpoch ∗
    (*(⌜int.Z latestEpoch > int.Z e⌝ → epoch_ptsto latestEpoch ={Ei, Eo}=∗ Φ #EStale) ∗*) (* XXX: program exits in this case *)
    (⌜int.Z latestEpoch ≤ int.Z e⌝ → epoch_ptsto e ={Ei}=∗ (* XXX: one inner mask is probably enough, thhough we could have multiple invariants *)
     (∃ oldv, kv_epoch_ptsto k e oldv ∗ (∃ v, ⌜is_Some oldv → oldv = Some v⌝ →
                                               kv_epoch_ptsto k e (Some v) ={Ei2,Eo}=∗
                                                              (own_Clerk ck -∗ Φ #v))))) -∗
    WP Clerk__Get #ck #e @ Eo {{ Φ }}.
Proof.
Admitted.

(*
Lemma wp_Server__Put {Eo Ei:coPset} Φ (k e v:u64) (s args:loc):
  (|={Eo,Ei}=> ∃ vold, kv_ptsto k vold ∗ kv_ptsto_epoch k e vold ∗
    (kv_ptsto k v ∗ kv_ptsto_epoch k e v ={Ei,Eo}=∗ Φ #v)) -∗
    WP Server__Put #s #args @ Eo {{ Φ }}.
Proof.
  iIntros "Hpre".
  wp_lam.
  wp_pures.
  (* wp_loadField. *)
Admitted. *)

End ctr_definitions.
