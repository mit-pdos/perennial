From iris.algebra Require Import gmap lib.mono_nat.
From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic Require Import lib.own.
From iris.bi.lib Require Import fractional.
From Perennial.program_proof Require Import proof_prelude.

Class kvMapG Σ :=
  { kv_map_inG :> inG Σ (gmapUR u64 (prodR (fracR) (agreeR (leibnizO (list u8))) )) }.

Definition kvptsto_frac `{!kvMapG Σ} γ (k:u64) (q:Qp) (v:list u8) :=
  own γ {[ k := ((q / 2)%Qp, to_agree (v: leibnizO (list u8))) ]}.

Definition kvptsto `{!kvMapG Σ} γ k v := kvptsto_frac γ k 1%Qp v.

Section memkv_ghost.

Context `{!kvMapG Σ}.

Lemma kvptsto_agree γ k q v q' v':
  kvptsto_frac γ k q v -∗
  kvptsto_frac γ k q' v' -∗
  ⌜v = v'⌝
.
Proof.
Admitted.

Lemma kvptsto_update v' γ k v1 v2 :
  kvptsto γ k v1 -∗
  kvptsto γ k v2 ==∗
  kvptsto γ k v' ∗
  kvptsto γ k v'
.
Proof.
Admitted.

End memkv_ghost.
