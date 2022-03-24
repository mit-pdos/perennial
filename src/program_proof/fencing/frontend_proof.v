From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import frontend.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export rpc_lib rpc_proof rpc_spec.
From Perennial.program_proof.fencing Require Export ctr_proof.

Section frontend_proof.

Context `{!heapGS Σ}.

Local Definition q2 := (1/2)%Qp.
Local Definition q4 := (1/4)%Qp.

Definition own_Server (s:loc) (epoch:u64) : iProp Σ :=
  ∃ (ck1 ck2:loc),
  "#Hepoch" ∷ readonly (s ↦[frontend.Server :: "epoch"] #epoch) ∗
  "Hck1" ∷ s ↦[frontend.Server :: "ck1"] #ck1 ∗
  "Hck2" ∷ s ↦[frontend.Server :: "ck1"] #ck2 ∗
  "Hck1_own" ∷ own_Clerk ck1 ∗
  "Hck2_own" ∷ own_Clerk ck2 ∗

  "Hghost1" ∷ (∃ ov, own_val epoch ov q4) ∗
  (* either have 1/2, or have 1/4 and have witness that latestEpoch >= epoch *)
  (* TODO: add second value *)
  "_" ∷ True.

Definition frontendN := nroot .@ "frontend".

Definition is_Server s : iProp Σ :=
  ∃ mu,
  "Hmu" ∷ readonly (s ↦[frontend.Server :: "mu"] mu) ∗
  "HmuInv" ∷ is_lock frontendN mu (∃ epoch, own_Server s epoch)
.

Definition k0 := (U64 0).
Definition k1 := (U64 1).

Definition kv_ptsto (k v:u64) : iProp Σ.
Admitted.

Global Instance kv_ptsto_timeless k v : Timeless (kv_ptsto k v).
Admitted.

Definition frontend_inv_def: iProp Σ :=
  ∃ (latestEpoch v:u64),
  "HlatestEpoch" ∷ own_epoch latestEpoch q2 ∗
  "Hval" ∷ own_val latestEpoch (Some v) q4 ∗
  "Hkv" ∷ kv_ptsto k0 v.

Definition frontend_inv : iProp Σ :=
  inv frontendN (frontend_inv_def).

Lemma wp_FetchAndIncrement (s:loc) (key:u64) :
  key = 0 ∨ key = 1 →
  is_Server s -∗
  frontend_inv -∗
  {{{
        True
  }}}
    Server__FetchAndIncrement #s #key
  {{{
        (v:u64), RET #v; True
  }}}.
Proof.
  intros Hkey.
  iIntros "#Hsrv #Hinv !#" (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (Hret_ptr) "Hret".
  wp_pures.
  wp_if_destruct.
  {
    wp_loadField.
    wp_loadField.
    wp_apply (wp_Clerk__Get with "Hck2_own").
    iInv "Hinv" as ">Hown" "Hclose".
    iNamed "Hown".
    iModIntro.
    iExists _; iFrame.
    iIntros "%Hfresh HlatestEpoch".
    iModIntro.
    admit.
  }
Admitted.

End frontend_proof.
