From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import frontend.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export rpc_lib rpc_proof rpc_spec.

Section frontend_proof.

Context `{!heapGS Σ}.

Definition own_Server (s:loc) epoch : iProp Σ :=
  ∃ ck1 ck2,
  "#Hepoch" ∷ readonly (s ↦[frontend.Server :: "epoch"] #epoch) ∗
  "Hck1" ∷ s ↦[frontend.Server :: "ck1"] #ck1 ∗
  "Hck2" ∷ s ↦[frontend.Server :: "ck1"] #ck2 ∗
  (* TODO: add ownership of clerks *)
  "_" ∷ True.

Definition frontendN := nroot .@ "frontend".

Definition is_Server s : iProp Σ :=
  ∃ mu,
  "Hmu" ∷ readonly (s ↦[frontend.Server :: "mu"] mu) ∗
  "HmuInv" ∷ is_lock frontendN mu (∃ epoch, own_Server s epoch)
.

Lemma wp_FetchAndIncrement (s:loc) (key:u64) :
  key = 0 ∨ key = 1 →
  is_Server s -∗
  {{{
        True
  }}}
    Server__FetchAndIncrement #s #key
  {{{
        (v:u64), RET #v; True
  }}}.
Proof.
  intros Hkey.
  iIntros "#Hsrv !#" (Φ) "_ HΦ".
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
    wp_apply (wp_Clerk__Get_unknown).
  }
End frontend_proof.
