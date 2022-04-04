From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import frontend.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export urpc_lib urpc_proof urpc_spec.
From Perennial.program_proof.fencing Require Export ctr_proof.
From iris.base_logic Require Import mono_nat.

Section frontend_proof.

Context `{!heapGS Σ}.

Local Definition q2 := (1/2)%Qp.
Local Definition q4 := (1/4)%Qp.

Definition k0 := (U64 0).
Definition k1 := (U64 1).

Definition kv_ptsto (k v:u64) : iProp Σ.
Admitted.

Global Instance kv_ptsto_timeless k v : Timeless (kv_ptsto k v).
Admitted.

Context `{!inG Σ epochR}.
Context `{!inG Σ valR}.
Context `{!mono_nat.mono_natG Σ}.
Context `{!mapG Σ u64 u64}.
Context `{!mapG Σ u64 unit}.

Definition frontend_inv_def γ: iProp Σ :=
  ∃ (latestEpoch v:u64),
  "HlatestEpoch" ∷ own_latest_epoch γ latestEpoch q2 ∗
  "Hval" ∷ own_val γ latestEpoch v q4 ∗
  "Hkv" ∷ kv_ptsto k0 v.

Definition own_FrontendServer (s:loc) γ (epoch:u64) : iProp Σ :=
  ∃ (ck1 ck2:loc),
  "#Hepoch" ∷ readonly (s ↦[frontend.Server :: "epoch"] #epoch) ∗
  "Hck1" ∷ s ↦[frontend.Server :: "ck1"] #ck1 ∗
  "Hck2" ∷ s ↦[frontend.Server :: "ck2"] #ck2 ∗
  "Hck1_own" ∷ own_Clerk ck1 ∗
  "Hck2_own" ∷ own_Clerk ck2 ∗

  "Hghost1" ∷ (own_unused_epoch γ epoch ∨ (∃ v, is_latest_epoch_lb γ epoch ∗ own_val γ epoch v q4)).
  (* TODO: add second value *)

Definition frontendN := nroot .@ "frontend".

Definition is_Server s γ : iProp Σ :=
  ∃ mu,
  "Hmu" ∷ readonly (s ↦[frontend.Server :: "mu"] mu) ∗
  "HmuInv" ∷ is_lock frontendN mu (∃ epoch, own_FrontendServer s γ epoch)
.
Definition frontend_inv γ : iProp Σ :=
  inv frontendN (frontend_inv_def γ).

Lemma wp_FetchAndIncrement (s:loc) γ (key:u64) :
  key = 0 ∨ key = 1 →
  is_Server s γ -∗
  frontend_inv γ -∗
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
    wp_bind (ctr.Clerk__Get _ _).
    wp_apply (wp_wand _ _ _
                (λ v,
              ∃ (v0:u64),
              ⌜v = #v0⌝ ∗
            "Hlb" ∷ is_latest_epoch_lb γ epoch ∗
            "HepochVal" ∷ own_val γ epoch v0 q4 ∗
            "Hck1_own" ∷ own_Clerk ck1
                    )%I
               with "[Hck1_own Hghost1]").
    {
      wp_apply (wp_Clerk__Get with "Hck1_own").
      iInv "Hinv" as ">Hown" "Hclose".
      iNamed "Hown".
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "Hmask".

      iExists latestEpoch.
      destruct (decide (int.Z latestEpoch < int.Z epoch)%Z) as [Hineq|Hineq].
      { (* case: epoch number is new *)
        iDestruct "Hghost1" as "[Hunused | Hbad]"; last first.
        { (* is_latest_epoch_lb contradicts inequality *)
          iDestruct "Hbad" as (?) "[#Hlb _]".
          iDestruct (mono_nat_lb_own_valid with "HlatestEpoch Hlb") as %Hvalid.
          exfalso. word.
        }
        iFrame.
        iIntros (v0) "(HnewVal & HprevEpochVal & HlatestEpoch)".
        iDestruct (ghost_map_points_to_agree with "Hval HprevEpochVal") as %Hagree.
        rewrite Hagree.
        iMod "Hmask".
        iEval (rewrite -Qp_quarter_quarter) in "HnewVal".
        iDestruct "HnewVal" as "[HnewVal HnewVal2]".
        iDestruct (mono_nat_lb_own_get with "HlatestEpoch") as "#Hlb". (* for doing the put *)
        iMod ("Hclose" with "[HlatestEpoch HnewVal Hkv]") as "_".
        {
          iNext.
          iExists _, _.
          iFrame.
        }
        iModIntro.
        iIntros "Hck1_own".
        iRename "HnewVal2" into "HepochVal".
        iExists _.
        iSplitL ""; first done.
        iFrame "∗#".
      }
      { (* case: ctr server already knows about latest epoch number *)
        (* XXX: this destruct only handles the if/else when using int.Z. Why? *)
        destruct (decide (int.Z latestEpoch = int.Z epoch)) as [Heq|Heasy]; last done.
        replace (latestEpoch) with (epoch) by word.
        iDestruct "Hghost1" as "[Hbad|Hghost1]".
        { (* non-matching case, contradictory *)
          iExFalso.
          (* FIXME: to make this work, own_unused_epoch and own_val have to be contradictory; maybe own_val have a frozen points-to or something *)
          admit.
        }
        {
          iDestruct "Hghost1" as (v') "[#Hlb Hghost1]".
          iDestruct (ghost_map_points_to_combine with "Hval Hghost1") as "[Hval %HvEq]".
          rewrite dfrac_op_own.
          rewrite Qp_quarter_quarter.
          iExists v.
          iFrame.

          iIntros "[Hval HlatestEpoch]".
          iMod "Hmask".
          iEval (rewrite -Qp_quarter_quarter) in "Hval".
          iDestruct "Hval" as "[HnewVal HnewVal2]".
          iMod ("Hclose" with "[HlatestEpoch HnewVal Hkv]") as "_".
          {
            iNext.
            iExists _, _.
            iFrame.
          }
          iModIntro.
          iIntros.
          iExists _; iSplitL ""; first done.
          iFrame "∗#".
        }
      }
    }
    iIntros (gv) "HH".
    iDestruct "HH" as (v) "[%Hval HH]".
    rewrite Hval.
    iNamed "HH".
    wp_store.

    (* Put(epoch, ret + 1) *)
    wp_loadField.
    wp_load.
    wp_loadField.
    admit.
  }
  { (* same proof, but with second server *)
    admit.
  }
Admitted.

End frontend_proof.
