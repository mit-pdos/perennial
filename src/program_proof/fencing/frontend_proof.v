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

Context `{!inG Σ epochR}.
Context `{!inG Σ valR}.
Context `{!mono_nat.mono_natG Σ}.
Context `{!mapG Σ u64 u64}.
Context `{!mapG Σ u64 bool}.

Definition kv_ptsto (γ:gname) (k v:u64) : iProp Σ :=
  k ⤳[γ]{# 1/2} v.

Context `{γkv:gname}.

Definition frontend_inv_def γ: iProp Σ :=
  ∃ (latestEpoch v:u64),
  "HlatestEpoch" ∷ own_latest_epoch γ latestEpoch q2 ∗
  "Hval" ∷ own_val γ latestEpoch v q4 ∗
  "Hkv" ∷ kv_ptsto γkv k0 v.

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

Lemma wp_FetchAndIncrement (s:loc) γ (key:u64) Q :
  key = 0 ∨ key = 1 →
  is_Server s γ -∗
  frontend_inv γ -∗
  {{{
        |={⊤∖↑frontendN,∅}=> ∃ v, kv_ptsto γkv k0 v ∗ (kv_ptsto γkv k0 (word.add v 1) ={∅,⊤∖↑frontendN}=∗ Q v)
  }}}
    Server__FetchAndIncrement #s #key
  {{{
        (v:u64), RET #v; Q v
  }}}.
Proof.
  intros Hkey.
  iIntros "#Hsrv #Hinv !#" (Φ) "Hkvfupd HΦ".
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
            "#Hlb" ∷ is_latest_epoch_lb γ epoch ∗
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
        iDestruct (own_val_combine with "Hval HprevEpochVal") as "[_ %Hagree]".
        rewrite Hagree.
        iMod "Hmask".
        iEval (rewrite -Qp_quarter_quarter) in "HnewVal".
        iDestruct (own_val_split with "HnewVal") as "[HnewVal HnewVal2]".
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
          iDestruct (unused_own_val_false with "Hbad Hval") as "$".
        }
        {
          iDestruct "Hghost1" as (v') "[#Hlb Hghost1]".
          iDestruct (own_val_combine with "Hval Hghost1") as "[Hval %HvEq]".
          rewrite Qp_quarter_quarter.
          iExists v.
          iFrame.

          iIntros "[Hval HlatestEpoch]".
          iMod "Hmask".
          iEval (rewrite -Qp_quarter_quarter) in "Hval".
          iDestruct (own_val_split with "Hval") as "[HnewVal HnewVal2]".
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

    wp_apply (wp_Clerk__Put γ with "Hck1_own").
    iInv "Hinv" as ">HH" "Hclose".
    iNamed "HH".
    iExists latestEpoch.
    iApply (fupd_mask_intro).
    { set_solver. }
    iIntros "Hmask".
    iDestruct (mono_nat_lb_own_valid with "HlatestEpoch Hlb") as %Hvalid.
    destruct (decide (int.Z latestEpoch < int.Z epoch)%Z) as [Hineq|Hineq].
    {
      exfalso.
      word.
    }
    destruct (decide (int.Z latestEpoch = int.Z epoch)%Z) as [Heq|Heasy]; last done.
    replace (latestEpoch) with (epoch) by word.
    iDestruct (own_val_combine with "HepochVal Hval") as "[Hval %Hveq]".
    rewrite Qp_quarter_quarter.
    rewrite -Hveq.
    iExists v.
    iFrame.

    iIntros "[Hval HlatestEpoch]".
    iMod "Hmask".
    iEval (rewrite -Qp_quarter_quarter) in "Hval".
    iDestruct (own_val_split with "Hval") as "[Hval HepochVal]".
    iMod "Hkvfupd".
    iDestruct "Hkvfupd" as (?) "[Hkv2 Hkvfupd]".
    clear Hveq.
    iDestruct (ghost_map_points_to_combine with "Hkv Hkv2") as "[Hkv %Hveq]".
    rewrite dfrac_op_own.
    rewrite Qp_half_half.
    rewrite -Hveq.

    iMod (ghost_map_points_to_update (word.add v 1) with "Hkv") as "Hkv".
    iDestruct "Hkv" as "[Hkv Hkv2]".
    iMod ("Hkvfupd" with "Hkv2") as "HQ".

    iMod ("Hclose" with "[Hval HlatestEpoch Hkv]") as "HH".
    {
      iNext.
      iExists _, _; iFrame "Hval∗".
    }
    iModIntro.
    iIntros "Hck1_own".
    wp_pures.
    wp_loadField.

    wp_apply (release_spec with "[$Hlocked $HmuInv Hck1 Hck2 Hck1_own Hck2_own HepochVal ]").
    {
      iExists epoch.
      iNext.
      iExists _, _.
      iFrame "Hck1 Hck2 ∗#".
      iRight.
      iExists _; iFrame.
    }
    wp_pures.
    wp_load.
    iApply "HΦ". (* TODO: post-condition should say something *)
    by iFrame.
  }
  { (* same proof, but with second server *)
    admit.
  }
Admitted.

End frontend_proof.
