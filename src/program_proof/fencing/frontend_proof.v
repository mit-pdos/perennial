From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import frontend.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.grove_shared Require Export erpc_lib urpc_proof urpc_spec.
From Perennial.program_proof.fencing Require Export ctr_proof config_proof.
From Perennial.program_proof Require Import marshal_proof.
From iris.base_logic Require Import mono_nat.

Module frontend.
Section frontend_proof.

Context `{!heapGS Σ}.

Record frontend_names :=
{
  urpc_gn : server_chan_gnames;
  kv_gn : gname;
  ctr1_gn : ctr_names;
  ctr2_gn : ctr_names;
}.

Local Definition q2 := (1/2)%Qp.
Local Definition q4 := (1/4)%Qp.

Definition k0 := (W64 0).
Definition k1 := (W64 1).

Context `{!ctrG Σ}.
Context `{!urpcregG Σ}.
Context `{!erpcG Σ}.

Implicit Type γ : frontend_names.

Definition kv_ptsto γkv (k v:u64) : iProp Σ :=
  k ⤳[γkv]{# 1/2} v.

Definition frontend_inv1_def γ: iProp Σ :=
  ∃ (latestEpoch v:u64),
  "HlatestEpoch" ∷ own_latest_epoch γ.(ctr1_gn) latestEpoch q2 ∗
  "Hval" ∷ own_val γ.(ctr1_gn) latestEpoch v q4 ∗
  "Hkv" ∷ kv_ptsto γ.(kv_gn) k0 v.

Definition frontend_inv2_def γ: iProp Σ :=
  ∃ (latestEpoch v:u64),
  "HlatestEpoch" ∷ own_latest_epoch γ.(ctr2_gn) latestEpoch q2 ∗
  "Hval" ∷ own_val γ.(ctr2_gn) latestEpoch v q4 ∗
  "Hkv" ∷ kv_ptsto γ.(kv_gn) k1 v.

Definition own_Server (s:loc) γ (epoch:u64) : iProp Σ :=
  ∃ (ck1 ck2:loc),
  "#Hepoch" ∷ readonly (s ↦[frontend.Server :: "epoch"] #epoch) ∗
  "Hck1" ∷ s ↦[frontend.Server :: "ck1"] #ck1 ∗
  "Hck2" ∷ s ↦[frontend.Server :: "ck2"] #ck2 ∗
  "Hck1_own" ∷ ctr.own_Clerk γ.(ctr1_gn) ck1 ∗
  "Hck2_own" ∷ ctr.own_Clerk γ.(ctr2_gn) ck2 ∗

  "Hghost1" ∷ (own_unused_epoch γ.(ctr1_gn) epoch ∨ (∃ v, is_latest_epoch_lb γ.(ctr1_gn) epoch ∗ own_val γ.(ctr1_gn) epoch v q4)) ∗
  "Hghost2" ∷ (own_unused_epoch γ.(ctr2_gn) epoch ∨ (∃ v, is_latest_epoch_lb γ.(ctr2_gn) epoch ∗ own_val γ.(ctr2_gn) epoch v q4))
.

Definition frontendN := nroot .@ "frontend".

Definition is_Server s γ : iProp Σ :=
  ∃ mu,
  "Hmu" ∷ readonly (s ↦[frontend.Server :: "mu"] mu) ∗
  "HmuInv" ∷ is_lock frontendN mu (∃ epoch, own_Server s γ epoch)
.

Definition frontend_inv γ : iProp Σ :=
  "#Hinv1" ∷ inv frontendN (frontend_inv1_def γ) ∗
  "#Hunusedinv1" ∷ ctr.unused_epoch_inv γ.(ctr1_gn) ∗
  "#Hinv2" ∷ inv frontendN (frontend_inv2_def γ) ∗
  "#Hunusedinv2" ∷ ctr.unused_epoch_inv γ.(ctr2_gn)
.

Lemma wp_FetchAndIncrement (s:loc) γ (key:u64) Q :
  key = 0 ∨ key = 1 →
  is_Server s γ -∗
  frontend_inv γ -∗
  {{{
        |={⊤∖↑frontendN,∅}=> ∃ v, kv_ptsto γ.(kv_gn) key v ∗
      (⌜uint.nat v < uint.nat (word.add v (W64 1))⌝ -∗ kv_ptsto γ.(kv_gn) key (word.add v 1) ={∅,⊤∖↑frontendN}=∗ Q v)
  }}}
    Server__FetchAndIncrement #s #key
  {{{
        (v:u64), RET #v; Q v
  }}}.
Proof.
  intros Hkey.
  iIntros "#Hsrv #Hinv !#" (Φ) "Hkvfupd HΦ".
  wp_rec.
  wp_pures.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (Hret_ptr) "Hret".
  wp_pures.
  iNamed "Hinv".
  wp_if_destruct.
  {
    wp_loadField.
    wp_loadField.
    wp_bind (ctr.Clerk__Get _ _).
    wp_apply (wp_wand _ _ _
                (λ v,
              ∃ (v0:u64),
              ⌜v = #v0⌝ ∗
            "#Hlb" ∷ is_latest_epoch_lb γ.(ctr1_gn) epoch ∗
            "HepochVal" ∷ own_val γ.(ctr1_gn) epoch v0 q4 ∗
            "Hck1_own" ∷ ctr.own_Clerk γ.(ctr1_gn) ck1
                    )%I
               with "[Hck1_own Hghost1]").
    { (* ctr.Clerk__Get *)
      wp_apply (ctr.wp_Clerk__Get with "Hck1_own").
      iApply (ctr.EnterNewEpoch_spec_wand _ _ ((∃ v, own_val γ.(ctr1_gn) epoch v (1 / 4))
                                                    ∨ is_latest_epoch_lb_strict γ.(ctr1_gn) epoch
                                              ) with "[] [-]"); last first.
      { (* EnterNewEpoch(): first linearization point *)
        iInv "Hinv1" as ">Hown" "Hclose".
        iNamed "Hown".
        iApply fupd_mask_intro.
        {
          assert (disjoint (A:=coPset) (↑ctr.unusedN) (↑ctr.getN)).
          {
            unfold ctr.unusedN. unfold ctr.getN.
            by apply ndot_ne_disjoint.
          }
          assert (disjoint (A:=coPset) (↑ctr.unusedN) (↑frontendN)).
          {
            unfold ctr.unusedN. unfold frontendN.
            by apply ndot_ne_disjoint.
          }
          set_solver.
        }
        iIntros "Hmask".

        iExists latestEpoch.
        destruct (decide (uint.Z latestEpoch < uint.Z epoch)%Z) as [Hineq|Hineq].
        { (* case: epoch number is new *)
          iDestruct "Hghost1" as "[Hunused | Hbad]"; last first.
          { (* is_latest_epoch_lb contradicts inequality *)
            iDestruct "Hbad" as (?) "[#Hlb _]".
            iDestruct (mono_nat_lb_own_valid with "HlatestEpoch Hlb") as %Hvalid.
            exfalso. word.
          }
          iFrame.
          iIntros (v0) "HnewVal  HprevEpochVal  HlatestEpoch".
          iDestruct (own_val_combine with "Hval HprevEpochVal") as "[_ %Hagree]".
          rewrite Hagree.
          iMod "Hmask" as "_".
          iEval (rewrite -Qp.quarter_quarter) in "HnewVal".
          iDestruct (own_val_split with "HnewVal") as "[HnewVal HnewVal2]".
          iDestruct (mono_nat_lb_own_get with "HlatestEpoch") as "#Hlb". (* for doing the put *)
          iMod ("Hclose" with "[HlatestEpoch HnewVal Hkv]") as "_".
          {
            iNext.
            iExists _, _.
            iFrame.
          }
          iModIntro.
          iLeft.
          iExists _; iFrame.
        }
        { (* case: epoch number is not brand new *)
          iFrame.
          iIntros "Hlatest".
          iMod "Hmask".
          iDestruct "Hghost1" as "[Hunused|Hv]".
          { (* derive a contradiction with e == latestEpoch; the cast e <
               latestEpoch should require proving True, not proving Φ. We'll have to
               strengthen the spec for ctr *)
            destruct (decide (uint.Z latestEpoch = uint.Z epoch)).
            {
              replace (latestEpoch) with (epoch) by word.
              iMod (fupd_mask_subseteq (↑ctr.unusedN)).
              { (* TODO: this is a copy paste of the previous fupd_mask_intro. *)
                assert (disjoint (A:=coPset) (↑ctr.unusedN) (↑ctr.getN)).
                {
                  unfold ctr.unusedN. unfold ctr.getN.
                  by apply ndot_ne_disjoint.
                }
                assert (disjoint (A:=coPset) (↑ctr.unusedN) (↑frontendN)).
                {
                  unfold ctr.unusedN. unfold frontendN.
                  by apply ndot_ne_disjoint.
                }
                set_solver.
              } (* FIXME: more namespaces+set_solver. *)
              iMod (ctr.unused_own_val_false with "Hunusedinv1 Hunused Hval") as "HH".
              done.
            }
            iRight.
            assert (uint.Z epoch < uint.Z latestEpoch)%Z as Hineq2 by word.
            iDestruct (own_latest_epoch_get_lb with "Hlatest") as "#Hlb".
            iMod ("Hclose" with "[Hval Hlatest Hkv]").
            {
              iNext.
              iExists _, _. iFrame.
            }
            iModIntro.
            iApply (mono_nat_lb_own_le (n:=uint.nat latestEpoch)).
            { word. }
            iFrame "#".
          }
          iMod ("Hclose" with "[Hval Hlatest Hkv]").
          {
            iNext.
            iExists _, _. iFrame.
          }
          iModIntro.
          iDestruct "Hv" as (?) "[_ Hv]".
          iLeft. iExists _; iFrame "Hv".
        }
      }
      (* Now, prove the fupd for GetAtEpoch(). *)
      { (* Second linearization point *)
        iIntros "Hval2".
        iInv "Hinv1" as ">Hi" "Hclose".
        iNamed "Hi".
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros "Hmask".

        iDestruct "Hval2" as "[Hval2|#Hbad]"; last first.
        { (* case: the epoch number is stale already; this is impossible *)
          iDestruct (mono_nat_lb_own_valid with "HlatestEpoch Hbad") as "[%_ %Hineq]".
          iExists latestEpoch.
          iFrame.
          destruct (decide (uint.Z latestEpoch = uint.Z epoch)).
          { (* contradicts the fact that we're in the stale case *)
            exfalso.
            word.
          }
          iIntros "HlatestEpoch".
          iMod "Hmask".
          iMod ("Hclose" with "[Hkv Hval HlatestEpoch]").
          {
            iNext.
            iExists _, _.
            iFrame.
          }
          by iModIntro.
        }

        iDestruct "Hval2" as (v2) "Hval2".
        iExists latestEpoch.
        iFrame.
        destruct (decide (uint.Z latestEpoch = uint.Z epoch)).
        { (* e is the latest number seen by the ctr server (i.e. our request is not stale)*)
          replace (latestEpoch) with (epoch) by naive_solver.
          iDestruct (own_val_combine with "Hval2 Hval") as "[Hval %Hveq]".
          iModIntro.
          rewrite (Qp.quarter_quarter).
          iExists _; iFrame "Hval".
          iIntros "Hval".
          iModIntro.
          iIntros "Hlatest".
          iMod "Hmask".
          iEval (rewrite -Qp.quarter_quarter) in "Hval".
          iDestruct (own_val_split with "Hval") as "[Hval Hval2]".
          iDestruct (own_latest_epoch_get_lb with "Hlatest") as "#Hlb".
          iMod ("Hclose" with "[Hkv Hval2 Hlatest]").
          {
            iNext.
            iExists _, _.
            rewrite Hveq.
            iFrame.
          }
          iModIntro.
          iIntros "Hck".
          iExists _; iFrame "∗#".
          done.
        }
        { (* the server has a different number than e *)
          iIntros "Hlatest".
          iMod "Hmask".
          iMod ("Hclose" with "[Hval Hkv Hlatest]").
          {
            iNext.
            iExists _, _.
            iFrame.
          }
          iModIntro.
          done.
        }
      }
    }
    (* Done with Get() *)
    iIntros (gv) "HH".
    iDestruct "HH" as (v) "[%Hval HH]".
    rewrite Hval.
    iNamed "HH".
    wp_store.

    wp_load.
    wp_apply (std_proof.wp_SumAssumeNoOverflow).
    iIntros (Hno_overflow).

    (* Put(epoch, ret + 1) *)
    wp_loadField.
    wp_load.
    wp_loadField.

    wp_apply (ctr.wp_Clerk__Put γ.(ctr1_gn) with "Hck1_own").

    (* EnterNewEpoch *)
    iInv "Hinv1" as ">HH" "Hclose".
    iNamed "HH".
    iExists latestEpoch.
    iApply (fupd_mask_intro).
    {
      assert (disjoint (A:=coPset) (↑ctr.unusedN) (↑ctr.getN)).
      {
        unfold ctr.unusedN. unfold ctr.getN.
        by apply ndot_ne_disjoint.
      }
      assert (disjoint (A:=coPset) (↑ctr.unusedN) (↑frontendN)).
      {
        unfold ctr.unusedN. unfold frontendN.
        by apply ndot_ne_disjoint.
      }
      set_solver.
    }
    iIntros "Hmask".
    iDestruct (mono_nat_lb_own_valid with "HlatestEpoch Hlb") as %Hvalid.
    destruct (decide (uint.Z latestEpoch < uint.Z epoch)%Z) as [Hineq|Hineq].
    { (* case: server's first time seeing epoch; cannot be true *)
      exfalso.
      word.
    }

    iFrame.
    iIntros "Hlatest".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hkv Hval Hlatest]") as "_".
    {
      iNext.
      iExists _, _.
      iFrame.
    }
    iModIntro.

    (* PutAtEpoch *)
    iInv "Hinv1" as ">HH" "Hclose".
    clear latestEpoch Hineq Hvalid.
    iNamed "HH".
    iDestruct (own_latest_epoch_with_lb with "HlatestEpoch Hlb") as %Hineq.
    iExists _; iFrame.

    destruct (decide _).
    { (* case: epoch number is valid *)

      iMod "Hkvfupd".
      iDestruct "Hkvfupd" as (oldv) "[Hkv2 Hkvfupd]".

      unfold ctr.Put_core_spec.
      replace (latestEpoch) with (epoch) by word.
      iDestruct (own_val_combine with "Hval HepochVal") as "[Hval %Hveq]".
      rewrite dfrac_op_own Qp.quarter_quarter.
      rewrite Hveq.
      iExists _; iFrame.
      iModIntro.
      iModIntro.
      iIntros "HnewVal".
      iModIntro.
      iIntros "Hlatest".
      unfold kv_ptsto.
      iDestruct (ghost_map_points_to_agree with "Hkv2 Hkv") as %Hveq2.
      rewrite Hveq2.
      iCombine "Hkv Hkv2" as "Hkv".
      iMod (ghost_map_points_to_update (word.add v 1) with "Hkv") as "Hkv".
      iDestruct "Hkv" as "[Hkv Hkv2]".

      iSpecialize ("Hkvfupd" with "[]").
      {
        iPureIntro.
        word.
      }
      iMod ("Hkvfupd" with "Hkv2") as "Hkvfupd".
      iEval (rewrite -Qp.quarter_quarter) in "HnewVal".
      iDestruct (own_val_split with "HnewVal") as "[Hval Hval2]".
      iMod ("Hclose" with "[Hkv Hlatest Hval2]") as "_".
      {
        iNext.
        iExists _, _.
        iFrame.
      }
      iModIntro.
      iIntros "Hck1_own".
      wp_pures.
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlocked $HmuInv Hck1 Hck2 Hck2_own Hck1_own Hval Hghost2]").
      {
        iNext.
        iExists _, _, _.
        iFrame "∗#".
        iRight.
        iExists _; iFrame.
      }
      wp_pures.
      wp_load.
      iApply "HΦ".
      iFrame.
      done.
    }
    { (* case: epoch number is stale *)
      iApply (fupd_mask_intro).
      { set_solver. }
      iIntros "Hmask".
      iIntros "Hlatest".
      iMod "Hmask".
      iMod ("Hclose" with "[Hkv Hval Hlatest]") as "_".
      {
        iNext.
        iExists _, _.
        iFrame.
      }
      done.
    }
  }
  { (* same proof, but with second server *)
    assert (key = 1) by naive_solver.
    wp_loadField.
    wp_loadField.
    wp_bind (ctr.Clerk__Get _ _).
    wp_apply (wp_wand _ _ _
                (λ v,
              ∃ (v0:u64),
              ⌜v = #v0⌝ ∗
            "#Hlb" ∷ is_latest_epoch_lb γ.(ctr2_gn) epoch ∗
            "HepochVal" ∷ own_val γ.(ctr2_gn) epoch v0 q4 ∗
            "Hck2_own" ∷ ctr.own_Clerk γ.(ctr2_gn) ck2
                    )%I
               with "[Hck2_own Hghost2]").
    { (* ctr.Clerk__Get *)
      wp_apply (ctr.wp_Clerk__Get with "Hck2_own").
      iApply (ctr.EnterNewEpoch_spec_wand _ _ ((∃ v, own_val γ.(ctr2_gn) epoch v (1 / 4))
                                                    ∨ is_latest_epoch_lb_strict γ.(ctr2_gn) epoch
                                              ) with "[] [-]"); last first.
      { (* EnterNewEpoch(): first linearization point *)
        iInv "Hinv2" as ">Hown" "Hclose".
        iNamed "Hown".
        iApply fupd_mask_intro.
        {
          assert (disjoint (A:=coPset) (↑ctr.unusedN) (↑ctr.getN)).
          {
            unfold ctr.unusedN. unfold ctr.getN.
            by apply ndot_ne_disjoint.
          }
          assert (disjoint (A:=coPset) (↑ctr.unusedN) (↑frontendN)).
          {
            unfold ctr.unusedN. unfold frontendN.
            by apply ndot_ne_disjoint.
          }
          set_solver.
        }
        iIntros "Hmask".

        iExists latestEpoch.
        destruct (decide (uint.Z latestEpoch < uint.Z epoch)%Z) as [Hineq|Hineq].
        { (* case: epoch number is new *)
          iDestruct "Hghost2" as "[Hunused | Hbad]"; last first.
          { (* is_latest_epoch_lb contradicts inequality *)
            iDestruct "Hbad" as (?) "[#Hlb _]".
            iDestruct (mono_nat_lb_own_valid with "HlatestEpoch Hlb") as %Hvalid.
            exfalso. word.
          }
          iFrame.
          iIntros (v0) "HnewVal  HprevEpochVal  HlatestEpoch".
          iDestruct (own_val_combine with "Hval HprevEpochVal") as "[_ %Hagree]".
          rewrite Hagree.
          iMod "Hmask" as "_".
          iEval (rewrite -Qp.quarter_quarter) in "HnewVal".
          iDestruct (own_val_split with "HnewVal") as "[HnewVal HnewVal2]".
          iDestruct (mono_nat_lb_own_get with "HlatestEpoch") as "#Hlb". (* for doing the put *)
          iMod ("Hclose" with "[HlatestEpoch HnewVal Hkv]") as "_".
          {
            iNext.
            iExists _, _.
            iFrame.
          }
          iModIntro.
          iLeft.
          iExists _; iFrame.
        }
        { (* case: epoch number is not brand new *)
          iFrame.
          iIntros "Hlatest".
          iMod "Hmask".
          iDestruct "Hghost2" as "[Hunused|Hv]".
          { (* derive a contradiction with e == latestEpoch; the cast e <
               latestEpoch should require proving True, not proving Φ. We'll have to
               strengthen the spec for ctr *)
            destruct (decide (uint.Z latestEpoch = uint.Z epoch)).
            {
              replace (latestEpoch) with (epoch) by word.
              iMod (fupd_mask_subseteq (↑ctr.unusedN)).
              { (* TODO: this is a copy paste of the previous fupd_mask_intro. *)
                assert (disjoint (A:=coPset) (↑ctr.unusedN) (↑ctr.getN)).
                {
                  unfold ctr.unusedN. unfold ctr.getN.
                  by apply ndot_ne_disjoint.
                }
                assert (disjoint (A:=coPset) (↑ctr.unusedN) (↑frontendN)).
                {
                  unfold ctr.unusedN. unfold frontendN.
                  by apply ndot_ne_disjoint.
                }
                set_solver.
              } (* FIXME: more namespaces+set_solver. *)
              iMod (ctr.unused_own_val_false with "Hunusedinv2 Hunused Hval") as "HH".
              done.
            }
            iRight.
            assert (uint.Z epoch < uint.Z latestEpoch)%Z as Hineq2 by word.
            iDestruct (own_latest_epoch_get_lb with "Hlatest") as "#Hlb".
            iMod ("Hclose" with "[Hval Hlatest Hkv]").
            {
              iNext.
              iExists _, _. iFrame.
            }
            iModIntro.
            iApply (mono_nat_lb_own_le (n:=uint.nat latestEpoch)).
            { word. }
            iFrame "#".
          }
          iMod ("Hclose" with "[Hval Hlatest Hkv]").
          {
            iNext.
            iExists _, _. iFrame.
          }
          iModIntro.
          iDestruct "Hv" as (?) "[_ Hv]".
          iLeft. iExists _; iFrame "Hv".
        }
      }
      (* Now, prove the fupd for GetAtEpoch(). *)
      { (* Second linearization point *)
        iIntros "Hval2".
        iInv "Hinv2" as ">Hi" "Hclose".
        iNamed "Hi".
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros "Hmask".

        iDestruct "Hval2" as "[Hval2|#Hbad]"; last first.
        { (* case: the epoch number is stale already; this is impossible *)
          iDestruct (mono_nat_lb_own_valid with "HlatestEpoch Hbad") as "[%_ %Hineq]".
          iExists latestEpoch.
          iFrame.
          destruct (decide (uint.Z latestEpoch = uint.Z epoch)).
          { (* contradicts the fact that we're in the stale case *)
            exfalso.
            word.
          }
          iIntros "HlatestEpoch".
          iMod "Hmask".
          iMod ("Hclose" with "[Hkv Hval HlatestEpoch]").
          {
            iNext.
            iExists _, _.
            iFrame.
          }
          by iModIntro.
        }

        iDestruct "Hval2" as (v2) "Hval2".
        iExists latestEpoch.
        iFrame.
        destruct (decide (uint.Z latestEpoch = uint.Z epoch)).
        { (* e is the latest number seen by the ctr server (i.e. our request is not stale)*)
          replace (latestEpoch) with (epoch) by naive_solver.
          iDestruct (own_val_combine with "Hval2 Hval") as "[Hval %Hveq]".
          iModIntro.
          rewrite (Qp.quarter_quarter).
          iExists _; iFrame "Hval".
          iIntros "Hval".
          iModIntro.
          iIntros "Hlatest".
          iMod "Hmask".
          iEval (rewrite -Qp.quarter_quarter) in "Hval".
          iDestruct (own_val_split with "Hval") as "[Hval Hval2]".
          iDestruct (own_latest_epoch_get_lb with "Hlatest") as "#Hlb".
          iMod ("Hclose" with "[Hkv Hval2 Hlatest]").
          {
            iNext.
            iExists _, _.
            rewrite Hveq.
            iFrame.
          }
          iModIntro.
          iIntros "Hck".
          iExists _; iFrame "∗#".
          done.
        }
        { (* the server has a different number than e *)
          iIntros "Hlatest".
          iMod "Hmask".
          iMod ("Hclose" with "[Hval Hkv Hlatest]").
          {
            iNext.
            iExists _, _.
            iFrame.
          }
          iModIntro.
          done.
        }
      }
    }
    (* Done with Get() *)
    iIntros (gv) "HH".
    iDestruct "HH" as (v) "[%Hval HH]".
    rewrite Hval.
    iNamed "HH".
    wp_store.

    (* overflow assumption *)
    wp_load.
    wp_apply (std_proof.wp_SumAssumeNoOverflow).
    iIntros (Hno_overflow).

    (* Put(epoch, ret + 1) *)
    wp_loadField.
    wp_load.
    wp_loadField.

    wp_apply (ctr.wp_Clerk__Put γ.(ctr2_gn) with "Hck2_own").

    (* EnterNewEpoch *)
    iInv "Hinv2" as ">HH" "Hclose".
    iNamed "HH".
    iExists latestEpoch.
    iApply (fupd_mask_intro).
    {
      assert (disjoint (A:=coPset) (↑ctr.unusedN) (↑ctr.getN)).
      {
        unfold ctr.unusedN. unfold ctr.getN.
        by apply ndot_ne_disjoint.
      }
      assert (disjoint (A:=coPset) (↑ctr.unusedN) (↑frontendN)).
      {
        unfold ctr.unusedN. unfold frontendN.
        by apply ndot_ne_disjoint.
      }
      set_solver.
    }
    iIntros "Hmask".
    iDestruct (mono_nat_lb_own_valid with "HlatestEpoch Hlb") as %Hvalid.
    destruct (decide (uint.Z latestEpoch < uint.Z epoch)%Z) as [Hineq|Hineq].
    { (* case: server's first time seeing epoch; cannot be true *)
      exfalso.
      word.
    }

    iFrame.
    iIntros "Hlatest".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hkv Hval Hlatest]") as "_".
    {
      iNext.
      iExists _, _.
      iFrame.
    }
    iModIntro.

    (* PutAtEpoch *)
    iInv "Hinv2" as ">HH" "Hclose".
    clear latestEpoch Hineq Hvalid.
    iNamed "HH".
    iDestruct (own_latest_epoch_with_lb with "HlatestEpoch Hlb") as %Hineq.
    iExists _; iFrame.

    destruct (decide _).
    { (* case: epoch number is valid *)

      iMod "Hkvfupd".
      iDestruct "Hkvfupd" as (oldv) "[Hkv2 Hkvfupd]".

      unfold ctr.Put_core_spec.
      replace (latestEpoch) with (epoch) by word.
      iDestruct (own_val_combine with "Hval HepochVal") as "[Hval %Hveq]".
      rewrite dfrac_op_own Qp.quarter_quarter.
      rewrite Hveq.
      iExists _; iFrame.
      iModIntro.
      iModIntro.
      iIntros "HnewVal".
      iModIntro.
      iIntros "Hlatest".
      unfold kv_ptsto.
      rewrite H.
      iDestruct (ghost_map_points_to_agree with "Hkv2 Hkv") as %Hveq2.
      rewrite Hveq2.
      iCombine "Hkv Hkv2" as "Hkv".
      iMod (ghost_map_points_to_update (word.add v 1) with "Hkv") as "Hkv".
      iDestruct "Hkv" as "[Hkv Hkv2]".

      iSpecialize ("Hkvfupd" with "[]").
      { word. }
      iMod ("Hkvfupd" with "Hkv2") as "Hkvfupd".
      iEval (rewrite -Qp.quarter_quarter) in "HnewVal".
      iDestruct (own_val_split with "HnewVal") as "[Hval Hval2]".
      iMod ("Hclose" with "[Hkv Hlatest Hval2]") as "_".
      {
        iNext.
        iExists _, _.
        iFrame.
      }
      iModIntro.
      iIntros "Hck2_own".
      wp_pures.
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlocked $HmuInv Hck1 Hck2 Hck2_own Hck1_own Hval Hghost1]").
      {
        iNext.
        iExists _, _, _.
        iFrame "∗#".
        iRight.
        iExists _; iFrame.
      }
      wp_pures.
      wp_load.
      iApply "HΦ".
      iFrame.
      done.
    }
    { (* case: epoch number is stale *)
      iApply (fupd_mask_intro).
      { set_solver. }
      iIntros "Hmask".
      iIntros "Hlatest".
      iMod "Hmask".
      iMod ("Hclose" with "[Hkv Hval Hlatest]") as "_".
      {
        iNext.
        iExists _, _.
        iFrame.
      }
      done.
    }
  }
Qed.

(* TaDa-style spec *)
Program Definition FAISpec_tada γ :=
  λ reqData, λne (Φ : list u8 -d> iPropO Σ),
  (∃ k, ⌜k = 0 ∨ k = 1⌝ ∗ ⌜has_encoding reqData [EncUInt64 k]⌝ ∗
      |={⊤∖↑frontendN,∅}=> ∃ v, kv_ptsto γ.(kv_gn) k v ∗
        (⌜uint.nat v < uint.nat (word.add v (W64 1))⌝ -∗ kv_ptsto γ.(kv_gn) k (word.add v 1) ={∅,⊤∖↑frontendN}=∗
                (∀ l, ⌜has_encoding l [EncUInt64 v]⌝ -∗ Φ l))
    )%I
.
Next Obligation.
  solve_proper.
Defined.

Definition is_host γ host : iProp Σ :=
  is_urpc_dom γ.(urpc_gn) {[ (W64 0) ]} ∗
  is_urpc_spec_pred γ.(urpc_gn) host 0 (FAISpec_tada γ).

Lemma wp_StartServer γ γcfg (me configHost host1 host2:u64) :
  config.is_host γcfg configHost (λ e, own_unused_epoch γ.(ctr1_gn) e ∗ own_unused_epoch γ.(ctr2_gn) e) (λ _, True) -∗
  ctr.is_host host1 γ.(ctr1_gn) -∗
  ctr.is_host host2 γ.(ctr2_gn) -∗
  is_host γ me -∗
  frontend_inv γ -∗
  {{{
      True
  }}}
    frontend.StartServer #me #configHost #host1 #host2
  {{{
        RET #(); True
  }}}.
Proof using Type*.
  iIntros "#His_cfg #His_host1 #His_host2 #His_host #Hinv !#" (Φ) "Hpre HΦ".
  Opaque frontend.Server. (* FIXME: why do I need this? *)
  wp_rec.
  wp_pures.
  wp_apply (wp_allocStruct).
  { apply zero_val_ty'. Transparent Server. unfold Server. done. }
  Opaque frontend.Server.
  iIntros (s) "Hs".
  wp_pures.
  wp_apply (config.wp_MakeClerk with "His_cfg").
  iIntros (ck) "#His_ck".
  wp_pures.
  wp_apply (config.wp_Clerk__AcquireEpoch with "His_ck").
  { auto. }
  iIntros (epoch) "Hunused".

  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH".
  simpl.
  wp_storeField.
  wp_apply (wp_new_free_lock).
  iIntros (mu) "HmuInv".
  wp_storeField.

  wp_apply (ctr.wp_MakeClerk with "His_host1").
  iIntros (ck1) "Hck1_own".
  wp_storeField.

  wp_apply (ctr.wp_MakeClerk with "His_host2").
  iIntros (ck2) "Hck2_own".
  wp_storeField.

  iAssert (|={⊤}=> is_Server s γ)%I with "[HmuInv mu ck1 ck2 epoch Hck1_own Hck2_own Hunused]" as ">#His_srv".
  {
    unfold is_Server.
    iMod (readonly_alloc_1 with "mu") as "#Hmu".
    iMod (readonly_alloc_1 with "epoch") as "#Hepoch".
    iExists _; iFrame "∗#".
    iApply (alloc_lock with "HmuInv").
    iNext.
    iExists _.
    iExists _, _.
    iFrame "ck1 ck2 ∗#".
    iDestruct "Hunused" as "[$ $]".
  }

  wp_apply (map.wp_NewMap u64).
  iIntros (handlers) "Hhandlers".

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.
  wp_apply (wp_MakeServer with "Hhandlers").
  iIntros (r) "Hr".
  wp_pures.
  wp_apply (wp_StartServer_pred with "[$Hr]").
  { set_solver by idtac. (* FIXME regular set_solver leaves shelved goals *) }
  {
    iDestruct "His_host" as "[H1 H2]".
    unfold handlers_complete.
    rewrite dom_insert_L.
    rewrite dom_empty_L.
    iSplitL "".
    {
      iExactEq "H1".
      f_equal.
      set_solver.
    }
    iApply (big_sepM_insert_2 with "").
    {
      simpl. iExists _; iFrame "#".
      clear Φ.
      rewrite /is_urpc_handler_pred.
      iIntros (????) "!#".
      iIntros (Φ) "Hpre HΦ".
      iDestruct "Hpre" as "(Hreq_sl & Hrep & HFAISpec)".
      wp_pures.
      iDestruct "HFAISpec" as (k) "(%H01 & %Henc & Hfupd)".
      wp_apply (wp_new_dec with "Hreq_sl").
      { done. }
      iIntros (dec) "Hdec".
      wp_pures.
      wp_apply (wp_new_enc).
      iIntros (enc) "Henc".
      wp_pures.
      wp_apply (wp_Dec__GetInt with "Hdec").
      iIntros "_".

      wp_apply (wp_FetchAndIncrement with "His_srv Hinv [$Hfupd]").
      { naive_solver. }
      iIntros (v) "HPost".
      wp_apply (wp_Enc__PutInt with "Henc").
      { done. }
      iIntros "Henc".
      wp_pures.
      wp_apply (wp_Enc__Finish with "Henc").
      iIntros (rep_sl rep_data) "(%Hrep_enc & %Hrep_len & Hrep_sl)".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_small".
      wp_store.
      iApply "HΦ".
      iModIntro.
      iFrame.
      iApply "HPost".
      done.
    }
    by iApply big_sepM_empty.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

Definition is_Clerk γ ck : iProp Σ :=
  ∃ (cl:loc) (host:chan),
  "#Hcl" ∷ readonly (ck ↦[frontend.Clerk :: "cl"] #cl) ∗
  "#Hcl_is" ∷ is_uRPCClient cl host ∗
  "#His_host" ∷ is_host γ host
  .

Lemma wp_MakeClerk γ (host:u64) :
  is_host γ host -∗
  {{{
        True
  }}}
    MakeClerk #host
  {{{
        (ck:loc), RET #ck; is_Clerk γ ck
  }}}
.
Proof.
  iIntros "#Hhost !#" (Φ) "_ HΦ".
  wp_rec. wp_pures.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (ck) "Hck".
  iDestruct (struct_fields_split with "Hck") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply (wp_MakeClient).
  iIntros (cl) "#Hcl_is".
  wp_storeField.
  iMod (readonly_alloc_1 with "cl") as "#Hcl".
  iApply "HΦ".
  iExists _, _.
  iFrame "#".
  done.
Qed.

Lemma wp_Clerk__FetchAndIncrement ck (key:u64) γ (ret_ptr:loc) Φ ret_placeholder :
key = 0 ∨ key = 1 →
  is_Clerk γ ck -∗
  ret_ptr ↦[uint64T] #ret_placeholder -∗
  □ (|={⊤∖↑frontendN,∅}=> ∃ v, kv_ptsto γ.(kv_gn) key v ∗
      (⌜uint.nat v < uint.nat (word.add v (W64 1))⌝ -∗ kv_ptsto γ.(kv_gn) key (word.add v 1)
       ={∅,⊤∖↑frontendN}=∗ (ret_ptr ↦[uint64T] #v -∗ Φ #0))) -∗
  □ (∀ (err:u64), ⌜err ≠ 0⌝ -∗ (ret_ptr ↦[uint64T] #ret_placeholder) -∗ Φ #err) -∗
  WP Clerk__FetchAndIncrement #ck #key #ret_ptr {{ Φ }}
.
Proof.
  intros Hkey.
  iIntros "#Hck_is Hret_ptr #HΦ1 #HΦ2".
  wp_rec. wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (reply_ptr) "Hreply_ptr".
  wp_pures.

  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc").
  { done. }
  iIntros "Henc".
  wp_pures.

  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (req_sl reqData) "(%HreqEnc & %HreqLen & Hreq_sl)".

  iNamed "Hck_is".
  wp_loadField.

  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_small".
  wp_apply (wp_Client__Call_pred with "[$Hreply_ptr $Hreq_small Hcl_is]").
  {
    iFrame "#".
    iDestruct "His_host" as "[_ $]".
    iModIntro.
    iNext.
    simpl.
    iExists (uint.nat key).
    iSplitL "".
    {
      iPureIntro.
      naive_solver.
    }
    simpl in HreqEnc.
    iSplitL "".
    {
      iPureIntro.
      naive_solver.
    }
    replace (W64 (uint.nat key)) with (key) by word.
    iMod "HΦ1".
    iModIntro.
    iDestruct "HΦ1" as (?) "[Hkv HΦ1]".
    iExists _; iFrame.
    iIntros "H1 H2".
    iMod ("HΦ1" with "H1 H2") as "HΦ1".
    iModIntro.
    iIntros.
    instantiate (1:=(λ l, ∃ v, ⌜has_encoding l [EncUInt64 v]⌝ ∗ (ret_ptr ↦[uint64T] #v -∗ Φ #0))%I).
    simpl.
    iExists _; iFrame.
    done.
  }
  iIntros (err) "(Hreq_small & Hpost)".
  wp_pures.

  destruct err.
  { (* urpc error *)
    rewrite bool_decide_false; last by destruct c.
    wp_pures.
    iModIntro.
    iApply "HΦ2".
    {
      iPureIntro.
      by destruct c.
    }
    {
      iFrame.
    }
  }
  (* got a reply *)
  wp_pures.

  iDestruct "Hpost" as (??) "(Hreply & Hreply_small & Hpost)".
  wp_load.
  iDestruct "Hpost" as (?) "[%HrepEnc Hpost]".
  wp_apply (wp_new_dec with "[$Hreply_small]").
  { done. }
  iIntros (dec) "Hdec".
  wp_pures.
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  iNamed "Hret_ptr".
  wp_store.
  iApply "Hpost".
  iFrame.
  done.
Qed.

End frontend_proof.
End frontend.
