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

Local Definition q2 := (1/2)%Qp.
Local Definition q4 := (1/4)%Qp.

Definition k0 := (U64 0).
Definition k1 := (U64 1).

Context `{!ctrG Σ}.
Context `{!urpcregG Σ}.

Definition kv_ptsto (γ:gname) (k v:u64) : iProp Σ :=
  k ⤳[γ]{# 1/2} v.

Context `{γkv:gname}.

Definition frontend_inv_def γ: iProp Σ :=
  ∃ (latestEpoch v:u64),
  "HlatestEpoch" ∷ own_latest_epoch γ latestEpoch q2 ∗
  "Hval" ∷ own_val γ latestEpoch v q4 ∗
  "Hkv" ∷ kv_ptsto γkv k0 v.

Definition own_Server (s:loc) γ (epoch:u64) : iProp Σ :=
  ∃ (ck1 ck2:loc),
  "#Hepoch" ∷ readonly (s ↦[frontend.Server :: "epoch"] #epoch) ∗
  "Hck1" ∷ s ↦[frontend.Server :: "ck1"] #ck1 ∗
  "Hck2" ∷ s ↦[frontend.Server :: "ck2"] #ck2 ∗
  "Hck1_own" ∷ ctr.own_Clerk γ ck1 ∗
  "Hck2_own" ∷ ctr.own_Clerk γ ck2 ∗

  "Hghost1" ∷ (own_unused_epoch γ epoch ∨ (∃ v, is_latest_epoch_lb γ epoch ∗ own_val γ epoch v q4)).
  (* TODO: add second value *)

Definition frontendN := nroot .@ "frontend".

Definition is_Server s γ : iProp Σ :=
  ∃ mu,
  "Hmu" ∷ readonly (s ↦[frontend.Server :: "mu"] mu) ∗
  "HmuInv" ∷ is_lock frontendN mu (∃ epoch, own_Server s γ epoch)
.

Definition frontend_inv γ : iProp Σ :=
  inv frontendN (frontend_inv_def γ).

Lemma wp_FetchAndIncrement (s:loc) γ (key:u64) Q :
  key = 0 ∨ key = 1 →
  is_Server s γ -∗
  frontend_inv γ -∗
  {{{
        |={⊤∖↑frontendN,∅}=> ∃ v, kv_ptsto γkv key v ∗ (kv_ptsto γkv key (word.add v 1) ={∅,⊤∖↑frontendN}=∗ Q v)
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
            "Hck1_own" ∷ ctr.own_Clerk γ ck1
                    )%I
               with "[Hck1_own Hghost1]").
    {
      wp_apply (ctr.wp_Clerk__Get with "Hck1_own").
      iInv "Hinv" as ">Hown" "Hclose".
      iNamed "Hown".
      iApply fupd_mask_intro.
      { unfold ctr.ctrN. unfold frontendN.
        (* FIXME: just a pure inequality of sets; set_solver. *)
        admit.
      }
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
        iIntros (v0) "HnewVal  HprevEpochVal  HlatestEpoch".
        iDestruct (own_val_combine with "Hval HprevEpochVal") as "[_ %Hagree]".
        rewrite Hagree.
        iMod "Hmask" as "_".
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
        (* TODO: have to re-open and close the invariant for the second linearization point *)
        (*
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

    wp_apply (ctr.wp_Clerk__Put γ with "Hck1_own").
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
  } *)
Admitted.

(* TaDa-style spec *)
Program Definition FAISpec_tada (γ:gname) :=
  λ reqData, λne (Φ : list u8 -d> iPropO Σ),
  (∃ k, ⌜k = 0 ∨ k = 1⌝ ∗ ⌜has_encoding reqData [EncUInt64 k]⌝ ∗
       |={⊤∖↑frontendN,∅}=> ∃ v, kv_ptsto γ k v ∗
                      (kv_ptsto γ k (word.add v 1) ={∅,⊤∖↑frontendN}=∗ (∀ l, ⌜has_encoding l [EncUInt64 v]⌝ -∗ Φ l))
    )%I
.
Next Obligation.
  solve_proper.
Defined.

Definition is_host γurpc_gn γ host : iProp Σ :=
  handlers_dom γurpc_gn {[ (U64 0) ]} ∗
  handler_spec γurpc_gn host 0 (FAISpec_tada γ).

Lemma wp_StartServer γurpc_gn γ γcfg (me configHost host1 host2:u64) :
  config.is_host γcfg configHost (own_unused_epoch γ) (λ _, True) -∗
  is_host γurpc_gn γkv me -∗
  frontend_inv γ -∗
  {{{
      True
  }}}
    frontend.StartServer #me #configHost #host1 #host2
  {{{
        RET #(); True
  }}}.
Proof.
  iIntros "#His_cfg #His_host #Hinv !#" (Φ) "Hpre HΦ".
  Opaque frontend.Server. (* FIXME: why do I need this? *)
  wp_lam.
  wp_pures.
  wp_apply (wp_allocStruct).
  { apply zero_val_ty'. Transparent Server. unfold Server. done. }
  Opaque frontend.Server.
  iIntros (s) "Hs".
  wp_pures.
  wp_apply (config.wp_MakeClerk with "His_cfg").
  iIntros (ck) "#His_ck".
  wp_pures.
  wp_apply (config.wp_Clerk__AcquireEpoch with "His_cfg His_ck").
  { auto. }
  iIntros (epoch) "Hunused".

  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH".
  simpl.
  wp_storeField.
  wp_apply (wp_new_free_lock).
  iIntros (mu) "HmuInv".
  wp_storeField.

  wp_apply (ctr.wp_MakeClerk).
  iIntros (ck1) "Hck1_own".
  wp_storeField.

  wp_apply (ctr.wp_MakeClerk).
  iIntros (ck2) "Hck2_own".
  wp_storeField.

  iAssert (|={⊤}=> is_Server s γ)%I with "[HmuInv mu ck1 ck2 epoch Hck1_own Hck2_own Hunused]" as ">#His_srv".
  {
    unfold is_Server.
    iMod (readonly_alloc_1 with "mu") as "#Hmu".
    iMod (readonly_alloc_1 with "epoch") as "#Hepoch".
    iExists _; iFrame "#∗".
    iApply (alloc_lock with "HmuInv").
    iNext.
    iExists _.
    iExists _, _.
    iFrame "ck1 ck2 #∗".
  }

  wp_apply (map.wp_NewMap).
  iIntros (handlers) "Hhandlers".

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.
  wp_apply (wp_MakeServer with "Hhandlers").
  iIntros (r) "Hr".
  wp_pures.
  wp_apply (wp_StartServer γurpc_gn with "[$Hr]").
  { set_solver. }
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
      rewrite /impl_handler_spec.
      iIntros (??????) "!#".
      iIntros (Φ) "Hpre HΦ".
      iDestruct "Hpre" as "(Hreq_sl & Hrep & Hrep_sl & HFAISpec)".
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
      iClear "Hrep_sl".
      iIntros (rep_sl rep_data) "(%Hrep_enc & %Hrep_len & Hrep_sl)".
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_small".
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

End frontend_proof.
End frontend.
