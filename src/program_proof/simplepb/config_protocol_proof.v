From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export admin.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb Require Export config_proof pb_definitions pb_protocol primary_protocol.

Section config_global.

Context {pb_record:Sm.t}.
Notation pbG := (pbG (pb_record:=pb_record)).
Notation OpType := (Sm.OpType pb_record).

Context `{!gooseGlobalGS Σ}.
Context `{!pbG Σ}.

Definition configN := nroot .@ "config".

(* before calling this lemma, have to already allocate pb ghost state *)
Lemma config_ghost_init_2 γ conf confγs :
  ([∗ list] γsrv ; host ∈ confγs ; conf, is_pb_host host γ γsrv) -∗
  pb_init_config γ.(s_pb) (r_pb <$> confγs)
  ={⊤}=∗ ∃ γconf, is_conf_inv γ γconf ∗ makeConfigServer_pre γconf conf.
Proof.
  iIntros "#Hhosts Hinitconf".
  iMod (config_ghost_init conf) as (γconf) "(Hconfpre & Hepoch & Hconf)".
  iExists _; iFrame "Hconfpre".
  iMod (inv_alloc with "[-]") as "$"; last done.
  iNext.
  iExists (U64 0), conf, confγs, (U64 0).
  iFrame.
  iNamed "Hinitconf".
  iFrame "∗#%".
  (*
  iSplitL.
  { iRight. done. }
  iIntros (???).
  exfalso.
  word. *)
Admitted.

End config_global.

Section pb_config_proof.

Context {pb_record:Sm.t}.
Notation pbG := (pbG (pb_record:=pb_record)).
Notation OpType := (Sm.OpType pb_record).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).

Context `{!heapGS Σ}.
Context `{!pbG Σ}.

Definition is_conf_host confHost γ : iProp Σ :=
  ∃ γconf,
  config_proof.is_host confHost γconf ∗ is_conf_inv γ γconf.

Definition is_Clerk2 ck γ : iProp Σ :=
  ∃ γconf,
    "#Hinv" ∷ is_conf_inv γ γconf ∗
    "#Hck" ∷ config_proof.is_Clerk ck γconf.

Lemma wp_MakeClerk2 (configHost:u64) γ :
  {{{
        is_conf_host configHost γ
  }}}
    config.MakeClerk #configHost
  {{{
      ck, RET #ck; is_Clerk2 ck γ
  }}}.
Proof.
  iIntros (Φ) "#Hhost HΦ".
  iDestruct "Hhost" as (?) "[Hhost Hinv]".
  wp_apply (config_proof.wp_MakeClerk with "[$Hhost]").
  iIntros.
  iApply "HΦ".
  iExists  _; iFrame "#".
Qed.

Lemma wp_Clerk__GetConfig2 ck γ Φ :
  is_Clerk2 ck γ -∗
  □(∀ confγs (conf:list u64) config_sl,
  (is_slice_small config_sl uint64T 1 conf ∗
  ([∗ list] γsrv ; host ∈ confγs ; conf, is_pb_host host γ γsrv) -∗
   Φ (slice_val config_sl)%V
  )) -∗
  WP config.Clerk__GetConfig #ck {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  iNamed "Hck".
  wp_apply (wp_Clerk__GetConfig with "[$Hck]").
  iModIntro.
  iIntros "Hlc".
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iNamed "Hi".
  iExists _.
  iFrame.
  iIntros "Hconfig".
  iMod "Hmask".
  iMod ("Hclose" with "[-]").
  {
    iNext. iExists _, _, _, _.
    iFrame "∗#%".
  }
  iModIntro.
  iIntros (?) "Hconf".
  iApply "HΦ".
  iFrame "∗#".
Qed.

Lemma wp_Clerk__GetEpochAndConfig2 ck γ Φ :
  is_Clerk2 ck γ -∗
  □((∀ (epoch epoch_lb:u64) confγs (conf:list u64) config_sl,
  (is_slice_small config_sl uint64T 1 conf ∗
  config_proposal_unset γ.(s_pb) epoch ∗
  own_proposal_unused γ.(s_pb) epoch ∗
  own_init_proposal_unused γ.(s_prim) epoch ∗
  is_epoch_config γ.(s_pb) epoch_lb (r_pb <$> confγs) ∗
  (∀ epoch_skip, ⌜int.nat epoch_lb < int.nat epoch_skip⌝ → ⌜int.nat epoch_skip < int.nat epoch⌝ → is_epoch_skipped γ.(s_pb) epoch_skip) ∗
  ([∗ list] γsrv ; host ∈ confγs; conf, is_pb_host host γ γsrv) ∗
  (∀ γsrv, ⌜γsrv ∈ (r_pb <$> confγs)⌝ → is_epoch_lb γsrv epoch_lb)) -∗
   Φ (#0, #epoch, slice_val config_sl)%V
  ) ∧ (∀ (err:u64) sl, ⌜err ≠ 0⌝ -∗ Φ (#err, #0, slice_val sl)%V))
  -∗
  WP config.Clerk__GetEpochAndConfig #ck {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  iNamed "Hck".
  wp_apply (wp_Clerk__GetEpochAndConfig with "[$Hck]").
  iModIntro.
  iIntros "Hlc".
  iSplit.
  {
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iNamed "Hi".
    iExists _, _.
    iFrame.
    iIntros "%Hno_overflow Hepoch Hconf".
    iMod "Hmask".

    (* Hunset becomes skipped, and the first unused becomes unset. *)
    iDestruct (big_sepS_elem_of_acc_impl (word.add epoch (U64 1)) with "Hunused") as "[Hunset_new Hunused]".
    { set_solver. }

    iSpecialize ("Hunset_new" with "[]").
    { done. }
    iDestruct "Hunset_new" as "(Hunset_new & Hunset_new2 & Hprop)".

    iDestruct "Hunset_or_set" as "[Hunset|%Hset]".
    {
      iMod (own_update with "Hunset") as "Hskip1".
      {
        apply singleton_update.
        apply dfrac_agree_persist.
      }
      iDestruct "Hskip1" as "#Hskip1".

      iMod ("Hclose" with "[Hunset_new2 Hunused Hepoch Hconf]").
      {
        iNext. iExists _, _, _, _.
        iFrame "Hepoch Hconf His_conf ∗#".
        iSplitL "Hunused".
        {
          iApply "Hunused".
          {
            iModIntro.
            iIntros (???) "H". iIntros.
            iApply "H".
            iPureIntro.
            word.
          }
          {
            iIntros. exfalso. word.
          }
        }
        iIntros (???).
        assert (int.nat epoch_skip = int.nat epoch ∨ int.nat epoch_skip < int.nat epoch ∨ int.nat epoch_skip >= int.nat (word.add epoch (U64 1))) as Hineq.
        { word. }
        destruct Hineq as [Heq|[Hineq|Hineq]].
        {
          replace (epoch_skip) with (epoch) by word.
          iFrame "Hskip1".
        }
        {
          iApply "His_skip".
          { done. }
          { done. }
        }
        { exfalso. word. }
      }
      iModIntro.
      iIntros.
      iApply "HΦ".
      iDestruct "Hprop" as "[$ $]".
      iFrame "∗ His_conf #".

      (* TODO: repetetive proof *)
      iIntros.
      assert (int.nat epoch_skip = int.nat epoch ∨ int.nat epoch_skip < int.nat epoch ∨ int.nat epoch_skip >= int.nat (word.add epoch (U64 1))) as Hineq.
      { word. }
      destruct Hineq as [Heq|[Hineq|Hineq]].
      {
        replace (epoch_skip) with (epoch) by word.
        iFrame "Hskip1".
      }
      {
        iApply "His_skip".
        { done. }
        { done. }
      }
      { exfalso. word. }
    }
    {
      iClear "His_skip".

      iMod ("Hclose" with "[Hunset_new2 Hunused Hepoch Hconf]").
      {
        iNext. iExists _, _, _, _.
        iFrame "∗ His_conf #".
        iSplitL "Hunused".
        {
          iApply "Hunused".
          {
            iModIntro.
            iIntros (???) "H". iIntros.
            iApply "H".
            iPureIntro.
            word.
          }
          {
            iIntros. exfalso. word.
          }
        }
        iIntros (???).
        exfalso.
        rewrite Hset in H.
        replace (int.nat (word.add epoch 1%Z)) with (int.nat epoch + 1) in H0 by word.
        word.
      }
      iModIntro.
      iIntros.
      iApply "HΦ".
      iDestruct "Hprop" as "[$ $]".
      iFrame "∗ His_conf #".
      iIntros (???).
      exfalso.
      rewrite Hset in H.
      replace (int.nat (word.add epoch 1%Z)) with (int.nat epoch + 1) in H0 by word.
      word.
    }
  }
  {
    iRight in "HΦ".
    iIntros.
    by iApply "HΦ".
  }
Qed.

Lemma wp_Clerk__WriteConfig2 ck γ Φ config_sl conf confγ epoch :
  is_Clerk2 ck γ -∗
  is_slice_small config_sl uint64T 1 conf -∗
  is_epoch_config_proposal γ.(s_pb) epoch (r_pb <$> confγ) -∗
  ([∗ list] γsrv ; host ∈ confγ ; conf, is_pb_host host γ γsrv) -∗
  (∀ γsrv, ⌜γsrv ∈ (r_pb <$> confγ)⌝ → is_epoch_lb γsrv epoch) -∗
  □ (∀ (err:u64),
      (if (decide (err = U64 0)) then
        is_epoch_config γ.(s_pb) epoch (r_pb <$> confγ)
      else
        True) -∗
      is_slice_small config_sl uint64T 1 conf -∗
      Φ #err)
  -∗
  WP config.Clerk__WriteConfig #ck #epoch (slice_val config_sl) {{ Φ }}
.
Proof.
  iIntros "#Hck Hsl #Hconf_prop #Hhosts #Hlbs #HΦ".
  iNamed "Hck".
  wp_apply (wp_Clerk__WriteConfig with "Hck Hsl"); last first.
  {
    iIntros.
    iApply ("HΦ" with "[] [$]").
    destruct (decide _).
    { exfalso. done. }
    done.
  }
  iModIntro.
  iIntros "Hlc".
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iApply fupd_mask_intro.
  {
    enough (↑epochLeaseN ## (↑configN:coPset)) by set_solver.
    by apply ndot_ne_disjoint.
  }
  iIntros "Hmask".
  iNamed "Hi".
  iExists _.
  iFrame "∗".
  destruct (decide (_)); last first.
  { (* write failed because of stale epoch. *)
    iIntros "Hepoch".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hepoch Hconf Hunused Hunset_or_set]").
    {
      iNext.  iExists _, _, _, _.
      iFrame "∗ His_conf #".
    }
    iModIntro.
    iIntros (??) "Hsl".
    wp_pures.
    iApply ("HΦ" with "[] Hsl").
    destruct (decide (_)).
    { exfalso. done. }
    done.
  }
  { (* successful write *)
    rewrite e.
    iExists _.
    iFrame.
    iIntros "Hconf Hepoch".
    iMod "Hmask" as "_".

    iDestruct "Hunset_or_set" as "[Hunset|%Hset]"; last first.
    { (* config was already set before *)
      replace (epoch) with (epoch_lb) by word.
      iDestruct "Hconf_prop" as "[Hconf_prop %Hle]".
      iDestruct "His_conf" as "(? & His_conf_prop & ?)".
      iDestruct (own_valid_2 with "His_conf_prop Hconf_prop") as %Hvalid.
      rewrite singleton_op in Hvalid.
      rewrite singleton_valid in Hvalid.
      rewrite dfrac_agree_op_valid in Hvalid.
      replace (r_pb <$> confγs) with (r_pb <$> confγ) in * by naive_solver.

      iMod ("Hclose" with "[Hepoch Hconf Hunused]").
      {
        iNext.  iExists _, _, _, _.
        iFrame "Hhosts ∗#".
        by iRight.
      }
      iApply "HΦ".
      iModIntro.
      iFrame "#".
    }
    { (* config is being set for the first time *)
      iMod (own_update with "Hunset") as "Hset".
      {
        apply singleton_update.
        apply cmra_update_exclusive.
        instantiate (1:=(to_dfrac_agree (DfracOwn 1) ((Some (r_pb <$> confγ)) : (leibnizO _)))).
        done.
      }
      iMod (own_update with "Hset") as "Hset".
      { apply singleton_update. apply dfrac_agree_persist. }
      iDestruct "Hset" as "#Hset".
      iMod ("Hclose" with "[Hconf Hepoch Hunused]").
      {
        iNext. iExists _, _, _, _.
        iFrame "∗ Hset #".
        iDestruct "Hconf_prop" as "[_ %Hineq]".
        iSplitL.
        { by iRight. }
        iIntros (???).
        exfalso.
        word.
      }
      iApply "HΦ".
      by iFrame "Hconf_prop Hset".
    }
  }
Qed.

End pb_config_proof.
