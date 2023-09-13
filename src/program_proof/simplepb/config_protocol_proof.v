From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export admin.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb Require Export config_proof pb_definitions
     pb_protocol primary_protocol.

Section config_global.

Context {params:pbParams.t}.
Import pbParams.
Notation OpType := (Sm.OpType pb_record).

Context `{!gooseGlobalGS Σ}.
Context `{!pbG Σ}.

Definition configN := nroot .@ "config".

Definition is_pb_config_host confHost γ : iProp Σ :=
  ∃ γconf,
  "#Hhost" ∷ is_config_host confHost γconf ∗
  "#HconfInv" ∷ is_conf_inv γ γconf ∗
  "#HprophRead" ∷ is_proph_read_inv γ
.

(* before calling this lemma, have to already allocate pb ghost state *)
Lemma alloc_pb_config_ghost γ conf confγs :
  ([∗ list] γsrv ; host ∈ confγs ; conf, is_pb_host host γ γsrv) -∗
  pb_init_for_config γ.(s_pb) (r_pb <$> confγs) -∗
  primary_init_for_config γ.(s_prim)
  ={⊤}=∗ ∃ γconf, is_conf_inv γ γconf ∗ makeConfigServer_pre γconf conf.
Proof.
  iIntros "#Hhosts Hinitconf HprimInit".
  iMod (config_ghost_init conf) as (γconf) "(Hconfpre & Hepoch & Hres & Hconf)".
  iExists _; iFrame "Hconfpre".
  iMod (inv_alloc with "[-]") as "$"; last done.
  iNext.
  iExists (U64 0), (U64 0), conf, confγs.
  iFrame.
  iNamed "Hinitconf".
  iFrame "His_conf ∗#%".
  unfold primary_init_for_config.
  iSplitR; first done.
  iSplitL.
  { iApply (big_sepS_impl with "[Hunused HprimInit]").
    { iApply (big_sepS_sep with "[$Hunused $HprimInit]"). }
    iModIntro.
    iIntros (??) "[H1 H2] %".
    iSpecialize ("H1" with "[//]").
    iSpecialize ("H2" with "[//]").
    iFrame.
  }
  iSplitR.
  { by iRight. }
  iIntros (???). exfalso. word.
Qed.

End config_global.

Section pb_config_proof.

Context {params:pbParams.t}.
Import pbParams.
Notation OpType := (Sm.OpType pb_record).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).

Context `{!heapGS Σ}.
Context `{!pbG Σ}.

Definition is_Clerk2 ck γ γconf : iProp Σ :=
    "#Hinv" ∷ is_conf_inv γ γconf ∗
    "#Hck" ∷ config_proof.is_Clerk ck γconf.

Lemma wp_MakeClerk2 (configHost:u64) γ :
  {{{
        is_pb_config_host configHost γ
  }}}
    config.MakeClerk #configHost
  {{{
      γconf ck, RET #ck; is_Clerk2 ck γ γconf
  }}}.
Proof.
  iIntros (Φ) "#Hhost HΦ".
  iNamed "Hhost".
  wp_apply (config_proof.wp_MakeClerk with "[$Hhost]").
  iIntros.
  iApply "HΦ".
  iFrame "#".
Qed.

Lemma wp_Clerk__GetConfig2 ck γ γconf Φ :
  is_Clerk2 ck γ γconf -∗
  □(∀ confγs (conf:list u64) config_sl,
  (own_slice_small config_sl uint64T 1 conf ∗
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

Lemma wp_Clerk_ReserveEpochAndGetConfig2 ck γ γconf Φ :
  is_Clerk2 ck γ γconf -∗
  □((∀ (epoch epoch_lb:u64) confγs (conf:list u64) config_sl,
  (own_slice_small config_sl uint64T 1 conf ∗
  is_reserved_epoch_lb γconf epoch ∗
  config_proposal_unset γ.(s_pb) epoch ∗
  own_proposal_unused γ.(s_pb) epoch ∗
  own_init_proposal_unused γ.(s_prim) epoch ∗
  is_epoch_config γ.(s_pb) epoch_lb (r_pb <$> confγs) ∗
  (∀ epoch_skip, ⌜int.nat epoch_lb < int.nat epoch_skip⌝ → ⌜int.nat epoch_skip < int.nat epoch⌝ → is_epoch_skipped γ.(s_pb) epoch_skip) ∗
  ([∗ list] γsrv ; host ∈ confγs; conf, is_pb_host host γ γsrv) ∗
  (∀ γsrv, ⌜γsrv ∈ (r_pb <$> confγs)⌝ → is_epoch_lb γsrv epoch_lb)) -∗
   Φ (#epoch, slice_val config_sl)%V
  )) -∗
  WP config.Clerk__ReserveEpochAndGetConfig #ck {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  iNamed "Hck".
  wp_apply (wp_Clerk__ReserveEpochAndGetConfig with "[$Hck]").
  iModIntro.
  iIntros "Hlc".
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iNamed "Hi".
  iExists _, _.
  iFrame.
  iIntros "%Hno_overflow Hres Hconf".
  iDestruct (mono_nat_lb_own_get with "Hres") as "#Hwit".
  iMod "Hmask".

  (* Hunset becomes skipped, and the first unused becomes unset. *)
  iDestruct (big_sepS_elem_of_acc_impl (word.add reservedEpoch (U64 1)) with "Hunreserved") as "[Hunset_new Hunused]".
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

    iMod ("Hclose" with "[Hres Hunset_new2 Hunused Hepoch Hconf]").
    {
      iNext. iExists _, _, _, _.
      iFrame "Hepoch Hres Hconf His_conf ∗#".
      iSplitR.
      { iPureIntro. word. }
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
      assert (int.nat epoch_skip = int.nat reservedEpoch ∨ int.nat epoch_skip < int.nat reservedEpoch ∨ int.nat epoch_skip >= int.nat (word.add reservedEpoch (U64 1))) as Hineq.
      { word. }
      destruct Hineq as [Heq|[Hineq|Hineq]].
      {
        replace (epoch_skip) with (reservedEpoch) by word.
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
    assert (int.nat epoch_skip = int.nat reservedEpoch ∨ int.nat epoch_skip < int.nat reservedEpoch ∨ int.nat epoch_skip >= int.nat (word.add reservedEpoch (U64 1))) as Hineq.
    { word. }
    destruct Hineq as [Heq|[Hineq|Hineq]].
    {
      replace (epoch_skip) with (reservedEpoch) by word.
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

    iMod ("Hclose" with "[Hres Hunset_new2 Hunused Hepoch Hconf]").
    {
      iNext. iExists _, _, _, _.
      iFrame "∗ His_conf #".
      iSplitR.
      { iPureIntro. word. }
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
      replace (int.nat (word.add reservedEpoch 1%Z)) with (int.nat reservedEpoch + 1) in H0 by word.
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
    replace (int.nat (word.add reservedEpoch 1%Z)) with (int.nat reservedEpoch + 1) in H0 by word.
    word.
  }
Qed.

Lemma wp_Clerk__WriteConfig2 ck γ γconf Φ config_sl conf confγ epoch :
  is_Clerk2 ck γ γconf -∗
  own_slice_small config_sl uint64T 1 conf -∗
  is_epoch_config_proposal γ.(s_pb) epoch (r_pb <$> confγ) -∗
  is_reserved_epoch_lb γconf epoch -∗
  ([∗ list] γsrv ; host ∈ confγ ; conf, is_pb_host host γ γsrv) -∗
  (∀ γsrv, ⌜γsrv ∈ (r_pb <$> confγ)⌝ → is_epoch_lb γsrv epoch) -∗
  □ (∀ (err:u64),
      (if (decide (err = U64 0)) then
        is_epoch_config γ.(s_pb) epoch (r_pb <$> confγ)
      else
        True) -∗
      own_slice_small config_sl uint64T 1 conf -∗
      Φ #err)
  -∗
  WP config.Clerk__TryWriteConfig #ck #epoch (slice_val config_sl) {{ Φ }}
.
Proof.
  iIntros "#Hck Hsl #Hconf_prop #Hwit #Hhosts #Hlbs #HΦ".
  iNamed "Hck".
  wp_apply (wp_Clerk__TryWriteConfig with "Hck Hsl"); last first.
  {
    iIntros.
    iApply ("HΦ" with "[] [$]").
    destruct (decide _).
    { exfalso. done. }
    done.
  }
  2:{ iFrame "#". }
  iModIntro.
  iIntros "Hlc".
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iApply fupd_mask_intro.
  {
    enough (↑epochLeaseN ## (↑configN:coPset)) by solve_ndisj.
    by apply ndot_ne_disjoint.
  }
  iIntros "Hmask".
  iNamed "Hi".
  iExists _, _.
  iFrame "∗".
  destruct (decide (_)); last first.
  { (* write failed because of stale epoch. *)
    iIntros "Hepoch Hres".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hepoch Hres Hconf Hunreserved Hunset_or_set]").
    {
      iNext.  iExists _, _, _, _.
      iFrame "∗ His_conf #%".
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
    iIntros "Hconf Hres Hepoch".
    iMod "Hmask" as "_".

    iDestruct "Hunset_or_set" as "[Hunset|%Hset]"; last first.
    { (* config was already set before *)
      replace (epoch) with (epoch0) by word.
      iDestruct "Hconf_prop" as "[Hconf_prop %Hle]".
      iDestruct "His_conf" as "(? & His_conf_prop & ?)".
      iDestruct (own_valid_2 with "His_conf_prop Hconf_prop") as %Hvalid.
      rewrite singleton_op in Hvalid.
      rewrite singleton_valid in Hvalid.
      rewrite dfrac_agree_op_valid in Hvalid.
      replace (r_pb <$> confγs) with (r_pb <$> confγ) in * by naive_solver.

      iMod ("Hclose" with "[Hepoch Hconf Hunreserved Hres]").
      {
        iNext.  iExists _, _, _, _.
        iFrame "Hhosts ∗#".
        iSplitR; first done.
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
      iMod ("Hclose" with "[Hconf Hres Hepoch Hunreserved]").
      {
        iNext. iExists _, _, _, _.
        iFrame "∗ Hset #".
        iDestruct "Hconf_prop" as "[_ %Hineq]".
        iSplitR; first done.
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
