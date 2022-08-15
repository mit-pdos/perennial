From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export admin.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb Require Import pb_definitions config_proof.

Section admin_proof.

Context {pb_record:PBRecord}.
Notation pbG := (pbG (pb_record:=pb_record)).
Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_snap_encoding := (pb_has_snap_encoding pb_record).
Notation has_op_encoding_injective := (pb_has_op_encoding_injective pb_record).
Notation compute_reply := (pb_compute_reply pb_record).

Notation wp_Clerk__GetState := (wp_Clerk__GetState (pb_record:=pb_record)).
Notation wp_Clerk__SetState := (wp_Clerk__SetState (pb_record:=pb_record)).

Context `{!heapGS Σ}.
Context `{!pbG Σ}.
Context `{!configG Σ}.

Definition adminN := nroot .@ "admin".

Definition is_conf_inv γpb γconf : iProp Σ :=
  inv adminN (∃ epoch conf (confγs:list pb_server_names) epoch_lb,
      "Hepoch" ∷ own_epoch γconf epoch ∗
      "Hconf" ∷ own_config γconf conf ∗
      "#His_conf" ∷ is_epoch_config γpb epoch_lb confγs ∗
      "#His_hosts" ∷ ([∗ list] γsrv ; host ∈ confγs ; conf, is_pb_host γpb γsrv host) ∗
      "#His_lbs" ∷ (∀ γsrv, ⌜γsrv ∈ confγs⌝ → pb_ghost.is_epoch_lb γsrv epoch_lb) ∗
      "Hunused" ∷ ([∗ set] epoch' ∈ (fin_to_set u64), ⌜int.nat epoch < int.nat epoch'⌝ → config_unset γpb epoch' ∗ config_unset γpb epoch') ∗
      "Hunset" ∷ config_unset γpb epoch ∗
      "#His_skip" ∷ (∀ epoch_skip, ⌜int.nat epoch_skip < int.nat epoch⌝ → ⌜int.nat epoch_lb < int.nat epoch_skip⌝ → is_epoch_skipped γpb epoch_skip)
      )
.

Definition is_Clerk2 ck γpb : iProp Σ :=
  ∃ γconf,
    "#Hinv" ∷ is_conf_inv γpb γconf ∗
    "#Hck" ∷ is_Clerk ck γconf.

Lemma wp_Clerk__GetEpochAndConfig2 ck γpb Φ :
  is_Clerk2 ck γpb -∗
  □(∀ (epoch epoch_lb:u64) confγs (conf:list u64) config_sl,
  (is_slice config_sl uint64T 1 conf ∗
  config_unset γpb epoch ∗
  is_epoch_config γpb epoch_lb confγs ∗
  (∀ epoch_skip, ⌜int.nat epoch_skip < int.nat epoch⌝ → ⌜int.nat epoch_lb < int.nat epoch_skip⌝ → is_epoch_skipped γpb epoch_skip) ∗
  ([∗ list] γsrv ; host ∈ confγs ; conf, is_pb_host γpb γsrv host) ∗
  (∀ γsrv, ⌜γsrv ∈ confγs⌝ → pb_ghost.is_epoch_lb γsrv epoch_lb)) -∗
   Φ (#epoch, slice_val config_sl)%V
  ) -∗
  WP config.Clerk__GetEpochAndConfig #ck {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  iNamed "Hck".
  wp_apply (wp_Clerk__GetEpochAndConfig with "[$Hck]").
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
  iIntros "%Hno_overflow Hepoch Hconf".
  iMod "Hmask".

  (* Hunset becomes skipped, and the first unused becomes unset. *)
  iDestruct (big_sepS_elem_of_acc_impl (word.add epoch (U64 1)) with "Hunused") as "[Hunset_new Hunused]".
  { set_solver. }
  iMod (own_update with "Hunset") as "Hskip1".
  {
    apply singleton_update.
    apply dfrac_agree_persist.
  }
  iDestruct "Hskip1" as "#Hskip1".
  iSpecialize ("Hunset_new" with "[]").
  { done. }
  iDestruct "Hunset_new" as "[Hunset_new Hunset_new2]".

  iMod ("Hclose" with "[Hunset_new2 Hunused Hepoch Hconf]").
  {
    iNext. iExists _, _, _, _.
    iFrame "∗#".
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
  iFrame "∗#".

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
Qed.

Lemma wp_Reconfig γ (configHost:u64) (servers:list u64) (servers_sl:Slice.t) :
  {{{
        "Hservers_sl" ∷ is_slice servers_sl uint64T 1 servers ∗
        "#Hhost" ∷ ∀ srv, ⌜srv ∈ servers⌝ → (∃ γsrv, is_pb_host γ γsrv srv)
  }}}
    EnterNewConfig #configHost (slice_val servers_sl)
  {{{
        RET #(); True
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_MakeClerk with "").
  { admit. }
Admitted.

End admin_proof.
