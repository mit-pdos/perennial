From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import gset.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

Section simulation.
  Context `{!invG Σ}.
  Context {state: Type} (wf: state -> Prop) (P: state -> iProp Σ).
  Context (E: coPset).
  (* TODO: if we can start using this everywhere I think we can start proving
  generic theorems about simulation, like the one below *)
  Definition simulation_fupd {T} (tr: transition state T) (Q: T -> iProp Σ): iProp Σ :=
    (∀ σ σ' r,
         ⌜wf σ⌝ -∗
         ⌜relation.denote tr σ σ' r⌝ -∗
        (P σ ={E}=∗ P σ' ∗ ⌜wf σ'⌝ ∗ Q r)).

  Theorem simulation_bind_fupd {A B}
          (tr1: transition state A)
          (tr2: A -> transition state B)
          (Q: B -> iProp Σ) :
    simulation_fupd tr1 (fun x => simulation_fupd (tr2 x) Q) -∗
    simulation_fupd (bind tr1 tr2) Q.
  Proof.
    iIntros "Hfupd".
    iIntros (σ1 σ3 r Hwf Htr) "HP".
    simpl in Htr.
    inversion Htr; subst; clear Htr.
    rename s2 into σ2.
    iMod ("Hfupd" with "[] [] HP") as "(HP&%Hwf2&Hfupd2)"; eauto.
    iMod ("Hfupd2" with "[] [] HP") as "(HP&%Hwf3&HQ)"; eauto.
    iFrame.
    auto.
  Qed.
End simulation.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names (Σ:=Σ)).
Implicit Types (s: log_state.t) (memLog: list update.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let innerN := walN .@ "wal".
Let circN := walN .@ "circ".

Definition in_bounds γ (a: u64): iProp Σ. Admitted.
Instance in_bounds_persistent γ a : Persistent (in_bounds γ a).
Proof. Admitted.

(* TODO: this will actually require combining in_bounds with some authoritative
resource from the invariant, obviously it can't be for an arbitrary [σ] *)
Theorem in_bounds_valid γ σ a :
  in_bounds γ a -∗ ⌜is_Some (σ.(log_state.d) !! int.val a)⌝.
Proof. Admitted.

(* this is more or less big_sepM_lookup_acc, but with is_installed_read unfolded *)
Theorem is_installed_read_lookup {γ d txns installed_lb durable_txn_id} {a: u64} :
  is_Some (d !! int.val a) ->
  is_installed γ d txns installed_lb durable_txn_id -∗
  ∃ txn_id b,
    ⌜(installed_lb ≤ txn_id ≤ durable_txn_id)%nat ∧
      apply_upds (txn_upds (take (S txn_id) txns)) d !! int.val a = Some b⌝ ∗
    int.val a d↦ b ∗ (int.val a d↦ b -∗ is_installed γ d txns installed_lb durable_txn_id).
Proof.
  rewrite /is_installed_read.
  iIntros (Hlookup) "Hbs".
  destruct Hlookup as [b0 Hlookup].
  iNamedRestorable "Hbs".
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hlookup with "Hdata") as "[Hb Hdata]".
  iApply restore_intro in "Hb".
  iDestruct "Hb" as (b) "(%Hbvalue&Hb&%Ha_bound&Hb')".
  iDestruct (restore_elim with "Hb'") as "#Hb_restore"; iClear "Hb'".
  iExists (if decide (int.val a ∈ being_installed)
           then new_installed_txn_id
           else installed_lb), b.
  iFrame "Hb".
  iSplit.
  { iPureIntro. split; auto.
    destruct (decide _); lia. }
  iIntros "Hb".
  iApply "Hbs"; iFrame.
  iApply "Hdata".
  iApply "Hb_restore".
  iFrame.
Qed.

Lemma is_durable_txn_bound γ cs txns diskEnd_txn_id durable_lb :
  is_durable_txn γ cs txns diskEnd_txn_id durable_lb -∗
  ⌜(diskEnd_txn_id < length txns)%nat⌝.
Proof.
  iNamed 1.
  iPureIntro.
  apply is_highest_weaken in Hend_txn.
  apply is_txn_bound in Hend_txn; lia.
Qed.

Theorem wp_Walog__ReadInstalled (Q: Block -> iProp Σ) l γ a :
  {{{ is_wal P l γ ∗
      in_bounds γ a ∗
       (∀ σ σ' b,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_read_installed a) σ σ' b⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q b))
   }}}
    Walog__ReadInstalled #l #a
  {{{ bl, RET slice_val bl; ∃ b, is_block bl 1 b ∗ Q b}}}.
Proof.
  iIntros (Φ) "(#Hwal & #Ha_valid & Hfupd) HΦ".
  wp_call.
  wp_apply (wp_Read_fupd _ _ 1 (* q=1 *)).
  iDestruct "Hwal" as "[Hwal Hcirc]".
  iInv "Hwal" as (σ) "[Hinner HP]" "Hclose".
  iDestruct "Hinner" as "(>? & ? & ? & >? & >Hdisk)"; iNamed.
  iNamed "Hdisk".
  iNamed "Hdisk".

  iDestruct (in_bounds_valid _ σ with "Ha_valid") as %Hlookup.
  iDestruct (is_installed_read_lookup Hlookup with "Hinstalled") as
      (txn_id b [Htxn_id Hbval]) "(Hb&Hinstalled)".
  iModIntro.
  iExists b; iFrame "Hb".
  iNext.
  iIntros "Hb".
  iSpecialize ("Hinstalled" with "Hb").
  iNamed "circ.start".
  fold innerN.
  iMod (fupd_intro_mask' _ (⊤∖↑N)) as "HinnerN".
  { solve_ndisj. }
  iDestruct (is_durable_txn_bound with "circ.end") as %Hdurable_bound.

  iMod ("Hfupd" $! σ σ b with "[//] [] HP") as "[HP HQ]".
  { iPureIntro.
    repeat (simpl; monad_simpl).
    exists σ txn_id.
    { econstructor; eauto; lia. }
    repeat (simpl; monad_simpl). }
  iMod "HinnerN" as "_".
  iFrame.
  iMod ("Hclose" with "[-HQ HΦ]") as "_".
  {
    iModIntro.
    iExists _; iFrame "HP".
    iFrame.
    iSplit; auto.
    iExists _; iFrame.
    iExists _, _; iFrame "# ∗".
    auto.
  }
  iIntros "!>" (s) "Hs".
  iApply "HΦ".
  iExists _; iFrame.
  iDestruct (is_slice_to_small with "Hs") as "$".
Qed.

Theorem wp_installBlocks γ d bufs_s (bufs: list update.t)
        (installed_txn_id new_installed_txn_id: nat) :
  {{{ readonly (updates_slice_frag bufs_s 1 bufs) ∗
      (* these aren't enough assumptions - we need bufs to actually match the
      new transactions being installed (which will come from snapshotting the
      memLog invariant) *)
      own γ.(being_installed_name) (◯ Excl' (∅: gset Z)) ∗
      own γ.(new_installed_name) (◯ Excl' installed_txn_id)
   }}}
    installBlocks #d (slice_val bufs_s)
  {{{ RET #(); updates_slice bufs_s bufs ∗
      (* probably not enough in the postcondition, but it can only be ghost
      variables so maybe this is it *)
      own γ.(being_installed_name) (◯ Excl' (list_to_set (C:=gset Z) ((λ u, int.val (update.addr u)) <$> bufs))) ∗
      own γ.(new_installed_name) (◯ Excl' installed_txn_id)
  }}}.
Proof.
Admitted.

(* TODO: why do we need this here again? *)
Opaque is_sliding.

Theorem wp_Walog__logInstall γ l σₛ :
  {{{ "#st" ∷ readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
      "#d" ∷ readonly (l ↦[Walog.S :: "d"] σₛ.(wal_d)) ∗
      "#memLock" ∷ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
      "#condInstall" ∷ readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
      "Hlkinv" ∷ wal_linv σₛ.(wal_st) γ ∗
      "His_locked" ∷ locked #σₛ.(memLock) ∗
      "#lk" ∷ is_lock N #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ) ∗
      "#cond_install" ∷ is_cond σₛ.(condInstall) #σₛ.(memLock)
  }}}
    Walog__logInstall #l
  {{{ (blkCount installEnd:u64), RET (#blkCount, #installEnd);
      "Hlkinv" ∷ wal_linv σₛ.(wal_st) γ ∗
      "His_locked" ∷ locked #σₛ.(memLock)
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ"; iNamed "Hpre". (* TODO: would be nice to do this anonymously *)
  iNamedRestorable "Hlkinv".
  iNamedRestorable "Hfields".
  iNamed "Hfield_ptsto".
  wp_call.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_sliding__takeTill with "His_memLog"); first by word.
  iIntros (q s) "(His_memLog&Htxn_slice)".
  wp_pures.
  wp_apply wp_slice_len; wp_pures.
  wp_if_destruct; wp_pures.
  { iApply "HΦ".
    iFrame "His_locked".
    iApply "Hlkinv"; iFrameNamed.
    iApply "Hfields"; iFrameNamed. }
  (* note that we get to keep Htxn_slice *)
  (* TODO: need to checkout some persistent fact that keeps these transactions
  tied to the abstract state, so that installBlocks can install them *)
  wp_loadField.
  wp_apply (release_spec with "[$lk $His_locked HdiskEnd_circ Hstart_circ HmemLog_linv
His_memLog HmemLog HdiskEnd Hshutdown Hnthread]").
  { iNext.
    iApply "Hlkinv"; iFrameNamed.
    iApply "Hfields"; iFrameNamed. }
  wp_pures.
  wp_apply util_proof.wp_DPrintf.
  wp_pures.
  admit. (* TODO: need reasonably correct spec for installBlocks *)
Admitted.

Theorem wp_Walog__installer γ l :
  {{{ is_wal P l γ }}}
    Walog__installer #l
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hwal HΦ".
  iMod (is_wal_read_mem with "Hwal") as "#Hmem".
  wp_call.
  iNamed "Hmem".
  iNamed "Hstfields".
  wp_loadField.
  wp_apply (acquire_spec with "lk").
  iIntros "[Hlocked Hlockinv]".
  wp_apply (wp_inc_nthread with "[$Hlockinv $st]"); iIntros "Hlockinv".
  wp_pures.
  wp_bind (For _ _ _).
  wp_apply (wp_forBreak_cond (fun _ => "Hlockinv" ∷ wal_linv σₛ.(wal_st) γ ∗ "Hlocked" ∷ locked #σₛ.(memLock))%I
           with "[] [$Hlocked $Hlockinv]").
  { clear Φ.
    iIntros "!>" (Φ) "I HΦ"; iNamed "I".
    wp_apply (wp_load_shutdown with "[$st $Hlockinv]"); iIntros (shutdown) "Hlockinv".
    wp_pures.
    wp_if_destruct.
    - wp_pures.
      wp_apply (wp_Walog__logInstall with "[$st $d $lk $memlock $condInstall $cond_install $Hlocked $Hlockinv]").
      iIntros (blkCount installEnd) "post"; iNamed "post".
      wp_pures.
      wp_bind (If _ _ _).
      wp_if_destruct.
      { wp_apply util_proof.wp_DPrintf; wp_pures.
        iApply ("HΦ" with "[$]"). }
      wp_loadField.
      wp_apply (wp_condWait with "[$cond_install $lk $His_locked $Hlkinv]").
      iIntros "[His_locked Hlkinv]".
      wp_pures.
      iApply ("HΦ" with "[$]").
    - iApply ("HΦ" with "[$]"). }
  iIntros "I"; iNamed "I".
  wp_apply util_proof.wp_DPrintf.
  wp_apply (wp_dec_nthread with "[$Hlockinv $st]"); iIntros "Hlockinv".
  wp_loadField.
  wp_apply (wp_condSignal with "[$cond_shut]").
  wp_loadField.
  wp_apply (release_spec with "[$lk $Hlocked $Hlockinv]").
  iApply ("HΦ" with "[$]").
Qed.

End goose_lang.
