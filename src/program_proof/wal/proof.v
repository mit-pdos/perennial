From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names (Σ:=Σ)).
Implicit Types (s: log_state.t) (memLog: list update.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let circN := walN .@ "circ".

Lemma memLogMap_ok_memLog_lookup memStart memLog a i :
  int.val memStart + Z.of_nat (length memLog) < 2^64 ->
  map_get (compute_memLogMap memLog memStart ∅) a
  = (i, true) ->
  ∃ b, memLog !! int.nat (word.sub i memStart) = Some (update.mk a b)
  (* also, i is the highest index such that this is true *).
Proof.
  intros Hbound Hlookup.
  apply map_get_true in Hlookup.
  assert (int.val memStart ≤ int.val i) by admit. (* from how memLogMap is computed and lack of overflow *)
  replace (int.nat (word.sub i memStart)) with (int.nat i - int.nat memStart)%nat by word.
  (* this is hard, induction is hard with this left fold *)
Admitted.

Opaque struct.t.

Theorem wp_WalogState__readMem γ (st: loc) σ (a: u64) :
  {{{ wal_linv_fields st σ ∗
      memLog_linv γ σ.(memStart) σ.(memLog) }}}
    WalogState__readMem #st #a
  {{{ b_s b (ok:bool), RET (slice_val b_s, #ok);
      if ok then is_block b_s b ∗
                 ⌜apply_upds σ.(memLog) ∅ !! int.val a = Some b⌝ ∗
                 memLog_linv γ σ.(memStart) σ.(memLog)
      else True
  }}}.
Proof.
  iIntros (Φ) "(Hfields&HmemLog_inv) HΦ".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  wp_call.
  wp_loadField.
  wp_apply (wp_MapGet with "His_memLogMap").
  iIntros (i ok) "(%Hmapget&His_memLogMap)".
  wp_pures.
  wp_if_destruct.
  - wp_apply util_proof.wp_DPrintf.
    wp_loadField. wp_loadField.
    apply memLogMap_ok_memLog_lookup in Hmapget as [b HmemLog_lookup];
      last by admit. (* TODO: in-bounds proof *)
    wp_apply (wp_SliceGet_updates with "[$His_memLog]"); eauto.
    simpl.
    iIntros ([a' u_s]) "(<-&Hb&His_memLog)".
    wp_apply (wp_copyUpdateBlock with "Hb").
    iIntros (s') "[Hb Hb_new]".
    iSpecialize ("His_memLog" with "Hb").
    wp_pures.
    iApply "HΦ".
    iFrame.
    simpl in HmemLog_lookup |- *.
    (* TODO: this comes from HmemLog_lookup plus that a' is maximal (the
    apply_upds formulation is actually a good way to phrase it, especially since
    [apply_upds] and [compute_memLogMap] are similar fold_left's) *)
Admitted.

Theorem wp_Walog__ReadMem (Q: option Block -> iProp Σ) l γ a :
  {{{ is_wal P l γ ∗
       (∀ σ σ' mb,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗
         (P σ ={⊤ ∖ ↑N}=∗ P σ' ∗ Q mb))
   }}}
    Walog__ReadMem #l #a
  {{{ (ok:bool) bl, RET (slice_val bl, #ok); if ok
                                             then ∃ b, is_block bl b ∗ Q (Some b)
                                             else Q None}}}.
Proof.
  iIntros (Φ) "[#Hwal Hfupd] HΦ".
  destruct_is_wal.
  wp_loadField.
  wp_apply (acquire_spec with "lk"). iIntros "(Hlocked&Hlkinv)".
  wp_loadField.
Abort.

Theorem wp_Walog__logAppend l γ σₛ :
  {{{ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
      readonly (l ↦[Walog.S :: "condLogger"] #σₛ.(condLogger)) ∗
      readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
      is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
      is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
      readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
      wal_linv σₛ.(wal_st) γ ∗
      locked γ.(lock_name) ∗
      is_lock N γ.(lock_name) #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ)
  }}}
    Walog__logAppend #l
  {{{ (progress:bool), RET #progress;
      wal_linv σₛ.(wal_st) γ ∗
      locked γ.(lock_name)
  }}}.
Proof.
  iIntros (Φ) "(#HmemLock& #HcondLogger& #HcondInstall &
              #His_cond1 & #His_cond2 & #Hf & Hlkinv& Hlocked& #His_lock) HΦ".
  wp_call.
  wp_bind (For _ _ _).
  (* TODO: need inner part of wal_linv with fixed memLog, so we can say after
  this wait loop [length memLog ≤ Z.of_nat LogSz] *)
  wp_apply (wp_forBreak_cond
              (λ b, locked γ.(lock_name) ∗
                    wal_linv σₛ.(wal_st) γ)%I
              with "[] [$Hlkinv $Hlocked]").
  { iIntros "!>" (Φ') "(Hlocked&Hlkinv) HΦ".
    wp_loadField.
    iNamed "Hlkinv".
    iNamed "Hfields".
    iNamed "Hfield_ptsto".
    wp_loadField.
    wp_apply wp_slice_len; wp_pures.
    change (int.val (word.divu (word.sub 4096 8) 8)) with LogSz.
    wp_if_destruct.
    - wp_loadField.
      wp_apply (wp_condWait with "[$His_cond2 $Hlocked $His_lock His_memLog His_memLogMap HmemLog HmemStart HdiskEnd HnextDiskEnd HmemLogMap Hshutdown Hnthread HnextDiskEnd_txn HmemLog_linv]").
      { iExists _; iFrame "∗ #". iExists _; iFrame. }
      iIntros "(Hlocked&Hlkinv)".
      wp_pures.
      iApply ("HΦ" with "[$]").
    - iApply "HΦ"; iFrame.
      iExists _; iFrame "∗ #". iExists _; iFrame.
  }
  iIntros "(Hlocked&Hlkinv)".
Admitted.

Ltac shutdown_fields :=
  let shutdown := fresh "shutdown" in
  let nthread := fresh "nthread" in
  iDestruct (wal_linv_shutdown with "Hlkinv") as (shutdown nthread) "[[? ?] Hlkinv]";
  repeat wp_loadField;
  repeat wp_storeField;
  iSpecialize ("Hlkinv" with "[$] [$]");
  try (clear shutdown);
  try (clear nthread).

Lemma wp_inc_nthread l (st: loc) γ :
  {{{ readonly (l ↦[Walog.S :: "st"] #st) ∗ wal_linv st γ }}}
    struct.storeF WalogState.S "nthread" (struct.loadF Walog.S "st" #l)
    (struct.loadF WalogState.S "nthread" (struct.loadF Walog.S "st" #l) + #1)
    {{{ RET #(); wal_linv st γ }}}.
Proof.
  iIntros (Φ) "[#Hst Hlkinv] HΦ".
  shutdown_fields.
  iApply ("HΦ" with "[$]").
Qed.

Lemma wp_dec_nthread l (st: loc) γ :
  {{{ readonly (l ↦[Walog.S :: "st"] #st) ∗ wal_linv st γ }}}
    struct.storeF WalogState.S "nthread" (struct.loadF Walog.S "st" #l)
    (struct.loadF WalogState.S "nthread" (struct.loadF Walog.S "st" #l) - #1)
    {{{ RET #(); wal_linv st γ }}}.
Proof.
  iIntros (Φ) "[#Hst Hlkinv] HΦ".
  shutdown_fields.
  iApply ("HΦ" with "[$]").
Qed.

Theorem wp_Walog__logger l γ :
  {{{ is_wal P l γ }}}
    Walog__logger #l
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hwal HΦ".
  iMod (is_wal_read_mem with "Hwal") as "#Hmem".
  wp_call.
  iDestruct "Hmem" as (σₛ) "(Hfields&HcondLogger&HcondInstall&HcondShut&#Hlk)".
  iDestruct "Hfields" as "(Hf1&Hf2&Hf3&Hf4&Hf5&Hf6&Hf7)".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "(Hlk_held&Hlkinv)".
  wp_pures.

  wp_apply (wp_inc_nthread with "[$Hf4 $Hlkinv]"); iIntros "Hlkinv".
  wp_pures.
  wp_bind (For _ _ _).
  wp_apply (wp_forBreak_cond (fun b => wal_linv σₛ.(wal_st) γ ∗ locked γ.(lock_name))%I
              with "[] [$Hlkinv $Hlk_held]").
  { iIntros "!>" (Φ') "(Hlkinv&Hlk_held) HΦ".
    shutdown_fields.
    wp_pures.
    wp_if_destruct.
    - wp_pures.
      wp_apply (wp_Walog__logAppend with "[$Hlkinv $Hlk_held]").
      { iFrame "#". }
      iIntros (progress) "(Hlkinv&Hlk_held)".
      wp_pures.
      destruct (negb progress); [ wp_if_true | wp_if_false ]; wp_pures.
      + wp_loadField.
        wp_apply (wp_condWait with "[$HcondLogger $Hlk $Hlkinv $Hlk_held]").
        iIntros "(Hlk_held&Hlkinv)".
        wp_pures.
        iApply ("HΦ" with "[$]").
      + iApply ("HΦ" with "[$]").
    - iApply ("HΦ" with "[$]").
  }
  iIntros "(Hlkinv&Hlk_held)".
  wp_apply util_proof.wp_DPrintf.
  wp_apply (wp_dec_nthread with "[$Hf4 $Hlkinv]"); iIntros "Hlkinv".
  wp_loadField.
  wp_apply (wp_condSignal with "HcondShut").
  wp_loadField.
  wp_apply (release_spec with "[$Hlk $Hlk_held $Hlkinv]").
  iApply ("HΦ" with "[//]").
Qed.

End goose_lang.
