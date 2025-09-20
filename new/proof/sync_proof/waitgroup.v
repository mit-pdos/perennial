From New.proof.sync_proof Require Import base sema.
From New.experiments Require Import glob.

Section proof.
Context `{hG:heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!syncG Σ}.

Local Definition enc (waiters counters : Z) : w64 :=
  word.add (word.slu (W64 counters) (W64 32)) (W64 (uint.Z waiters)).

Local Lemma enc_get_counter (waiters counter : Z) :
  0 <= waiters < 2^31 →
  W32 (uint.Z (word.sru (enc waiters counter) (W64 32))) = W32 counter.
Proof. intros. unfold enc. word. Qed.

Local Lemma enc_get_waiters (waiters counter : Z) :
  0 ≤ waiters < 2^31 →
  W32 (uint.Z (word.and (enc waiters counter) (W64 2147483647))) = W32 waiters.
Proof. unfold enc. admit. Admitted.

Local Lemma enc_get_bubble (waiters counter : Z) :
  0 ≤ waiters < 2^31 →
  0 ≤ counter < 2^32 →
  word.and (enc waiters counter) (W64 sync.waitGroupBubbleFlag) = (W64 0).
Proof.
  unfold enc. unfold sync.waitGroupBubbleFlag. intros.
  rewrite Automation.word.word_eq_iff_Z_eq.
  rewrite word.unsigned_and. rewrite word.unsigned_add.
  rewrite word.unsigned_slu //.
  repeat ereplace (uint.Z (W64 ?[x])) with ?x by word.
Admitted.

Local Lemma enc_add_counter (waiters counter : Z) (delta : w64):
  word.add (enc waiters counter) (word.slu delta (W64 32)) =
  enc waiters (counter + sint.Z delta).
Proof. unfold enc. word. Qed.

Local Lemma enc_add_waiters (waiters counter : Z) (delta : w64) :
  word.add (enc waiters counter) delta =
  enc (waiters + sint.Z delta) counter.
Proof. unfold enc. word. Qed.

Local Lemma enc_inj (waiters counter waiters' counter' : Z) :
  0 ≤ waiters < 2^31 → 0 ≤ waiters' < 2^31 →
  0 ≤ counter < 2^32 → 0 ≤ counter' < 2^32 →
  enc waiters counter = enc waiters' counter' →
  waiters = waiters' ∧ counter = counter'.
Proof. unfold enc. intros. word. Qed.

Local Lemma enc_0 :
  W64 0 = enc 0 0.
Proof. reflexivity. Qed.

Record WaitGroup_names := {
    counter_gn : gname ;
    sema_gn : gname ;
    waiter_gn : gname ;
    zerostate_gn : gname ;
  }.

Implicit Type γ : WaitGroup_names.

Definition own_WaitGroup_waiters γ (possible_waiters : Z) : iProp Σ :=
  own_tok_auth_dfrac γ.(waiter_gn) (DfracOwn (1/2)) (Z.to_nat possible_waiters).
#[global] Opaque own_WaitGroup_waiters.
#[local] Transparent own_WaitGroup_waiters.
#[global] Instance own_WaitGroup_waiters_timeless γ w : Timeless (own_WaitGroup_waiters γ w) := _.

Definition own_WaitGroup_wait_token γ : iProp Σ :=
  own_toks γ.(waiter_gn) 1.
#[global] Opaque own_WaitGroup_wait_token.
#[local] Transparent own_WaitGroup_wait_token.
#[global] Instance own_WaitGroup_wait_token_timeless γ  : Timeless (own_WaitGroup_wait_token γ) := _.

Local Definition is_WaitGroup_inv wg γ N : iProp Σ :=
  inv (N.@"wg") (∃ (counter waiters possible_waiters : Z) (sema : w32) unfinished_waiters,
  "Hsema" ∷ own_sema γ.(sema_gn) sema ∗
  "Hsema_zerotoks" ∷  own_toks γ.(zerostate_gn) (uint.nat sema) ∗

  "Hptsto" ∷ own_Uint64 (struct.field_ref_f sync.WaitGroup "state" wg) (DfracOwn (1/2)) (enc waiters counter) ∗
  "Hptsto2" ∷ (
      if decide (counter = 0 ∧ waiters ≠ 0) then True
      else own_Uint64 (struct.field_ref_f sync.WaitGroup "state" wg) (DfracOwn (1/2)) (enc waiters counter)
    ) ∗
  "Hctr" ∷ ghost_var γ.(counter_gn) (1/2)%Qp counter ∗

  (* When Add's caller has [own_waiters 0], this resource implies that there are no waiters. *)
  "Hwait_toks" ∷  own_toks γ.(waiter_gn) (Z.to_nat waiters) ∗
  "Hunfinished_wait_toks" ∷ own_toks γ.(waiter_gn) unfinished_waiters ∗

  "Hzeroauth" ∷ own_tok_auth γ.(zerostate_gn) unfinished_waiters ∗

  (* keeping this to maintain that the number of waiters does not overflow. *)
  "Hwaiters_bounded" ∷ own_tok_auth_dfrac γ.(waiter_gn) (DfracOwn (1/2)) (Z.to_nat possible_waiters) ∗

  "%Hunfinished_zero" ∷ ⌜ unfinished_waiters ≠ O → waiters = 0 ∧ counter = 0 ⌝ ∗
  "%Hunfinished_bound" ∷ ⌜ Z.of_nat unfinished_waiters < 2^31 ⌝ ∗
  "%Hpossible_waiters_bounded" ∷ ⌜ 0 ≤ possible_waiters < 2^31 ⌝ ∗
  "%Hwaiters_bounded" ∷ ⌜ 0 ≤ waiters ⌝ ∗
  "%Hcounter_bounded" ∷ ⌜ 0 ≤ counter < 2^32 ⌝
  )%I.

Definition is_WaitGroup wg γ N : iProp Σ :=
  "#Hsem" ∷ is_sema (struct.field_ref_f sync.WaitGroup "sema" wg) γ.(sema_gn) (N.@"sema") ∗
  "#Hinv" ∷ is_WaitGroup_inv wg γ N.
#[global] Opaque is_WaitGroup.
#[local] Transparent is_WaitGroup.
#[global] Instance is_WaitGroup_persistent wg γ N : Persistent (is_WaitGroup wg γ N) := _.

#[local]
Instance if_sumbool_timeless {PROP : bi} (P Q : PROP) {_:Timeless P} {_:Timeless Q} A B
  (x : sumbool A B) :
  Timeless (if x then P else Q).
Proof. apply _. Qed.

(* Prepare to Wait() *)
Lemma alloc_wait_token wg γ N (w : Z) :
  0 ≤ w < (2^31) - 1 →
  is_WaitGroup wg γ N -∗
  own_WaitGroup_waiters γ w ={↑N}=∗ own_WaitGroup_waiters γ (w + 1) ∗ own_WaitGroup_wait_token γ.
Proof.
  intros H. iIntros "[_ #Hinv] H".
  iInv "Hinv" as ">Hi". iNamed "Hi".
  iCombine "Hwaiters_bounded H" gives %[_ ->].
  iCombine "Hwaiters_bounded H" as "H".
  iMod (own_tok_auth_add 1 with "H") as "[H Htok]".
  iModIntro. rewrite <- (Z2Nat.inj_add _ 1) by word.
  iDestruct "H" as "[H1 H2]". iSplitR "Htok H2".
  2:{ by iFrame. } iFrame "∗#%". word.
Qed.

Lemma waiters_none_token_false γ :
  own_WaitGroup_waiters γ 0 -∗ own_WaitGroup_wait_token γ -∗ False.
Proof.
  iIntros "H1 H2".
  iCombine "H1 H2" gives %H. word.
Qed.

Definition own_WaitGroup γ (counter : Z) : iProp Σ :=
  ghost_var γ.(counter_gn) (1/2)%Qp counter.
#[global] Opaque own_WaitGroup.
#[local] Transparent own_WaitGroup.
#[global] Instance own_WaitGroup_timeless γ counter : Timeless (own_WaitGroup γ counter) := _.

Lemma init_WaitGroup N wg_ptr :
  wg_ptr ↦ (default_val sync.WaitGroup.t) ={⊤}=∗
  ∃ γ,
  is_WaitGroup wg_ptr γ N ∗ own_WaitGroup γ 0 ∗ own_WaitGroup_waiters γ 0.
Proof.
  iIntros "H".
  iDestruct (struct_fields_split with "H") as "H".
  iNamed "H". simpl.

  iMod (ghost_var_alloc 0) as "[%counter_gn [Hctr1 Hctr2]]".
  iMod (init_sema with "[$Hsema]") as "[%sema_gn [Hs1 Hs2]]".
  iMod (own_tok_auth_alloc) as "[%waiter_gn [Hwaiters Hw2]]".
  iMod (own_tok_auth_alloc) as "[%zerostate_gn Hzerostate]".

  iExists {| sema_gn := sema_gn; counter_gn := counter_gn; zerostate_gn := zerostate_gn; waiter_gn := waiter_gn |}.
  iFrame "∗#".
  unfold is_WaitGroup.
  iDestruct "Hstate" as "[Hstate Hstate2]".
  iMod (own_toks_0 waiter_gn) as "?".
  iMod (own_toks_0 waiter_gn) as "?".
  iMod (own_toks_0 zerostate_gn) as "?".
  iMod (inv_alloc with "[-]") as "$"; last done.
  iNext. repeat iExists 0. iFrame. simpl. replace (uint.nat (W32 0)) with 0%nat by done. iFrame.
  done.
Qed.

(* XXX: overflow?
  https://github.com/golang/go/issues/20687
  https://go-review.googlesource.com/c/go/+/140937/2/src/sync/waitgroup.go *)

Lemma wp_WaitGroup__Add (wg : loc) (delta : w64) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N -∗
  (|={⊤,↑N}=>
     ∃ oldc,
       "Hwg" ∷ own_WaitGroup γ oldc ∗
       "%Hbounds" ∷ ⌜ 0 ≤ oldc + sint.Z delta < 2^31 ⌝ ∗
       "HnoWaiters" ∷ (⌜ oldc ≠ 0 ⌝ ∨ own_WaitGroup_waiters γ 0) ∗
       "HΦ" ∷ ((⌜ oldc ≠ 0 ⌝ ∨ own_WaitGroup_waiters γ 0) -∗
               own_WaitGroup γ (oldc + sint.Z delta) ={↑N,⊤}=∗ Φ #())
  ) -∗
  WP wg @ (ptrT.id sync.WaitGroup.id) @ "Add" #delta {{ Φ }}.
Proof.
  wp_start as "#His".
  wp_apply wp_with_defer as "%defer defer".
  simpl subst. wp_auto. wp_apply wp_IsInBubble.
  wp_apply wp_Uint64__Add.
  iMod "HΦ".
  iNamed "HΦ".
  unfold own_WaitGroup.
  iNamed "His".
  iInv "Hinv" as ">Hi" "Hclose".
  iNamedSuffix "Hi" "_wg".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iCombine "Hctr_wg Hwg" as "Hctr" gives %[_ <-].
  destruct decide as [Hw|HnotInWakingState].
  {
    iExFalso.
    destruct Hw as [-> Hw].
    iDestruct "HnoWaiters" as "[%|HnoWaiter]"; first by exfalso.
    iCombine "HnoWaiter Hwait_toks_wg" gives %Hbad.
    exfalso. apply Hw. word.
  }
  iCombine "Hptsto_wg Hptsto2_wg" as "Hptsto".
  iExists _. iFrame. rewrite enc_add_counter.
  iMod (ghost_var_update (counter + sint.Z delta) with "Hctr") as "[Hctr_wg Hwg]".
  iIntros "[Hptsto1_wg Hptsto2_wg]".
  destruct unfinished_waiters.
  2:{
    iExFalso. destruct (Hunfinished_zero_wg ltac:(done)) as [-> ->].
    iDestruct "HnoWaiters" as "[%|HnoWaiters]"; first done.
    iCombine "HnoWaiters Hunfinished_wait_toks_wg" gives %Hbad. word.
  }
  subst.
  iCombine "Hwaiters_bounded_wg Hwait_toks_wg" gives %Hwaiters_bounded.
  destruct (decide (counter + sint.Z delta = 0 ∧ waiters ≠ 0)) as [Hwake|HnoWake].
  2:{ (* not done, no need to wake waiters. *)
    iMod "Hmask" as "_".
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]").
    {
      iNamed "Hi". iNext. iFrame.
      rewrite decide_False; last intuition.
      iFrame. iFrame "%". word.
    }
    iMod ("HΦ" with "[$] [$]").
    iModIntro.
    wp_auto.
    rewrite enc_get_bubble; [ | word.. ].
    wp_auto.
    rewrite enc_get_counter; [ | word.. ].
    rewrite enc_get_waiters; [ | word.. ].

    destruct bool_decide eqn:Hbad.
    {
      exfalso.
      rewrite bool_decide_eq_true in Hbad.
      word.
    }
    wp_auto.
    wp_bind (if: _ then _ else do: #())%E.
    clear Hbad.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗ _)%I with "[-]").
    {
      destruct bool_decide eqn:Heq0.
      - wp_auto.
        iSplitR; first done.
        iNamedAccu.
      - rewrite bool_decide_eq_false in Heq0.
        wp_auto.
        destruct bool_decide eqn:Heq1.
        + wp_auto. rewrite bool_decide_eq_true in Heq1.
          destruct bool_decide eqn:Heq2.
          * exfalso. rewrite bool_decide_eq_true in Heq2. word.
          * wp_auto. iFrame. done.
        + wp_auto. iFrame. done.
    }
    iIntros (?) "[% H]". iNamed "H".
    subst.
    wp_auto.
    destruct (bool_decide) eqn:Heq1.
    { (* no need to wake anyone up *) wp_auto. iFrame. }
    rewrite bool_decide_eq_false in Heq1.
    wp_auto.
    rewrite bool_decide_true.
    { (* no need to wake anyone up *) wp_auto. iFrame. }
    word.
  }

  (* will have to wake *)
  iRename "Hptsto2_wg" into "Hptsto". (* not going back to invariant. *)
  iMod "Hmask" as "_".
  iCombineNamed "*_wg" as "Hi".
  iMod ("Hclose" with "[Hi]") as "_".
  {
    iNamed "Hi". iNext.
    iFrame. rewrite decide_True; last intuition. word.
  }
  iMod ("HΦ" with "[$] [$]") as "HΦ".
  iModIntro.
  wp_auto.
  rewrite enc_get_bubble; [ | word.. ].
  wp_auto.
  rewrite enc_get_counter; [ | word.. ].
  rewrite enc_get_waiters; [ | word.. ].

  destruct bool_decide eqn:Hbad.
  { exfalso. rewrite bool_decide_eq_true in Hbad. word. }
  wp_auto.
  wp_bind (if: _ then _ else do: #())%E.
  clear Hbad.
  iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗ _)%I with "[-]").
  {
    destruct bool_decide eqn:Heq0.
    - wp_auto.
      iSplitR; first done.
      iNamedAccu.
    - rewrite bool_decide_eq_false in Heq0.
      wp_auto.
      destruct bool_decide eqn:Heq1.
      + wp_auto.
        rewrite bool_decide_eq_true in Heq1.
        destruct bool_decide eqn:Heq2.
        * exfalso. rewrite bool_decide_eq_true in Heq2. word.
        * wp_auto. iFrame. done.
      + wp_auto. iFrame. done.
  }
  iIntros (?) "[% H]". iNamed "H".
  subst.
  wp_auto.
  rewrite -> bool_decide_false by word.
  wp_auto.
  rewrite -> bool_decide_false by word.
  wp_auto.
  wp_apply wp_Uint64__Load.
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iExists _; iFrame.
  iIntros "Hptsto".
  iMod "Hmask" as "_".
  iModIntro.
  wp_auto.
  rewrite bool_decide_true //.

  (* want to get a bunch of unfinisheds. *)
  wp_auto.
  wp_apply wp_Uint64__Store.
  iInv "Hinv" as ">Hi" "Hclose".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  clear Hunfinished_zero_wg sema.
  iNamedSuffix "Hi" "_wg".
  iClear "Hptsto2_wg".
  iCombine "Hptsto Hptsto_wg"  gives %[_ Heq].
  iCombine "Hwaiters_bounded_wg Hwait_toks_wg" gives %Hwaiters0_bounded.
  apply enc_inj in Heq as [<- <-]; [|word..].
  iCombine "Hptsto Hptsto_wg" as "Hptsto".
  iExists _. iFrame.
  iIntros "Hptsto".
  iMod "Hmask" as "_".
  destruct (unfinished_waiters) eqn:Huf.
  2:{ exfalso. word. }
  clear Hunfinished_zero_wg.
  iClear "Hunfinished_wait_toks_wg".
  iCombine "Hzeroauth_wg Hsema_zerotoks_wg" gives %Hs.
  replace (sema) with (W32 0) by word.
  clear Huf Hs unfinished_waiters sema.
  iMod (own_tok_auth_add (Z.to_nat waiters) with "[$Hzeroauth_wg]") as "[Hzeroauth_wg Hzerotoks_wg]".
  iEval (rewrite enc_0) in "Hptsto".
  iDestruct "Hptsto" as "[Hptsto1_wg Hptsto2_wg]".
  destruct Hwake as [Hwake1 Hwake2].
  rewrite Hwake1.
  iMod (own_toks_0 γ.(waiter_gn)) as "Hwait_toks'_wg".
  iRename "Hzerotoks_wg" into "Hzerotoks". (* remove from invariant. *)
  iCombineNamed "*_wg" as "Hi".
  iMod ("Hclose" with "[Hi]") as "_".
  { iNext. iNamed "Hi". iFrame "Hptsto1_wg ∗". iPureIntro. split; [done | word]. }
  iModIntro.
  wp_auto.
  (* call semrelease. *)

  iAssert (
      ∃ (wrem : Z),
        "w" ∷ w_ptr ↦ (W32 wrem) ∗
        "Hzerotoks" ∷ own_toks γ.(zerostate_gn) (Z.to_nat wrem) ∗
        "%Hwrem_bounds" ∷ ⌜ 0 ≤ wrem < 2^32 ⌝
    )%I with "[w Hzerotoks]" as "HloopInv".
  { iFrame. word. }

  wp_for.
  iNamed "HloopInv".
  wp_auto.
  destruct bool_decide eqn:Hwrem.
  { (* no more waiters to wake up. *)
    rewrite decide_False; last naive_solver.
    rewrite decide_True //.
    wp_auto. iFrame.
  }

  (* wake up another waiter *)
  rewrite bool_decide_eq_false in Hwrem.
  rewrite decide_True //.
  wp_auto.
  wp_apply (wp_runtime_Semrelease with "[$]").
  iInv "Hinv" as ">Hi" "Hclose".
  iNamedSuffix "Hi" "_wg".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _; iFrame "Hsema_wg".
  iIntros "Hsema_wg".
  iMod "Hmask" as "_".
  replace (Z.to_nat wrem)%nat with (1+(Z.to_nat (wrem - 1)))%nat by word.
  iDestruct (own_toks_add with "Hzerotoks") as "[Hzerotok Hzerotoks]".
  iCombine "Hsema_zerotoks_wg Hzerotok" as "Hsema_zerotok_wg".
  iCombine "Hzeroauth_wg Hsema_zerotok_wg" gives %Hbound.
  iCombineNamed "*_wg" as "Hi".
  iMod ("Hclose" with "[Hi]").
  {
    iNamed "Hi". iFrame.
    replace (uint.nat (word.add sema (W32 1))) with ((uint.nat sema) + 1)%nat by word.
    iFrame. done.
  }
  iModIntro. wp_auto. wp_for_post. iFrame.
  iSplitL; last word.
  iApply to_named. iExactEq "w". f_equal. word.
Qed.

Lemma wp_WaitGroup__Done (wg : loc) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N -∗
  (|={⊤,↑N}=>
     ∃ counter,
       "Hwg" ∷ own_WaitGroup γ counter ∗
       "%Hbounds" ∷ ⌜ 0 ≤ counter - 1 < 2^31 ⌝ ∗
       "HnoWaiters" ∷ (⌜ counter ≠ 0 ⌝ ∨ own_WaitGroup_waiters γ 0) ∗
       "HΦ" ∷ ((⌜ counter ≠ 0 ⌝ ∨ own_WaitGroup_waiters γ 0) -∗
               own_WaitGroup γ (counter - 1) ={↑N,⊤}=∗ Φ #())
  ) -∗
  WP wg @ (ptrT.id sync.WaitGroup.id) @ "Done" #() {{ Φ }}.
Proof.
  wp_start as "#His".
  wp_auto.
  wp_apply (wp_WaitGroup__Add with "[$]").
  iMod "HΦ". iNamed "HΦ".
  change (sint.Z (W64 (-1))) with (-1).
  iModIntro. iFrame "Hwg HnoWaiters". iSplitR.
  { word. }
  iIntros "Hw Hctr".
  iMod ("HΦ" with "[$] [$]") as "HΦ".
  iModIntro. wp_auto. iApply "HΦ".
Qed.

Lemma wp_WaitGroup__Wait (wg : loc) (delta : w64) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N ∗ own_WaitGroup_wait_token γ -∗
  (|={⊤∖↑N, ∅}=>
     ∃ counter,
       own_WaitGroup γ counter ∗ (⌜ counter = 0 ⌝ → own_WaitGroup γ counter ={∅,⊤∖↑N}=∗
                               own_WaitGroup_wait_token γ -∗ Φ #())
  ) -∗
  WP wg @ (ptrT.id sync.WaitGroup.id) @ "Wait" #() {{ Φ }}.
Proof.
  wp_start as "(#Hwg & HR_in)". iNamed "Hwg".
  wp_auto. wp_for. wp_apply (wp_Uint64__Load).
  iInv "Hinv" as ">Hi" "Hclose".
  iNamedSuffix "Hi" "_wg".
  destruct (decide (counter = 0)).
  { (* counter is zero, so can return. *)
    subst.

    iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as (?) "[Hwg HΦ]".
    { solve_ndisj. }
    iModIntro.
    iCombine "Hwg Hctr_wg" gives %[_ ->].
    iExists _.
    iFrame.
    iIntros "Hptsto_wg".
    iMod ("HΦ" with "[//] [$Hwg]") as "HΦ".
    iMod "Hmask" as "_".
    iCombine "Hwaiters_bounded_wg Hwait_toks_wg" gives %Hwaiters_bounded.
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]").
    { iNamed "Hi". by iFrame. }
    iModIntro.
    wp_auto.
    rewrite enc_get_counter; [|word..].
    rewrite enc_get_waiters; [|word..].
    wp_auto.
    wp_bind (if: if: if: _ then _ else _ then _ else _ then _ else _)%E.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗ _)%I with "[-]").
    { wp_if_destruct. 2:{ iSplitR; first done. iNamedAccu. } wp_auto.
      rewrite enc_get_bubble; [ | word.. ]. wp_auto. iFrame. done. }
    iIntros "% [-> H]". iNamed "H". wp_auto. wp_for_post. by iApply "HΦ".
  }
  (* actually go to sleep *)
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _; iFrame.
  iIntros "Hptsto_wg".
  iMod "Hmask" as "_".

  iCombine "HR_in Hwait_toks_wg" as "Hwait_toks'_wg".
  iCombine "Hwaiters_bounded_wg Hwait_toks'_wg" gives %HwaitersLe.
  iDestruct (own_toks_add with "Hwait_toks'_wg") as "[HR_in Hwait_toks_wg]".
  iCombineNamed "*_wg" as "Hi".
  iMod ("Hclose" with "[Hi]").
  { iNamed "Hi". by iFrame. }
  iModIntro.
  wp_auto.
  rewrite enc_get_counter; [|word..].
  rewrite enc_get_waiters; [|word..].
  rewrite bool_decide_false; [|word..].
  wp_auto.
  rewrite enc_add_waiters; [|word..].
  wp_apply (wp_Uint64__CompareAndSwap).
  iInv "Hinv" as ">Hi" "Hclose".
  iNamedSuffix "Hi" "_wg".
  setoid_rewrite bool_decide_decide.
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists (enc waiters0 counter0).
  destruct (decide (_ = _)) as [Heq|Hneq].
  {
    iCombine "Hwaiters_bounded_wg Hwait_toks_wg" gives %Hwaiters0_bounded.
    apply enc_inj in Heq as [-> ->]; [|word..].
    rewrite decide_False.
    2:{ naive_solver. }
    iCombine "Hptsto_wg Hptsto2_wg" as "$".
    iSplitR; first done.
    iIntros "[Hptsto_wg Hptsto2_wg]".
    iCombine "HR_in Hwait_toks_wg" as "Hwait_toks_wg".
    iMod "Hmask" as "_".
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]") as "_".
    {
      iNext. iNamed "Hi". repeat iExists _. iFrame "Hptsto_wg ∗".
      replace (Z.to_nat (waiters + sint.Z (W64 1))) with (1 + Z.to_nat waiters)%nat by word.
      simpl. iFrame. iSplitL.
      { by destruct decide. }
      iPureIntro. word.
    }
    iModIntro.
    wp_auto.
    clear sema n unfinished_waiters Hunfinished_zero_wg Hunfinished_bound_wg
               unfinished_waiters0 Hunfinished_zero_wg0 Hunfinished_bound_wg0.

    rewrite enc_get_bubble; [ | word.. ]. wp_auto.
    wp_apply (wp_runtime_SemacquireWaitGroup with "[$]").
    iInv "Hinv" as ">Hi" "Hclose".
    iNamedSuffix "Hi" "_wg".
    iApply fupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hmask".
    iExists _; iFrame "Hsema_wg".
    iIntros "%Hsem Hsema_wg".
    destruct (uint.nat sema) eqn:Hsema.
    { exfalso. lia. }
    replace (S n) with (1 + n)%nat by done.
    iDestruct (own_toks_add with "Hsema_zerotoks_wg") as "[Hzerotok Hsema_zerotoks_wg]".
    iMod "Hmask" as "_".
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]") as "_".
    {
      iNext. iNamed "Hi". iFrame.
      replace (uint.nat (word.sub sema (W32 1))) with n by word.
      iFrame. done.
    }
    iModIntro.
    wp_auto.
    wp_apply (wp_Uint64__Load).
    iInv "Hinv" as ">Hi" "Hclose".
    iClear "v w state". clear dependent v_ptr counter w_ptr waiters state_ptr.
    clear unfinished_waiters sema n Hsema Hsem Hunfinished_zero_wg Hunfinished_bound_wg.
    iNamedSuffix "Hi" "_wg".
    iApply fupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hmask".
    iExists _. iFrame "Hptsto_wg".
    iCombine "Hzeroauth_wg Hzerotok" gives %Hunfinished_pos.
    specialize (Hunfinished_zero_wg ltac:(lia)) as [-> ->].
    iIntros "Hptsto_wg".
    iMod "Hmask" as "_".

    (* now, deallocate Htok. *)
    destruct unfinished_waiters; first by (exfalso; lia).
    iMod (own_tok_auth_delete_S with "Hzeroauth_wg Hzerotok") as "Hzeroauth_wg".
    replace (S _) with (1 + unfinished_waiters)%nat by done.
    iDestruct (own_toks_add with "Hunfinished_wait_toks_wg") as "[HR Hunfinished_wait_toks_wg]".
    iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as (?) "[Hwg HΦ]".
    { solve_ndisj. }
    iCombine "Hwg Hctr_wg" gives %[_ ->].
    iMod ("HΦ" with "[//] [$Hwg]") as "HΦ".
    iMod "Hmask".
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]") as "_".
    { iNamed "Hi". iFrame. iPureIntro. split; [done | word]. }
    iModIntro.
    wp_auto.
    wp_for_post.
    iApply "HΦ". done.
  }
  {
    iFrame "Hptsto_wg".
    iSplitR; first done.
    iIntros "Hptsto_wg".
    iMod "Hmask" as "_".
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]") as "_".
    { iNamed "Hi". iFrame. done. }
    iModIntro. wp_auto.
    wp_for_post.
    iFrame.
  }
Qed.

End proof.
