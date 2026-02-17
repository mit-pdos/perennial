From New.proof.sync_proof Require Import base sema.
From New.experiments Require Import glob.
From coqutil Require Import Z.bitblast.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : sync.Assumptions}.
Local Set Default Proof Using "All".

Local Definition waitGroupBubbleFlag := 2147483648.
Example waitGroupBubbleFlag_ok : #waitGroupBubbleFlag = sync.waitGroupBubbleFlag :=
  eq_refl.

Local Definition enc (wait counter : w32) : w64 :=
  word.add (word.slu (W64 (uint.Z counter)) (W64 32)) (W64 (uint.Z wait)).

Local Lemma enc_get_counter (wait counter : w32) :
  W32 (uint.Z (word.sru (enc wait counter) (W64 32))) = counter.
Proof. unfold enc. word. Qed.

Lemma word_and_modu (x : w64) :
  word.and x (W64 2147483647) = word.modu x (W64 2147483648).
Proof.
  ltac2:(Automation.word.normalize (fun () => ())). apply H.
  replace (2147483647) with (Z.ones 31) by done.
  rewrite Z.land_ones; word.
Qed.

Lemma Zltb_decide a b :
  Z.ltb a b = (if decide (a < b) then true else false).
Proof.
  pose proof (Zlt_cases a b).  destruct (a <? b).
  - rewrite decide_True //.
  - rewrite decide_False //.
Qed.

Lemma Zeqb_decide a b :
  Z.eqb a b = (if decide (a = b) then true else false).
Proof.
  pose proof (Zeq_bool_if a b). destruct (a =? b).
  - rewrite decide_True //.
  - rewrite decide_False //.
Qed.

Ltac bit_solve :=
  repeat first [
      rewrite -!Z.land_ones; [|lia..] |
      rewrite !Z.land_spec |
      rewrite Z.mul_pow2_bits; last lia |
      rewrite (Z.testbit_mod_pow2 _ 1); last lia |
      rewrite Z.div_pow2_bits'; [|lia..] |
      rewrite Z.pow2_bits_eqb; [|lia..] |
      rewrite !Zltb_decide |
      rewrite !Zeqb_decide |
      destruct decide |
      progress subst |
      lia |
      rewrite !andb_true_r |
      reflexivity
    ].

Lemma word_and_div (x : w64) :
  word.and x (W64 2147483648) =
  word.slu (word.modu (word.divu x (W64 2147483648)) (W64 2)) (W64 31).
Proof.
  ltac2:(Automation.word.normalize (fun () => ())). apply H.
  Z.bitblast.
  replace 18446744073709551616 with (2^64) by done.
  replace 2147483648 with (2^31) by done.
  bit_solve.
Qed.

Local Lemma enc_get_wait (wait counter : w32) :
  0 ≤ sint.Z wait →
  W32 (uint.Z (word.and (enc wait counter) (W64 2147483647))) = wait.
Proof.
  unfold enc. rewrite word_and_modu.
  (* FIXME: word should do a better job of simplifying constants. *)
  ltac2:(Automation.word.normalize (fun () => ())).

  set (x1:=2 ^ (32 `mod` 2 ^ 64)) in *.
  set (x2:=(2147483648 `mod` 2^64)) in *.
  set (y1:=2 ^ 32) in *.
  set (y2:=2 ^ 64) in *.
  compute in x1, x2, y1, y2.
  word.
Qed.

Local Lemma enc_add_counter (wait counter delta : w32) :
  word.add (enc wait counter) (word.slu (W64 (sint.Z delta)) (W64 32)) =
  enc wait (word.add counter delta).
Proof. unfold enc. word. Qed.

Local Lemma enc_add_wait (wait counter : w32) :
  0 ≤ sint.Z wait →
  (word.add (enc wait counter) (W64 1)) = enc (word.add (W32 1) wait) counter.
Proof. unfold enc. word. Qed.

Local Lemma enc_get_waitGroupBubbleFlag (wait counter : w32) :
  0 ≤ sint.Z wait →
  word.and (enc wait counter) (W64 waitGroupBubbleFlag) =
  W64 0.
Proof.
  unfold enc. unfold waitGroupBubbleFlag. rewrite word_and_div.
  (* FIXME: word should do a better job of simplifying constants. *)
  ltac2:(Automation.word.normalize (fun () => ())).

  set (x1:=2 ^ (32 `mod` 2 ^ 64)) in *.
  set (x2:=(2147483648 `mod` 2^64)) in *.
  set (x3:=(2 ^ (31 `mod` 2 ^ 64))) in *.
  set (x4:=(2 `mod` 2 ^ 64)) in *.
  set (y1:=2 ^ 32) in *.
  set (y2:=2 ^ 64) in *.
  compute in x1, x2, x3, x4, y1, y2.
  word.
Qed.

Local Lemma enc_inj (wait counter wait' counter' : w32) :
  enc wait counter = enc wait' counter' →
  wait = wait' ∧ counter = counter'.
Proof. unfold enc. intros. word. Qed.

Local Lemma enc_0 :
  W64 0 = enc (W32 0) (W32 0).
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
  inv (N.@"wg") (∃ (counter wait sema : w32) unfinished_waiters possible_waiters,
  "Hsema" ∷ own_sema γ.(sema_gn) sema ∗
  "Hsema_zerotoks" ∷  own_toks γ.(zerostate_gn) (uint.nat sema) ∗

  "Hptsto" ∷ own_Uint64 (struct_field_ref sync.WaitGroup.t "state" wg) (DfracOwn (1/2)) (enc wait counter) ∗
  "Hptsto2" ∷ (
      if decide (counter = W32 0 ∧ wait ≠ W32 0) then True
      else own_Uint64 (struct_field_ref sync.WaitGroup.t "state" wg) (DfracOwn (1/2)) (enc wait counter)
    ) ∗
  "Hctr" ∷ ghost_var γ.(counter_gn) (1/2)%Qp counter ∗

  (* When Add's caller has [own_waiters 0], this resource implies that there are no waiters. *)
  "Hwait_toks" ∷ own_toks γ.(waiter_gn) (sint.nat wait) ∗
  "Hunfinished_wait_toks" ∷ own_toks γ.(waiter_gn) unfinished_waiters ∗

  "Hzeroauth" ∷ own_tok_auth γ.(zerostate_gn) unfinished_waiters ∗

  (* Keeping this to maintain that the number of waiters does not overflow. *)
  "Hwaiters_bounded" ∷ own_tok_auth_dfrac γ.(waiter_gn) (DfracOwn (1/2)) possible_waiters ∗
  "%Hpossible_waiters_bound" ∷ ⌜ Z.of_nat possible_waiters < 2^31 ⌝ ∗

  "%Hunfinished_zero" ∷ ⌜ unfinished_waiters ≠ O → wait = W32 0 ∧ counter = W32 0 ⌝ ∗
  "%Hunfinished_bound" ∷ ⌜ Z.of_nat unfinished_waiters < 2^32 ⌝ ∗
  "%Hwaiter_notbubbled" ∷ ⌜ 0 ≤ sint.Z wait < 2^31 ⌝
  )%I.

Definition is_WaitGroup wg γ N : iProp Σ :=
  "#Hsem" ∷ is_sema (struct_field_ref sync.WaitGroup.t "sema" wg) γ.(sema_gn) (N.@"sema") ∗
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
Lemma alloc_wait_token wg γ N w :
  0 < w + 1 < 2^31 →
  is_WaitGroup wg γ N -∗
  own_WaitGroup_waiters γ w ={↑N}=∗ own_WaitGroup_waiters γ (w + 1) ∗ own_WaitGroup_wait_token γ.
Proof.
  intros H. iIntros "[_ #Hinv] H".
  iInv "Hinv" as ">Hi". iNamed "Hi".
  iCombine "Hwaiters_bounded H" gives %[_ ->].
  iCombine "Hwaiters_bounded H" as "H".
  iMod (own_tok_auth_add 1 with "H") as "[H Htok]".
  iModIntro. rewrite <- (Z2Nat.inj_add _ 1) by word.
  iDestruct "H" as "[H1 H2]". iSplitR "Htok H2"; iFrame; word.
Qed.

Lemma waiters_none_token_false γ :
  own_WaitGroup_waiters γ 0 -∗ own_WaitGroup_wait_token γ -∗ False.
Proof.
  iIntros "H1 H2". iCombine "H1 H2" gives %H. word.
Qed.

Lemma dealloc_wait_token wg γ N w :
  0 ≤ w - 1 →
  is_WaitGroup wg γ N -∗
  own_WaitGroup_waiters γ w -∗
  own_WaitGroup_wait_token γ ={↑N}=∗
  own_WaitGroup_waiters γ (w - 1).
Proof.
  intros H. iIntros "[_ #Hinv] H Htok".
  iInv "Hinv" as ">Hi". iNamedSuffix "Hi" "_wg".
  iCombine "Hwaiters_bounded_wg H" gives %[_ ->].
  iCombine "Hwaiters_bounded_wg H" as "H".
  iCombine "H Hunfinished_wait_toks_wg" gives %Hle.
  iMod (own_tok_auth_sub with "H Htok") as "[H Hwaiters_bounded_wg]".
  iModIntro. iFrame "∗#%".
  replace (Z.to_nat w - 1)%nat with (Z.to_nat (w - 1)) by word.
  iFrame. word.
Qed.

Definition own_WaitGroup γ (counter : w32) : iProp Σ :=
  ghost_var γ.(counter_gn) (1/2)%Qp counter.
#[global] Opaque own_WaitGroup.
#[local] Transparent own_WaitGroup.
#[global] Instance own_WaitGroup_timeless γ counter : Timeless (own_WaitGroup γ counter) := _.

Lemma init_WaitGroup N wg_ptr :
  wg_ptr ↦ zero_val sync.WaitGroup.t ={⊤}=∗
  ∃ γ,
  is_WaitGroup wg_ptr γ N ∗ own_WaitGroup γ (W32 0) ∗ own_WaitGroup_waiters γ 0.
Proof.
  iIntros "H". iStructNamed "H". simpl.

  iMod (ghost_var_alloc (W32 0)) as "[%counter_gn [Hctr1 Hctr2]]".
  iMod (init_sema with "[$sema]") as "[%sema_gn [Hs1 Hs2]]".
  iMod (own_tok_auth_alloc) as "[%waiter_gn [Hwaiters Hw2]]".
  iMod (own_tok_auth_alloc) as "[%zerostate_gn Hzerostate]".

  iExists {| sema_gn := sema_gn; counter_gn := counter_gn; zerostate_gn := zerostate_gn; waiter_gn := waiter_gn |}.
  iFrame "∗#".
  unfold is_WaitGroup.
  iDestruct "state" as "[state state2]".
  iMod (own_toks_0 waiter_gn) as "?".
  iMod (own_toks_0 waiter_gn) as "?".
  iMod (own_toks_0 zerostate_gn) as "?".
  iMod (inv_alloc with "[-]") as "$".
  { iNext. repeat iExists (W32 0). iFrame. done. }
  done.
Qed.

Local Lemma wg_delta_to_w32 (delta' : w32) (delta : w64) :
  delta' = (W32 (sint.Z delta)) →
  word.slu delta (W64 32) = word.slu (W64 (sint.Z delta')) (W64 32).
Proof. intros. word. Qed.

(* XXX: overflow?
  https://github.com/golang/go/issues/20687
  https://go-review.googlesource.com/c/go/+/140937/2/src/sync/waitgroup.go *)

Lemma wp_WaitGroup__Add (wg : loc) (delta : w64) γ N :
  let delta' := (W32 (sint.Z delta)) in
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N -∗
  (|={⊤,↑N}=>
     ▷ ∃ oldc,
       "Hwg" ∷ own_WaitGroup γ oldc ∗
       "%Hbounds" ∷ ⌜ 0 ≤ sint.Z oldc + sint.Z delta' < 2^31 ⌝ ∗
       "HΦ" ∷ ((⌜ oldc ≠ W32 0 ⌝ ∗ (own_WaitGroup γ (word.add oldc delta') ={↑N,⊤}=∗ Φ #())) ∨
         (own_WaitGroup_waiters γ 0 ∗
          (own_WaitGroup_waiters γ 0 -∗ own_WaitGroup γ (word.add oldc delta') ={↑N,⊤}=∗
           Φ #())))
  ) -∗
  WP wg @! (go.PointerType sync.WaitGroup) @! "Add" #delta {{ Φ }}.
Proof.
  intros delta'.
  wp_start as "#His".
  wp_apply wp_with_defer as "%defer defer".
  simpl subst. wp_auto. wp_apply wp_IsInBubble.
  wp_apply wp_Uint64__Add.
  iMod "HΦ".
  unfold own_WaitGroup.
  iNamed "His".
  iInv "Hinv" as ">Hi" "Hclose".
  iApply fupd_mask_intro. { solve_ndisj. } iIntros "Hmask".
  iNext. iNamedSuffix "Hi" "_wg". iNamed "HΦ".
  iCombine "Hctr_wg Hwg" as "Hctr" gives %[_ ->].
  destruct decide as [Hw|HnotInWakingState].
  {
    iExFalso.
    destruct Hw as [-> Hw].
    iDestruct "HΦ" as "[(% & _)|(HnoWaiter & HΦ)]"; first by exfalso.
    iDestruct "HnoWaiter" as "[_ HnoWaiter]".
    iCombine "HnoWaiter Hwait_toks_wg" gives %Hbad.
    exfalso. apply Hw. word.
  }
  iCombine "Hptsto_wg Hptsto2_wg" as "Hptsto".
  iExists _. iFrame.
  rewrite (wg_delta_to_w32 delta') // enc_add_counter.
  iMod (ghost_var_update (word.add oldc delta') with "Hctr") as "[Hctr_wg Hwg]".
  iIntros "[Hptsto1_wg Hptsto2_wg]".
  destruct unfinished_waiters.
  2:{
    iExFalso. destruct (Hunfinished_zero_wg ltac:(done)) as [-> ->].
    iDestruct "HΦ" as "[(% & _)|(HnoWaiter & HΦ)]"; first by exfalso.
    iDestruct "HnoWaiter" as "[_ HnoWaiter]".
    iCombine "HnoWaiter Hunfinished_wait_toks_wg" gives %Hbad. word.
  }
  subst.
  destruct (decide (word.add oldc delta' = W32 0 ∧ wait ≠ W32 0)) as [Hwake|HnoWake].
  2:{ (* not done, no need to wake waiters. *)
    iMod "Hmask" as "_".
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]").
    {
      iNamed "Hi". iNext. iFrame.
      rewrite decide_False; last intuition.
      iFrame. done.
    }
    iAssert (|={_,_}=> Φ #())%I with "[HΦ Hwg]" as ">HΦ".
    { iDestruct "HΦ" as "[(_ & HΦ)|(? & HΦ)]".
      - iMod ("HΦ" with "[$]"). done.
      - iMod ("HΦ" with "[$] [$]"). done. }
    iModIntro.
    wp_auto.
    rewrite enc_get_waitGroupBubbleFlag; last lia.
    rewrite bool_decide_true; last done. wp_auto.
    rewrite -> enc_get_wait; last lia.
    rewrite -> enc_get_counter.

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
          replace (W32 (sint.Z delta)) with delta' by reflexivity.
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
    iFrame. rewrite decide_True; last intuition. done.
  }
    iAssert (|={_,_}=> Φ #())%I with "[HΦ Hwg]" as ">HΦ".
    { iDestruct "HΦ" as "[(_ & HΦ)|(? & HΦ)]".
      - iMod ("HΦ" with "[$]"). done.
      - iMod ("HΦ" with "[$] [$]"). done. }
  iModIntro.
  wp_auto.

  rewrite enc_get_waitGroupBubbleFlag; last lia.
  rewrite bool_decide_true; last done. wp_auto.
  rewrite -> enc_get_wait; last lia.
  rewrite -> enc_get_counter.

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
        replace (W32 (sint.Z delta)) with delta' by reflexivity.
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
  iIntros "Hmask". iNext.
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
  iIntros "Hmask". iNext.
  clear Hunfinished_zero_wg sema.
  iNamedSuffix "Hi" "_wg".
  iClear "Hptsto2_wg".
  iCombine "Hptsto Hptsto_wg"  gives %Heq.
  apply enc_inj in Heq as [<- <-].
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
  iMod (own_tok_auth_add (sint.nat wait) with "[$Hzeroauth_wg]") as "[Hzeroauth_wg Hzerotoks_wg]".
  iEval (rewrite enc_0) in "Hptsto".
  iDestruct "Hptsto" as "[Hptsto1_wg Hptsto2_wg]".
  destruct Hwake as [Hwake1 Hwake2].
  rewrite Hwake1.
  iMod (own_toks_0 γ.(waiter_gn)) as "Hwait_toks'_wg".
  iRename "Hzerotoks_wg" into "Hzerotoks". (* remove from invariant. *)
  iCombineNamed "*_wg" as "Hi".
  iMod ("Hclose" with "[Hi]") as "_".
  { iNext. iNamed "Hi". iFrame "Hptsto1_wg ∗". simpl. iPureIntro. split; [done | word]. }
  iModIntro.
  wp_auto.
  (* call semrelease. *)

  iAssert (
      ∃ (wrem : w32),
        "w" ∷ w_ptr ↦ wrem ∗
        "Hzerotoks" ∷ own_toks γ.(zerostate_gn) (sint.nat wrem) ∗
        "%Hwrem_nonneg" ∷ ⌜ 0 ≤ sint.Z wrem ⌝
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
  replace (sint.nat wrem)%nat with (1+(sint.nat (word.sub wrem (W32 1))))%nat by word.
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
  iModIntro. wp_auto. wp_for_post. iFrame. word.
Qed.

Lemma wp_WaitGroup__Done (wg : loc) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N -∗
  (|={⊤,↑N}=>
     ▷ ∃ oldc,
       "Hwg" ∷ own_WaitGroup γ oldc ∗
       "%Hbounds" ∷ ⌜ 0 ≤ sint.Z oldc - 1 < 2^31 ⌝ ∗
       "HΦ" ∷ (own_WaitGroup γ (word.sub oldc (W32 1)) ={↑N,⊤}=∗ Φ #())
  ) -∗
  WP wg @! (go.PointerType sync.WaitGroup) @! "Done" #() {{ Φ }}.
Proof.
  wp_start as "#His".
  wp_auto.
  wp_apply (wp_WaitGroup__Add with "[$]").
  iMod "HΦ". iModIntro. iNext. iNamed "HΦ".
  replace (W32 (uint.Z (W64 (-1)))) with (W32 (-1)) by done.
  replace (sint.Z (W32 (-1))) with (-1) by done.
  iFrame "Hwg". iSplitR; first word.
  iLeft. iSplitR; first word. iIntros "Hctr".
  iMod ("HΦ" with "[Hctr]") as "HΦ".
  { iExactEq "Hctr". repeat f_equal. word. }
  iModIntro. wp_auto. iApply "HΦ".
Qed.

Lemma wp_WaitGroup__Wait (wg : loc) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N ∗ own_WaitGroup_wait_token γ -∗
  (|={⊤∖↑N, ∅}=>
     ▷ ∃ oldc,
       own_WaitGroup γ oldc ∗ (⌜ sint.Z oldc = 0 ⌝ → own_WaitGroup γ oldc ={∅,⊤∖↑N}=∗
                               own_WaitGroup_wait_token γ -∗ Φ #())
  ) -∗
  WP wg @! (go.PointerType sync.WaitGroup) @! "Wait" #() {{ Φ }}.
Proof.
  wp_start as "(#Hwg & HR_in)". iNamed "Hwg".
  wp_auto.
  wp_for.
  wp_apply (wp_Uint64__Load).
  iInv "Hinv" as ">Hi" "Hclose".
  iNamedSuffix "Hi" "_wg".
  destruct (decide (counter = W32 0)).
  { (* counter is zero, so can return. *)
    subst.

    iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as (?) "[Hwg HΦ]".
    { solve_ndisj. }
    iModIntro. iNext.
    iCombine "Hwg Hctr_wg" gives %[_ ->].
    iExists _.
    iFrame.
    iIntros "Hptsto_wg".
    iMod ("HΦ" with "[//] [$Hwg]") as "HΦ".
    iMod "Hmask" as "_".
    iCombineNamed "*_wg" as "Hi".
    iMod ("Hclose" with "[Hi]").
    { iNamed "Hi". by iFrame. }
    iModIntro.
    wp_auto.
    rewrite enc_get_counter enc_get_wait; [|lia..].
    rewrite bool_decide_true //=.
    wp_auto.
    wp_if_destruct.
    - wp_for_post. by iApply "HΦ".
    - wp_for_post. by iApply "HΦ".
  }
  (* actually go to sleep *)
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask !>".
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
  rewrite enc_get_counter enc_get_wait; last lia.
  rewrite bool_decide_false //.
  wp_auto.
  rewrite -> enc_add_wait by word.
  wp_apply (wp_Uint64__CompareAndSwap).
  iInv "Hinv" as ">Hi" "Hclose".
  iNamedSuffix "Hi" "_wg".
  setoid_rewrite bool_decide_decide.
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask !>".
  iExists (enc wait0 counter0).
  destruct (decide (_ = _)) as [Heq|Hneq].
  {
    apply enc_inj in Heq as [-> ->].
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
      replace (sint.nat (word.add (W32 1) wait)) with (1 + sint.nat wait)%nat by word.
      simpl. iFrame.
      iSplitL.
      { by destruct decide. }
      iPureIntro. word.
    }
    iModIntro.
    wp_auto.
    clear sema n unfinished_waiters Hunfinished_zero_wg Hunfinished_bound_wg
      Hwaiter_notbubbled_wg0
      unfinished_waiters0 Hunfinished_zero_wg0 Hunfinished_bound_wg0.

    rewrite -> enc_get_waitGroupBubbleFlag by lia. wp_auto.
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
    clear counter wait HwaitersLe Hwaiter_notbubbled_wg.
    clear unfinished_waiters sema n Hsema Hsem Hunfinished_zero_wg Hunfinished_bound_wg.
    iNamedSuffix "Hi" "_wg".
    iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as (?) "[Hwg HΦ]".
    { solve_ndisj. } iModIntro. iNext.
    iExists _. iFrame "Hptsto_wg".
    iCombine "Hzeroauth_wg Hzerotok" gives %Hunfinished_pos.
    specialize (Hunfinished_zero_wg ltac:(lia)) as [-> ->].
    iIntros "Hptsto_wg".

    (* now, deallocate Htok. *)
    destruct unfinished_waiters; first by (exfalso; lia).
    iMod (own_tok_auth_delete_S with "Hzeroauth_wg Hzerotok") as "Hzeroauth_wg".
    replace (S _) with (1 + unfinished_waiters)%nat by done.
    iDestruct (own_toks_add with "Hunfinished_wait_toks_wg") as "[HR Hunfinished_wait_toks_wg]".
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

End wps.
