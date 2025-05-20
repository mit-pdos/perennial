From Perennial.Helpers Require Import List ModArith.

(* this file verifies std and std_core *)
From Goose.github_com.goose_lang Require Import std.std_core.
From Goose.github_com.goose_lang Require Import std.

From iris.algebra Require Import excl gset.
From stdpp Require Import list.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import typed_slice.

Class multiparG Σ : Set :=
   { #[global] multiparG_auth :: inG Σ (gset_disjR nat);
     #[global] multiparG_tok :: inG Σ (exclR unitO) }.
Definition multiparΣ := #[GFunctor (gset_disjR nat); GFunctor (exclR unitO)].
Global Instance subG_multiparΣ {Σ} :
  subG multiparΣ Σ → multiparG Σ.
Proof. solve_inG. Qed.

Section goose_lang.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.

Implicit Types (v:val).

(* This lemma shadows the one for primitive.Assert *)
Lemma wp_Assert stk E cond :
  {{{ ⌜cond = true⌝ }}}
    Assert #cond @ stk; E
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "% HΦ". subst.
  wp_rec. wp_pures.
  iModIntro.
  by iApply "HΦ".
Qed.

Local Lemma take_S_lookup_ne {T} (xs : list T) i j :
  i ≠ j →
  take (S i) xs !! j = take i xs !! j.
Proof.
  destruct (le_lt_dec i j) as [Hle|Hlt].
  - intros ?. rewrite lookup_take_ge; last by lia.
    rewrite lookup_take_ge; last by lia. done.
  - rewrite lookup_take. 2:lia.
    rewrite lookup_take. 2:lia.
    done.
Qed.

Lemma inv_litint (i1 i2: w64) :
  #i1 = #i2 ↔ i1 = i2.
Proof.
  split; [ | congruence ].
  inversion 1; auto.
Qed.

Lemma wp_BytesEqual (x y : Slice.t) (xs ys : list byte) qx qy :
  {{{ own_slice_small x byteT qx xs ∗
      own_slice_small y byteT qy ys }}}
    BytesEqual (slice_val x) (slice_val y)
  {{{ RET #(bool_decide (xs = ys));
      own_slice_small x byteT qx xs ∗
      own_slice_small y byteT qy ys }}}.
Proof.
  iIntros (Φ) "[Hx Hy] HΦ". wp_rec. wp_pures.
  do 2 wp_apply wp_slice_len.
  wp_pures.
  iDestruct (own_slice_small_sz with "Hx") as %Hxlen.
  iDestruct (own_slice_small_sz with "Hy") as %Hylen.
  rewrite -bool_decide_not.
  destruct_decide (bool_decide_reflect (#x.(Slice.sz) ≠ #y.(Slice.sz))) as Hlen; wp_pures.
  { (* Different lengths. *)
    rewrite bool_decide_false.
    { iModIntro. iApply ("HΦ" with "[$]"). }
    intros <-.
    contradiction Hlen.
    do 2 f_equal.
    word. }
  wp_pures.
  apply inv_litint in Hlen.
  assert (length xs = length ys) as Hlens by congruence.

  wp_apply wp_ref_to; first by val_ty.
  iIntros (l) "Hi". wp_pures.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (ret) "Hret". wp_pures.

  iApply (wp_frame_wand with "HΦ").

  (* Weaken for loop invariant *)
  iAssert (∃ i : w64, l ↦[uint64T] #i ∗
                      ret ↦[boolT] #(bool_decide (take (uint.nat i) xs = take (uint.nat i) ys)))%I
    with "[Hi Hret]" as "Hinv".
  { iExists _. by iFrame. }

  wp_apply (wp_forBreak_cond' with "[-]"); first by iNamedAccu.
  iIntros "!# HP". iNamed "HP".
  iDestruct "Hinv" as (i) "[Hi Hret]".
  wp_pures.
  wp_load.
  wp_if_destruct; last first.
  { (* i >= length *)
    iModIntro.
    iRight. iSplit; first done. wp_load.
    iIntros "!> HΦ". iDestruct ("HΦ" with "[$Hx $Hy]") as "HΦ".
    iExactEq "HΦ".
    repeat f_equal.
    apply bool_decide_ext.
    rewrite take_ge; [ | len ].
    rewrite take_ge; [ | len ].
    auto. }
  wp_pures.
  destruct (lookup_lt_is_Some_2 xs (uint.nat i)) as [xi Hxi]; first word.
  destruct (lookup_lt_is_Some_2 ys (uint.nat i)) as [yi Hyi]; first word.
  wp_load.
  (* FIXME: some typeclass is set up wrong so TC inference picks the wrong type here *)
  wp_apply (wp_SliceGet (V:=u8) with "[$Hx]").
  { eauto. }
  iIntros "Hx".
  wp_load.
  wp_apply (wp_SliceGet (V:=u8) with "[$Hy]").
  { eauto. }
  iIntros "Hy".
  wp_pures.
  wp_if_destruct.
  - (* this index is inequal *)
    wp_store. iModIntro. iRight. iSplit; first done.
    wp_load. iModIntro.
    case_bool_decide as Heq.
    + exfalso. apply Heqb0. do 2 f_equal.
      apply Some_inj. rewrite -Hxi -Hyi Heq. done.
    + iIntros "HΦ". iApply "HΦ". eauto with iFrame.
  - (* this index is equal *)
    wp_load. wp_store.
    iModIntro. iLeft. iSplit; first done.
    iFrame "Hx Hy". iExists (word.add i (W64 1)).
    iFrame "Hi".
    iExactEq "Hret".
    repeat f_equal.
    apply bool_decide_ext.
    replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
    erewrite take_S_r by eauto.
    erewrite take_S_r by eauto.
    split; [ congruence | ].
    intros Heq.
    apply app_inv_tail in Heq; auto.
Qed.

Lemma wp_BytesClone sl_b q (b : list u8) :
  {{{
    own_slice_small sl_b byteT q b
  }}}
  BytesClone (slice_val sl_b)
  {{{
    sl_b0, RET (slice_val sl_b0);
    own_slice_small sl_b0 byteT (DfracOwn 1) b
  }}}.
Proof.
  iIntros (Φ) "Hsl_b HΦ".
  rewrite /BytesClone.
  wp_pures.
  wp_pure; [done|].
  wp_if_destruct.
  {
    iIntros "!>".
    iSpecialize ("HΦ" $! Slice.nil).
    iApply "HΦ".
    inversion Heqb0.
    apply (f_equal uint.Z) in H1.
    iDestruct (own_slice_small_nil _ (DfracOwn 1)) as "Hsl_b'"; [done|].
    iDestruct (own_slice_small_agree with "[$Hsl_b] [$Hsl_b']") as %Heq.
    destruct b; [|done].
    iApply own_slice_to_small.
    iApply own_slice_zero.
  }
  {
    wp_apply wp_NewSlice.
    iIntros (sl_b0) "Hsl_b0".
    replace (uint.nat 0) with (0%nat) by word.
    wp_apply (wp_SliceAppendSlice with "[$Hsl_b $Hsl_b0]"); [done|].
    iIntros (?) "[Hs' _]".
    iDestruct (own_slice_to_small with "Hs'") as "Hs'".
    by iApply "HΦ".
  }
Qed.

Lemma wp_SliceSplit t s dq `{!IntoVal V} (xs: list V) (n: w64) :
  {{{ own_slice_small s t dq xs ∗ ⌜uint.Z n < Z.of_nat (length xs)⌝ }}}
    SliceSplit t (to_val s) #n
  {{{ RET (to_val (slice_take s n), to_val (slice_skip s t n));
      own_slice_small (slice_take s n) t dq (take (uint.nat n) xs) ∗
      own_slice_small (slice_skip s t n) t dq (drop (uint.nat n) xs)
  }}}.
Proof.
  iIntros (Φ) "[Hs %Hn] HΦ".
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  iDestruct (own_slice_small_wf with "Hs") as %Hcap.
  wp_rec. wp_pures.
  wp_apply wp_SliceTake.
  { word. }
  wp_apply wp_SliceSkip.
  { word. }
  wp_pures. iModIntro. iApply "HΦ".
  iDestruct (slice_small_split with "Hs") as "[$ $]".
  word.
Qed.

Lemma wp_SliceSplit_full `{!IntoVal V} t s dq (xs: list V) (n: w64) :
  {{{ own_slice s t dq xs ∗ ⌜uint.Z n < Z.of_nat (length xs)⌝ }}}
    SliceSplit t (to_val s) #n
  {{{ RET (to_val (slice_take s n), to_val (slice_skip s t n));
      own_slice_small (slice_take s n) t dq (take (uint.nat n) xs) ∗
      own_slice (slice_skip s t n) t dq (drop (uint.nat n) xs)
  }}}.
Proof.
  iIntros (Φ) "[Hs %Hn] HΦ".
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  iDestruct (own_slice_split_1 with "Hs") as "[Hs Hcap]".
  wp_apply (wp_SliceSplit with "[$Hs]"); [ done | ].
  iIntros "[Htake Hskip]".
  iApply "HΦ". iFrame "Htake".
  iApply own_slice_split; iFrame "Hskip".
  iApply (own_slice_cap_skip with "Hcap"). word.
Qed.

Lemma wp_std_core_SumNoOverflow (x y : u64) stk E :
  ∀ Φ : val → iProp Σ,
    Φ #(bool_decide (uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z)) -∗
    WP std_core.SumNoOverflow #x #y @ stk; E {{ Φ }}.
Proof.
  iIntros (Φ) "HΦ". wp_rec.
  wp_pures.
  iModIntro. iExactEq "HΦ".
  repeat f_equal.
  apply bool_decide_ext.
  pose proof (sum_overflow_check x y).
  destruct (decide (uint.Z x ≤ uint.Z (word.add x y))); intuition idtac.
  - word.
  - word.
Qed.

Lemma wp_SumNoOverflow (x y : u64) stk E :
  ∀ Φ : val → iProp Σ,
    Φ #(bool_decide (uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z)) -∗
    WP std.SumNoOverflow #x #y @ stk; E {{ Φ }}.
Proof.
  iIntros (Φ) "HΦ". wp_rec.
  wp_apply wp_std_core_SumNoOverflow.
  done.
Qed.

Lemma wp_std_core_SumAssumeNoOverflow (x y : u64) stk E :
  ∀ Φ : val → iProp Σ,
    (⌜uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z⌝ -∗ Φ #(LitInt $ word.add x y)) -∗
    WP std_core.SumAssumeNoOverflow #x #y @ stk; E {{ Φ }}.
Proof.
  iIntros "%Φ HΦ". wp_rec; wp_pures.
  wp_apply wp_std_core_SumNoOverflow.
  wp_apply wp_Assume.
  rewrite bool_decide_eq_true.
  iIntros (H). wp_pures. iModIntro.
  iApply "HΦ"; done.
Qed.

Lemma wp_SumAssumeNoOverflow (x y : u64) stk E :
  ∀ Φ : val → iProp Σ,
    (⌜uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z⌝ -∗ Φ #(LitInt $ word.add x y)) -∗
    WP std.SumAssumeNoOverflow #x #y @ stk; E {{ Φ }}.
Proof.
  iIntros "%Φ HΦ". wp_rec; wp_pures.
  wp_apply wp_std_core_SumAssumeNoOverflow.
  done.
Qed.

Lemma wp_MulNoOverflow (x y : u64) stk E :
  ∀ Φ : val → iProp Σ,
    Φ #(bool_decide (uint.Z (word.mul x y) = (uint.Z x * uint.Z y)%Z)) -∗
    WP MulNoOverflow #x #y @ stk; E {{ Φ }}.
Proof.
  iIntros (Φ) "HΦ".
  wp_rec; wp_pures.
  wp_bind (If #(_) _ _).
  wp_if_destruct; wp_pures.
  - iModIntro.
    rewrite bool_decide_eq_true_2 //.
  - wp_if_destruct; wp_pures.
    + iModIntro.
      rewrite bool_decide_eq_true_2 //.
      word.
    + iModIntro.
      iExactEq "HΦ".
      repeat f_equal.
      apply bool_decide_ext.
      pose proof (mul_overflow_check_correct x y ltac:(word)).
      change (word.sub (word.slu (W64 1) (W64 64)) (W64 1)) with (W64 (2^64-1)).
      word.
Qed.

Lemma wp_MulAssumeNoOverflow (x y : u64) stk E :
  ∀ Φ : val → iProp Σ,
    (⌜uint.Z (word.mul x y) = (uint.Z x * uint.Z y)%Z⌝ -∗ Φ #(LitInt $ word.mul x y)) -∗
    WP MulAssumeNoOverflow #x #y @ stk; E {{ Φ }}.
Proof.
  iIntros (Φ) "HΦ".
  wp_rec; wp_pures.
  wp_apply wp_MulNoOverflow.
  wp_apply (wp_Assume).
  iIntros (H). wp_pures.
  iModIntro.
  iApply "HΦ".
  apply bool_decide_eq_true in H.
  iPureIntro; word.
Qed.

Definition is_JoinHandle (l: loc) (P: iProp Σ): iProp _ :=
  ∃ (mu_l cond_l: loc),
  "#mu" ∷ l ↦[JoinHandle :: "mu"]□ #mu_l ∗
  "#cond" ∷ l ↦[JoinHandle :: "cond"]□ #cond_l ∗
  "#Hcond" ∷ is_cond cond_l (#mu_l) ∗
  "#Hlock" ∷ is_lock (nroot .@ "JoinHandle") (#mu_l)
     (∃ (done_b: bool),
         "done_b" ∷ l ↦[JoinHandle :: "done"] #done_b ∗
         "HP" ∷ if done_b then P else True)
.

Lemma wp_newJoinHandle (P: iProp Σ) :
  {{{ True }}}
    newJoinHandle #()
  {{{ (l: loc), RET #l; is_JoinHandle l P }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec.
  rewrite -wp_fupd.
  wp_apply (wp_new_free_lock). iIntros (mu_l) "Hlock".
  wp_apply (wp_newCond' with "Hlock"). iIntros (cond_l) "[Hlock Hcond]".
  wp_pures.
  wp_apply wp_allocStruct; [ val_ty | ].
  iIntros (l) "Hhandle".
  iNamedStruct "Hhandle".
  iMod (struct_field_pointsto_persist with "mu") as "mu".
  iMod (struct_field_pointsto_persist with "cond") as "cond".
  iMod (alloc_lock (nroot .@ "JoinHandle") _ _
          (∃ (done_b: bool),
         "done_b" ∷ l ↦[JoinHandle :: "done"] #done_b ∗
         "HP" ∷ if done_b then P else True)
          with "Hlock [$done]"
       ) as "Hlock".
  iModIntro. iApply "HΦ".
  iFrame.
Qed.

Lemma wp_JoinHandle__finish l (P: iProp Σ) :
  {{{ is_JoinHandle l P ∗ P }}}
    JoinHandle__finish #l
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "[#Hhandle P]".
  wp_rec. iNamed "Hhandle".
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "Hlock").
  iIntros "[locked Hinv]". iNamed "Hinv".
  wp_storeField. wp_loadField.
  wp_apply (wp_Cond__Signal with "[$Hcond]").
  wp_loadField.
  wp_apply (wp_Mutex__Unlock with "[$Hlock $locked done_b P]").
  { iModIntro. iFrame "done_b P". }
  wp_pures.
  iModIntro. iApply "HΦ".
  done.
Qed.

Lemma wp_Spawn (P: iProp Σ) (f: val) :
  {{{ (∀ Φ, ▷(P -∗ Φ #()) -∗ WP f #() {{ Φ }}) }}}
  Spawn f
  {{{ (l: loc), RET #l; is_JoinHandle l P }}}.
Proof.
  iIntros (Φ) "Hwp HΦ".
  wp_rec.
  wp_apply (wp_newJoinHandle P). iIntros (l) "#Hhandle".
  wp_apply (wp_fork with "[Hwp]").
  - iModIntro. wp_apply "Hwp".
    iIntros "HP".
    wp_apply (wp_JoinHandle__finish with "[$Hhandle $HP]").
    done.
  - wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame "#".
Qed.

Lemma wp_JoinHandle__Join l P :
  {{{ is_JoinHandle l P }}}
    JoinHandle__Join #l
  {{{ RET #(); P }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iNamed "Hpre".
  wp_rec. wp_loadField.
  wp_apply (wp_Mutex__Lock with "Hlock").
  iIntros "[Hlocked Hlinv]". iNamed "Hlinv".
  wp_pures.
  wp_apply (wp_forBreak (λ continue,
                (* the lock invariant has to be part of the invariant so we can
                call Cond__Wait *)
                ∃ (done_b: bool),
                "locked" ∷ locked #mu_l ∗
                "done" ∷ l ↦[JoinHandle::"done"] #done_b ∗
                "HP" ∷ (if done_b then P else True) ∗
                (* if the loop terminates, we will have P
                 (this is possible while preserving the lock invariant because
                 the code sets [done_b = false]) *)
                "Hbreak" ∷ (⌜continue = false⌝ -∗ P))%I
           with "[] [$Hlocked $done_b $HP]").
  - clear Φ.
    iIntros "!>" (Φ) "IH HΦ". iNamed "IH".
    wp_loadField.
    wp_if_destruct; subst.
    + wp_storeField.
      iModIntro.
      iApply "HΦ".
      iFrame.
      auto.
    + wp_loadField.
      wp_apply (wp_Cond__Wait with "[$Hcond $Hlock $locked done HP]").
      { iFrame. }
      iIntros "[Hlocked Hlinv]". iNamed "Hlinv".
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iFrame.
  - iIntros (Hcontra).
    exfalso; congruence.
  - iIntros "IH". iNamed "IH".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $locked $done $HP]").
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iApply "Hbreak"; auto.
Qed.

(* We pass some "ghost data" from [elems] to each invocation; [length elems] determines
   how many threads there are. *)
Lemma wp_Multipar `{!multiparG Σ} {X:Type} (P Q : nat → X → iProp Σ) (num:u64) (elems : list X) (op : val) :
  length elems = uint.nat num →
  □(∀ (i : u64) x, ⌜elems !! uint.nat i = Some x⌝ -∗ P (uint.nat i) x -∗ WP op #i {{ _, Q (uint.nat i) x }}) -∗
  {{{ [∗ list] i ↦ x ∈ elems, P i x }}}
    Multipar #num op
  {{{ RET #(); [∗ list] i ↦ x ∈ elems, Q i x }}}.
Proof.
  iIntros "%Hlen #Hop !> %Φ HPs HΦ". wp_rec.
  wp_apply wp_ref_to. { val_ty. }
  iIntros (nleft_l) "Hnleft". wp_pures.
  iMod (own_alloc (GSet (set_seq 0 (length elems)))) as (γpending) "Hpending".
  { done. }
  iMod (own_alloc (Excl ())) as (γtok) "Htok".
  { done. }
  set lock_inv := ( (∃ nleft : u64, nleft_l ↦[uint64T] #nleft ∗ own γtok (Excl ())) ∨
    ∃ (nleft : u64) (pending : gset nat),
      "%Hsz" ∷ ⌜size pending = uint.nat nleft⌝ ∗
      "Hnleft" ∷ nleft_l ↦[uint64T] #nleft ∗
      "HPQ" ∷ ([∗ list] i ↦ x ∈ elems, ⌜i ∈ pending⌝ ∨ own γpending (GSet {[i]}) ∗ Q i x)
      )%I.
  wp_apply (wp_newMutex nroot _ lock_inv with "[Hnleft]").
  { iModIntro. rewrite /lock_inv. iRight.
    iExists num, (set_seq 0 (uint.nat num)). iFrame. iSplit.
    - iPureIntro. rewrite -list_to_set_seq size_list_to_set ?length_seq //.
      apply NoDup_seq.
    - iApply big_sepL_intro. iIntros "!> %k %i %Hlk". iLeft. iPureIntro.
      apply elem_of_set_seq. split; first lia.
      rewrite -Hlen. apply lookup_lt_is_Some_1. eauto. }
  iIntros (lk) "#Hlk". wp_pures.
  wp_apply (wp_newCond with "Hlk").
  iIntros (cond) "#Hcond". wp_pures.
  (* Loop starts *)
  wp_apply wp_ref_to. { val_ty. }
  iIntros (i_l) "Hi".
  set loop_inv := (λ cur : u64,
    [∗ list] i ↦ x ∈ drop (uint.nat cur) elems, own γpending (GSet {[(uint.nat cur)+i]}) ∗ P ((uint.nat cur)+i) x)%I%nat.
  wp_apply (wp_forUpto loop_inv _ _ 0 with "[] [HPs Hpending Hi]").
  { word. }
  { clear Φ.
    iIntros "%cur !> %Φ (Hloop & Hcur & %Hcur) HΦ". wp_pures.
    wp_load.
    assert (is_Some (elems !! uint.nat cur)) as [x Hx].
    { apply lookup_lt_is_Some. word. }
    iAssert (loop_inv (word.add cur 1) ∗ own γpending (GSet {[uint.nat cur]}) ∗ P (uint.nat cur) x)%I with "[Hloop]"
      as "(Hloop & Hpending & HP)".
    { rewrite /loop_inv.
      rewrite (drop_S _ _ _ Hx).
      simpl. rewrite Nat.add_0_r.
      iDestruct "Hloop" as "(($ & $) & Hloop)".
      replace (uint.nat (word.add cur 1)) with (S (uint.nat cur)) by word.
      setoid_rewrite Nat.add_succ_r. done. }
    wp_apply (wp_fork with "[HP Hpending]").
    { iModIntro. wp_bind (op _). iApply (wp_wand with "[HP]").
      { iApply "Hop"; done. }
      iIntros (_v) "HQ". wp_pures. clear _v.
      wp_apply (wp_Mutex__Lock with "Hlk").
      iIntros "(Hlocked & [Hinv|Hinv])".
      { (* supposedly the main thread already removed all the resources...
           this cannot really happen, but we just go along with it. *)
        iDestruct "Hinv" as (nleft) "(Hnleft & Htok)".
        wp_load. wp_store.
        wp_apply (wp_Cond__Signal with "Hcond").
        wp_apply (wp_Mutex__Unlock with "[$Hlocked $Hlk Hnleft Htok]"); last done.
        iLeft. eauto with iFrame. }
      iNamed "Hinv".
      wp_load. wp_store.
      wp_apply (wp_Cond__Signal with "Hcond").
      wp_apply (wp_Mutex__Unlock with "[-]"); last done. iFrame "Hlocked Hlk".
      iRight. iExists _, (pending ∖ {[uint.nat cur]}). iFrame "Hnleft".
      iDestruct (big_sepL_lookup_acc_impl (uint.nat cur) with "HPQ") as "[Hcur Hclose]".
      { done. }
      iFreeze "Hclose".
      iDestruct "Hcur" as "[%Hpending|[Hpending2 _]]"; last first.
      { (* This index is supposedly already done -- contradiction. *)
        iDestruct (own_valid_2 with "Hpending Hpending2") as %Hval%gset_disj_valid_op.
        exfalso. set_solver. }
      iModIntro. iSplit.
      { iPureIntro. rewrite size_difference; last set_solver.
        rewrite Hsz size_singleton.
        assert (uint.nat nleft ≠ 0%nat). 2:word.
        rewrite -Hsz. intros Hemp%size_empty_inv.
        rewrite ->Hemp in Hpending. set_solver. }
      iThaw "Hclose". iApply "Hclose"; last by eauto with iFrame.
      iIntros "!> %i' %i %Hi %Hnotcur [%Hpend|Hdone]".
      - iLeft. iPureIntro. set_solver.
      - iRight. eauto. }
    wp_pures. iApply "HΦ". eauto with iFrame. }
  { (* loop invariant holds initially *)
    iFrame "Hi". rewrite /loop_inv.
    replace (uint.nat num - uint.nat 0%Z)%nat with (uint.nat num) by word.
    iClear "#". clear loop_inv lock_inv num Hlen.
    iInduction elems as [|x elems] "IH" using rev_ind; simpl.
    { done. }
    rewrite big_sepL_app big_sepL_singleton.
    rewrite big_sepL_app big_sepL_singleton.
    rewrite length_app /= Nat.add_0_r set_seq_add_L.
    change (uint.nat 0) with 0%nat. simpl.
    iDestruct "HPs" as "[HPs $]".
    rewrite [_ ∪ ∅]right_id_L -gset_disj_union; last first.
    { apply disjoint_singleton_r.
      rewrite elem_of_set_seq. lia. }
    iDestruct "Hpending" as "[Hpending $]".
    iApply ("IH" with "HPs Hpending"). }
  (* continuation after loop *)
  iIntros "_".
  wp_apply (wp_Mutex__Lock with "Hlk").
  iIntros "[Hlocked Hinv]". wp_pures.
  wp_apply (wp_forBreak_cond' with "[-]"); first iNamedAccu.
  iIntros "!> Hloop". iNamed "Hloop".
  iDestruct "Hinv" as "[Hinv|Hinv]".
  { (* Supposedly we already took out everything, but now we have the token twice -- contradiction. *)
    iDestruct "Hinv" as (?) "[_ Htok2]".
    iDestruct (own_valid_2 with "Htok Htok2") as %[]. }
  iNamed "Hinv".
  wp_load. wp_pures.
  case_bool_decide as Hleft; wp_pures.
  { (* Not yet done, once more around the loop. *)
    wp_apply (wp_Cond__Wait with "[$Hcond $Hlk $Hlocked Hnleft HPQ]").
    { rewrite /lock_inv. eauto 10 with iFrame. }
    iIntros "[Hlocked Hinv]". wp_pures.
    eauto 10 with iFrame. }
  iModIntro. iRight. iSplit; first done.
  wp_apply (wp_Mutex__Unlock with "[$Hlk $Hlocked Hnleft Htok]").
  { rewrite /lock_inv. iLeft. eauto 10 with iFrame. }
  wp_pures. iApply "HΦ".
  iApply (big_sepL_impl with "HPQ").
  iIntros "!> !> %i' %i %Hlk [%Hpending|[_ $]]".
  exfalso.
  apply Znot_lt_ge in Hleft.
  change (uint.Z 0) with 0 in Hleft.
  assert (uint.nat nleft = 0%nat) as Hnotleft by word.
  rewrite Hnotleft in Hsz.
  apply size_empty_inv in Hsz.
  set_solver.
Qed.

Lemma wp_Shuffle (s: Slice.t) (xs: list w64) :
  {{{ own_slice_small s uint64T (DfracOwn 1) xs }}}
    Shuffle (to_val s)
  {{{ xs', RET #(); ⌜Permutation xs xs'⌝ ∗
                      own_slice_small s uint64T (DfracOwn 1) xs' }}}.
Proof.
Admitted.

Lemma seqZ_plus_1 n m :
  0 ≤ m →
  seqZ n (m + 1) = seqZ n m ++ [n + m].
Proof.
  intros.
  rewrite seqZ_app; try lia.
  reflexivity.
Qed.

Lemma wp_Permutation (n: w64) :
  {{{ True }}}
    std_core.Permutation #n
  {{{ xs (s: Slice.t), RET (slice_val s);
      ⌜Permutation xs (W64 <$> seqZ 0 (uint.Z n))⌝ ∗
      own_slice_small s uint64T (DfracOwn 1) xs
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec. wp_apply wp_NewSlice.
  iIntros (s) "Hs".
  change (IntoVal_def w64) with (W64 0).
  wp_apply wp_ref_to; [ val_ty | ].
  iIntros (i_ptr) "i". wp_pures.
  wp_apply (wp_forUpto (λ (i: w64),
       own_slice_small s uint64T (DfracOwn 1) ((W64 <$> seqZ 0 (uint.Z i)) ++ replicate (uint.nat n - uint.nat i) (W64 0))
     ) with "[] [Hs $i]").
  { word. }
  - iIntros (i) "!>".
    clear Φ.
    iIntros (Φ) "HI HΦ". iDestruct "HI" as "(Hs & i & %)".
    wp_pures.
    wp_load. wp_load.
    wp_apply (wp_SliceSet with "[$Hs]").
    {
      iPureIntro.
      apply lookup_lt_is_Some.
      len.
    }
    iIntros "Hs".
    wp_pures.
    iModIntro.
    iApply "HΦ". iFrame "i".
    iExactEq "Hs".
    f_equal.
    replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
    replace (uint.Z (word.add i (W64 1))) with (uint.Z i + 1) by word.
    rewrite insert_app_r_alt; [ | len ].
    autorewrite with len.
    replace (uint.nat i - uint.nat i)%nat with 0%nat by word.
    replace (uint.nat n - uint.nat i)%nat with
      (S (uint.nat n - uint.nat i - 1)%nat) by word.
    rewrite replicate_S /=.
    rewrite cons_middle.
    rewrite app_assoc.
    f_equal.
    + rewrite seqZ_plus_1; [ | word ].
      rewrite Z.add_0_l.
      rewrite fmap_app /=.
      repeat f_equal.
      word.
    + f_equal; word.
  - iApply own_slice_to_small in "Hs".
    iExactEq "Hs".
    f_equal.
    rewrite seqZ_nil /=; [ | word ].
    f_equal. word.
  - iIntros "[Hs i]".
    replace (uint.nat n - uint.nat n)%nat with 0%nat by word.
    rewrite replicate_0 app_nil_r.
    wp_pures.
    wp_apply (wp_Shuffle with "Hs").
    iIntros (xs) "[%Hperm Hs]".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame.
    auto.
Qed.

End goose_lang.
