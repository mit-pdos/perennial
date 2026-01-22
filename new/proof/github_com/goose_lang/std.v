From New.proof Require Import proof_prelude.
From New.proof Require Import math time.
From New.generatedproof.github_com.goose_lang Require Import std.
From New.proof Require Import github_com.goose_lang.primitive std.std_core sync.
From iris_named_props Require Import custom_syntax.

Set Default Proof Using "Type".

Class stdG Σ := {
    #[local] std_syncG :: syncG Σ;
  }.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : std.Assumptions}.
Local Set Default Proof Using "All".
Context `{!stdG Σ}.

#[global] Instance : IsPkgInit (iProp Σ) std := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) std := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop std get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    std.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init std }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  wp_apply (std_core.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (primitive.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (time.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (sync.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (math.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

Lemma wp_Assert (cond : bool) :
  {{{ is_pkg_init std ∗ ⌜cond = true⌝ }}}
    @! std.Assert #cond
  {{{ RET #(); True }}}.
Proof.
  wp_start as "%". subst.
  wp_auto.
  wp_end.
Qed.

Lemma wp_BytesEqual s1 s2 (xs1 xs2: list w8) dq1 dq2 :
  {{{ is_pkg_init std ∗ s1 ↦*{dq1} xs1 ∗ s2 ↦*{dq2} xs2 }}}
    @! std.BytesEqual #s1 #s2
  {{{ RET #(bool_decide (xs1 = xs2)); s1 ↦*{dq1} xs1 ∗ s2 ↦*{dq2} xs2 }}}.
Proof.
  wp_start as "[Hs1 Hs2]".
  wp_auto.
  iDestruct (own_slice_len with "Hs1") as "%".
  iDestruct (own_slice_len with "Hs2") as "%".
  wp_if_destruct.
  {
    assert (length xs1 = length xs2) by word.
    iAssert (∃ (i: w64),
                "i" ∷ i_ptr ↦ i ∗
                "%Hbound" ∷ ⌜0 ≤ uint.Z i ≤ Z.of_nat (length xs1)⌝ ∗
                "%Hi" ∷ ⌜∀ (n: nat), (n < uint.nat i)%nat → xs1 !! n = xs2 !! n⌝
            )%I with "[$i]" as "IH".
    {
      iPureIntro.
      split; [ word | intros; word ].
    }
    wp_for "IH".
    wp_if_destruct.
    - list_elem xs1 (sint.Z i) as x1_i.
      rewrite -> decide_True; last word. wp_auto.
      wp_apply (wp_load_slice_index with "[$Hs1]") as "Hs1"; [ word | eauto | ].
      rewrite -> decide_True; last word. wp_auto.
      list_elem xs2 (sint.Z i) as x2_i.
      wp_apply (wp_load_slice_index with "[$Hs2]") as "Hs2"; [ word | eauto | ].
      destruct (bool_decide_reflect (x1_i = x2_i)); subst; wp_auto.
      + wp_for_post.
        iFrame.
        iPureIntro.
        split; [ word | ].
        intros.
        destruct (decide (n < uint.nat i)); eauto with lia.
        assert (n = sint.nat i) by word; subst.
        congruence.
      + wp_for_post.
        rewrite -> bool_decide_eq_false_2 by congruence.
        wp_end.
    - rewrite bool_decide_eq_true_2.
      { wp_end. }
      eapply list_eq_same_length; [ eauto | eauto | ].
      intros ???? Hget1 Hget2.
      rewrite -> Hi in Hget1 by word.
      congruence.
  }
  rewrite bool_decide_eq_false_2.
  { wp_end. }
  intros ?%(f_equal length).
  word.
Qed.

Lemma wp_BytesClone (b:slice.t) (xs:list u8) (dq:dfrac) :
  {{{ is_pkg_init std ∗ b ↦*{dq} xs }}}
    @! std.BytesClone #b
  {{{ b', RET #b'; b' ↦* xs ∗ own_slice_cap w8 b' (DfracOwn 1) }}}.
Proof.
  wp_start as "Hb". wp_auto.
  wp_if_destruct.
  - wp_end.
    + iSplitL.
      * iDestruct (own_slice_len with "Hb") as "[%Hb_len %]".
        apply nil_length_inv in Hb_len. subst.
        iDestruct (own_slice_nil (DfracOwn 1)) as "Hnil".
        iApply "Hnil".
      * iApply own_slice_cap_nil.
  - wp_apply (wp_slice_append with "[$Hb]").
    + rewrite go.array_index_ref_0. iSplitL.
      * iApply own_slice_empty; done.
      * iApply own_slice_cap_empty; done.
    + rewrite app_nil_l.
      iIntros (?) "(Hsl & Hcap & Hb)".
      wp_end.
Qed.

Lemma wp_SumNoOverflow (x y : u64) :
  {{{ is_pkg_init std }}}
    @! std.SumNoOverflow #x #y
  {{{ RET #(bool_decide (uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z)); True }}}.
Proof.
  wp_start; wp_auto.
  wp_apply wp_SumNoOverflow.
  wp_end.
Qed.

Lemma wp_SumAssumeNoOverflow (x y : u64) :
  {{{ is_pkg_init std }}}
    @! std.SumAssumeNoOverflow #x #y
  {{{ RET #(word.add x y); ⌜uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z⌝ }}}.
Proof.
  wp_start; wp_auto.
  wp_apply wp_SumAssumeNoOverflow.
  iIntros "%". wp_end.
Qed.

Lemma wp_SignedSumAssumeNoOverflow (x y : u64) :
  {{{ is_pkg_init std }}}
    @! std.SignedSumAssumeNoOverflow #x #y
  {{{ RET #(word.add x y); ⌜sint.Z (word.add x y) = (sint.Z x + sint.Z y)%Z⌝ }}}.
Proof.
  wp_start as "_"; wp_auto.
  unfold math.MaxInt, math.MinInt.
  (repeat wp_if_destruct); try wp_apply wp_Assume as "%"; wp_end.
Qed.

Definition is_JoinHandle (l: loc) (P: iProp Σ): iProp _ :=
  ∃ (mu_l cond_l: loc),
  "#mu" ∷ l.[std.JoinHandle.t, "mu"] ↦□ mu_l ∗
  "#cond" ∷ l.[std.JoinHandle.t, "cond"] ↦□ cond_l ∗
  "#Hcond" ∷ is_Cond cond_l (interface.mk (go.PointerType sync.Mutex) #mu_l) ∗
  "#Hlock" ∷ is_Mutex mu_l
     (∃ (done_b: bool),
         "done_b" ∷ l.[std.JoinHandle.t, "done"] ↦ done_b ∗
         "HP" ∷ if done_b then P else True)
.

Lemma wp_newJoinHandle (P: iProp Σ) :
  {{{ is_pkg_init std }}}
    @! std.newJoinHandle #()
  {{{ (l: loc), RET #l; is_JoinHandle l P }}}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_alloc mu as "Hmu".
  wp_auto.
  wp_apply (wp_NewCond with "[#]") as "%cond #His_cond".
  wp_alloc jh_l as "jh". iStructNamedSuffix "jh" "_j".
  iPersist "mu_j cond_j". simpl.
  iMod (init_Mutex (∃ (done_b: bool),
         "done_b" ∷ jh_l.[std.JoinHandle.t, "done"] ↦ done_b ∗
         "HP" ∷ if done_b then P else True)
         with "Hmu [$]") as "Hlock".
  wp_auto.
  wp_end.
  rewrite /is_JoinHandle.
  iFrame "His_cond #". iFrame.
Qed.

Lemma wp_JoinHandle__finish l (P: iProp Σ) :
  {{{ is_pkg_init std ∗ is_JoinHandle l P ∗ P }}}
    l @! (go.PointerType std.JoinHandle) @! "finish" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[Hhandle P]".
  iNamed "Hhandle".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[locked Hinv]".
  iNamed "Hinv".
  wp_auto.
  wp_apply (wp_Cond__Signal with "[$Hcond]").
  wp_apply (wp_Mutex__Unlock with "[$Hlock $locked done_b P]").
  { iFrame "done_b P". }
  wp_end.
Qed.

Lemma wp_Spawn (P: iProp Σ) (f : func.t) :
  {{{ is_pkg_init std ∗
        (∀ Φ, ▷(P -∗ Φ #()) -∗ WP #f #() {{ Φ }}) }}}
  @! std.Spawn #f
  {{{ (l: loc), RET #l; is_JoinHandle l P }}}.
Proof.
  wp_start as "Hwp".
  wp_auto.
  wp_apply (wp_newJoinHandle P) as "%l #Hhandle".
  iPersist "f h".
  wp_apply (wp_fork with "[Hwp]").
  - wp_auto.
    wp_apply "Hwp".
    iIntros "HP".
    wp_auto.
    wp_apply (wp_JoinHandle__finish with "[$Hhandle $HP]").
    done.
  - wp_end.
Qed.

Lemma wp_JoinHandle__Join l P :
  {{{ is_pkg_init std ∗ is_JoinHandle l P }}}
    l @! (go.PointerType std.JoinHandle) @! "Join" #()
  {{{ RET #(); P }}}.
Proof.
  wp_start as "Hjh". iNamed "Hjh".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[Hlocked @]".

  iAssert (∃ (done_b: bool),
           "locked" ∷ own_Mutex mu_l ∗
           "done" ∷ l.[std.JoinHandle.t, "done"]↦ done_b ∗
           "HP" ∷ (if done_b then P else True))%I
          with "[$Hlocked $done_b $HP]" as "HI".
  wp_for "HI".
  destruct done_b0; wp_auto.
  - wp_for_post.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $locked $done]").
    wp_end.
  - wp_apply (wp_Cond__Wait with "[$Hcond locked done HP]") as "H".
    { iSplit.
      - iApply (Mutex_is_Locker with "[] Hlock"). iPkgInit.
      - iFrame. }
    iDestruct "H" as "[Hlocked Hlinv]". iNamed "Hlinv".
    wp_for_post. iFrame.
Qed.

End wps.
