From New.proof Require Export proof_prelude.
From New.golang.theory Require Import chan.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import chan_au_base simple.
From New.proof Require Import sync strings time tok_set.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!syncG Σ}.
Context `{!chanGhostStateG Σ slice.t}.
Context `{!waitgroup_joinG Σ}.

#[global] Instance : IsPkgInit chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf chan_spec_raw_examples := build_get_is_pkg_init_wf.

Record SearchReplace_names :=
  {
    wg: WaitGroup_names;
    wg_added : gname;
  }.

Implicit Types γ : SearchReplace_names.

Definition search_replace (x y: w64) : list w64 → list w64 :=
  fmap (λ a, if decide (a = x) then y else a).

#[local] Hint Unfold search_replace : len.

Definition chanP wg (x y: w64) (s: slice.t) : iProp Σ :=
  ∃ (xs: list w64),
    "Hxs" ∷ s ↦* xs ∗
    "Hwg_done" ∷ join.own_Done wg (s ↦* (search_replace x y xs)).

Definition waitgroupN := nroot .@ "waitgroup".

Lemma wp_worker (γs: simple_names) (ch: loc) (wg: loc) (x y: w64) :
  {{{ is_pkg_init chan_spec_raw_examples ∗
      "#Hchan" ∷ is_simple γs ch 4 (chanP wg x y) }}}
    @! chan_spec_raw_examples.worker #ch #wg #x #y
  {{{ RET #(); True }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  wp_apply (wp_simple_receive with "[$Hchan]").
  iIntros (s) "Hrcv".
  wp_auto. iPersist "y x".
  iAssert (∃ s,
      "s" ∷ s_ptr ↦ s ∗
      "Hrcv" ∷ chanP wg x y s
    )%I with "[s Hrcv]" as "HH".
  { iFrame. } clear s.
  wp_for. iNamed "HH". iNamed "Hrcv".
  iDestruct (own_slice_len with "[$]") as %Hlen.
  iAssert (
      ∃ (i : w64),
        "i" ∷ i_ptr ↦ i ∗
        "Hxs" ∷ s ↦* ((search_replace x y (take (sint.nat i) xs)) ++ (drop (sint.nat i) xs)) ∗
        "%Hi_bound" ∷ ⌜ uint.nat i ≤ length xs ⌝
    )%I with "[i Hxs]" as "HH".
  { iFrame. rewrite take_0 drop_0 /=. iFrame. word. }
  wp_for. iNamed "HH".
  wp_auto.
  case_bool_decide as Hi.
  (* FIXME: wp_if_destruct doesn't keep the fact around? *)
  - cleanup_bool_decide. wp_pures.
    wp_auto. wp_apply (join.wp_WaitGroup__Done with "[$Hwg_done Hxs]").
    { rewrite take_ge; last word. rewrite drop_ge; last word.
      rewrite app_nil_r. iFrame. }
    wp_for_post.
    wp_apply (wp_simple_receive with "[$Hchan]").
    iIntros (s') "Hrcv".
    wp_auto. iFrame.
  - rewrite decide_True //. wp_auto.
    wp_pure; first word.
    assert (sint.nat i < length xs)%nat as Hlt by word.
    apply list_lookup_lt in Hlt as [x' Hlookup].
    erewrite drop_S; last done.
    iDestruct (own_slice_elem_acc i with "Hxs") as "[Helem Hxs]".
    { word. }
    { rewrite lookup_app_r; last len.
      replace (_ - _)%nat with 0%nat by len. done. }
    wp_auto.
    wp_apply (wp_wand  _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗
                                   slice.elem_ref_f s uint64T i ↦ (if decide (x' = x) then y else x') ∗
                                   _
                )%I
               with "[Helem s i]").
    { case_bool_decide; wp_auto.
      - wp_pure; first word. wp_auto. rewrite decide_True //.
        iFrame. iSplitR; first done. iNamedAccu.
      - rewrite decide_False //. iFrame. done. }
    iIntros "% (-> & Helem & HH)". iNamed "HH". wp_for_post.
    iFrame. iSpecialize ("Hxs" with "[$]"). iSplitL "Hxs".
    { iApply to_named. iExactEq "Hxs". f_equal.
      rewrite insert_app_r_alt; last len.
      replace (sint.nat (word.add _ _))%nat with (sint.nat i + 1)%nat by word.
      rewrite take_more; last len. unfold search_replace. rewrite fmap_app.
      rewrite -app_assoc. f_equal.
      ereplace (<[_ := ?[a]]>) with (<[ O := ?a ]>).
      2:{ f_equal. len. }
      simpl. erewrite (drop_S xs _ (sint.nat i)); last done. f_equal.
      f_equal. len.
    }
    word.
Qed.

Lemma wp_SearchReplace (s: slice.t) (xs: list w64) (x y: w64) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ s ↦* xs ∗
      ⌜ length xs ≤ 2^63 - 1000 ⌝ ∗
      ⌜ length xs ≤ (2^31 - 1)*1000 ⌝
  }}}
    @! chan_spec_raw_examples.SearchReplace #s #x #y
  {{{ RET #(); s ↦* (search_replace x y xs) }}}.
Proof using chanGhostStateG0 waitgroup_joinG0 syncG0.
  (* The first overflow:
     implementation adds 1000 at a time, potentially surpassing the slice length
     before clamping. If it goes negative, then the clamping doesn't work. This
     inequality is technically implied by the second; keeping for
     documentation (and e.g. workRange can change). *)
  (* The second overflow:
     if `len(xs)` is bigger than `(2^31-1)*workRange`, then Add() will be called
     *more* than 2^31-1 times, potentially overflow the internal waitgroup
      counter. *)
  wp_start as "(Hs & %Hoverflow1 & %Hoverflow2)".
  wp_auto.
  iDestruct (own_slice_len with "Hs") as %Hlen.
  iDestruct (own_slice_wf with "Hs") as %Hcap. (* FIXME: rename to own_slice_cap? *)
  wp_if_destruct.
  {
    assert (length xs = 0%nat) by word.
    destruct xs; simpl in *; [ | congruence ].
    iApply "HΦ".
    iFrame.
  }
  wp_apply chan.wp_make.
  { done. }
  iIntros (ch γch_names) "[#His_chan Hoc]". simpl. wp_auto.
  iMod (init_WaitGroup with "wg") as (?) "H".
  iMod (join.init with "H") as "Hwg".
  iMod (start_simple_buffered _ _ _ (chanP wg_ptr x y) with "[$His_chan] [$Hoc]") as (γch) "#Hchan".
  iAssert (∃ (i : w64), "i" ∷ i_ptr ↦ i)%I with "[$i]" as "HH".
  wp_for. iNamed "HH". wp_auto.
  wp_if_destruct.
  2:{
    wp_apply wp_fork.
      { wp_apply wp_worker; last done. iFrame "#". }
      wp_for_post. iFrame.
  }

  set (workRange:=1000).
  iAssert (
      ∃ (offset : w64) nadded,
        "offset" ∷ offset_ptr ↦ offset ∗
        "Hs" ∷ (slice.slice_f s uint64T offset s.(slice.len_f)) ↦* drop (uint.nat offset) xs ∗
        "Hwg" ∷ join.own_Adder wg_ptr nadded
          ((slice.slice_f s uint64T 0 offset) ↦* take (uint.nat offset) (search_replace x y xs)) ∗
        "%Hoffset" ∷ ⌜ 0 ≤ sint.Z offset ≤ length xs ⌝ ∗
        "%Hnadded" ∷ ⌜ 0 ≤ workRange * sint.Z nadded ≤ sint.Z offset ∨ sint.nat offset = length xs⌝
    )%I with "[offset Hs Hwg]" as "HH".
  { iFrame. iExists _. rewrite drop_0 take_0.
    erewrite <- slice_slice_trivial. iFrame.
    iDestruct (join.own_Adder_wand with "[] Hwg") as "$".
    { iIntros "_". iApply own_slice_empty; simpl; word. }
    word. }
  iPersist "s".
  wp_for. iNamed "HH". wp_auto. case_bool_decide.
  { rewrite decide_False // decide_True //. wp_auto.
    wp_apply (join.wp_WaitGroup__Wait with "[$Hwg]").
    iClear "Hs". iIntros "[Hs Hwg]". subst.
    rewrite take_ge; last len. wp_auto. iApply "HΦ".
    rewrite <- slice_slice_trivial. iFrame. }
  rewrite decide_True //. wp_auto.
  set (nextOffset:=((sint.Z offset + workRange) `min` Z.of_nat (length xs))).
  wp_bind (if: _ then _ else _)%E.
  wp_apply (wp_wand  _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗
                                 "nextOffset" ∷ nextOffset_ptr ↦ (W64 nextOffset))%I with "[nextOffset]").
  { wp_if_destruct.
    - iSplitR; first done. iApply to_named. iExactEq "nextOffset".
      f_equal. unfold nextOffset. word.
    - iSplitR; first done. iApply to_named. iExactEq "nextOffset".
      f_equal. unfold nextOffset. word. }
  iIntros "% [-> H]". iNamed "H". wp_auto.
  wp_pure.
  { unfold nextOffset. word. }
  wp_auto. wp_apply (join.wp_WaitGroup__Add with "[$Hwg]").
  { word. }
  iIntros "[Hwg Hdone]".
  wp_auto.
  iDestruct (own_slice_split nextOffset with "Hs") as "[Hsection Hs]".
  { subst nextOffset. word. }
  rewrite drop_drop.
  wp_apply (wp_simple_send with "[Hdone Hsection]").
  { iFrame "#". iFrame. }
  wp_for_post.
  iFrame. iExists _.
  iSplitL "Hs".
  { iApply to_named. iExactEq "Hs". f_equal. f_equal. subst nextOffset. word. }
  iDestruct (join.own_Adder_wand with "[] Hwg") as "$".
  {
    iIntros "[Hpre Hsuf]".
    iDestruct (own_slice_combine offset with "Hpre Hsuf") as "Hs".
    { subst nextOffset. len. }
    iExactEq "Hs". f_equal.
    unfold search_replace. rewrite -!fmap_take. rewrite -fmap_app. f_equal.
    rewrite take_take_drop. f_equal.
    subst nextOffset. len.
  }
  subst nextOffset. word.
Qed.

Print Assumptions wp_SearchReplace.

End proof.
