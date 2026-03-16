From New.proof.github_com.goose_lang.goose.testdata.examples Require Import channel_examples_init.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import idiom.base bag future.
From New.code Require Import github_com.goose_lang.goose.testdata.examples.channel.
From iris.base_logic Require Import ghost_map.
From New.golang Require Import theory.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : chan_spec_raw_examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Open Scope Z_scope.

Section google_example.

Context `{!chan_idiomG Σ go_string}.
Context `{!ghost_map.ghost_mapG Σ gname (go_string → iProp Σ)}.
#[local] Existing Instance H.
Context `{!inG Σ unitR}.

Lemma wp_Web (q : go_string) :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.Web #q
  {{{ RET #(q ++ ".html"%go); True }}}.
Proof. wp_start. wp_auto. iApply "HΦ". done. Qed.

Lemma wp_Image (q : go_string) :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.Image #q
  {{{ RET #(q ++ ".png"%go); True }}}.
Proof. wp_start. wp_auto. iApply "HΦ". done. Qed.

Lemma wp_Video (q : go_string) :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.Video #q
  {{{ RET #(q ++ ".mp4"%go); True }}}.
Proof. wp_start. wp_auto. iApply "HΦ". done. Qed.

Definition google_expected (q: go_string) : list go_string :=
  [ q ++ ".html"%go; q ++ ".png"%go; q ++ ".mp4"%go ].

Inductive kind := KWeb | KImg | KVid.

Definition kind_eq_dec : ∀ x y : kind, {x = y} + {x ≠ y}.
Proof. decide equality. Defined.

Definition value_of (q:go_string) (k:kind) : go_string :=
  match k with
  | KWeb => q ++ ".html"%go
  | KImg => q ++ ".png"%go
  | KVid => q ++ ".mp4"%go
  end.

Definition pure_contract_of (q:go_string) (k:kind) : go_string → Prop :=
  λ v, v = value_of q k.

Definition contract_of (q:go_string) (k:kind) : go_string → iProp Σ :=
  λ v, ⌜pure_contract_of q k v⌝%I.

Lemma pure_contract_of_inj (q:go_string) (k1 k2:kind) :
  pure_contract_of q k1 = pure_contract_of q k2 → k1 = k2.
Proof.
  intro Heq. destruct k1, k2; try done.
  all: exfalso.
  all:  set v := value_of q KWeb.
    {
      have Heqv : pure_contract_of q KWeb v = pure_contract_of q KImg v by (exact (f_equal (fun f => f v) Heq)).
      rewrite /pure_contract_of in Heqv.
      subst v. unfold value_of in Heqv. symmetry in Heqv.
      assert (q ++ ".html"%go ≠ q ++ ".png"%go) by set_solver.
      assert ((q ++ ".html"%go = q ++ ".html"%go)) by done.
      assert (q ++ ".html"%go = q ++ ".png"%go).
      { rewrite Heqv. reflexivity. }
      congruence.
    }
    {
    have Heqv : pure_contract_of q KWeb v = pure_contract_of q KVid v by (exact (f_equal (fun f => f v) Heq)). rewrite /pure_contract_of in Heqv. subst v.
    unfold value_of in Heqv. symmetry in Heqv.
    assert (q ++ ".html"%go ≠ q ++ ".mp4"%go) by set_solver.
    assert ((q ++ ".html"%go = q ++ ".html"%go)) by done.
    assert (q ++ ".html"%go = q ++ ".mp4"%go).
    { rewrite Heqv. reflexivity. }
    congruence.
    }
    {
    have Heqv : pure_contract_of q KImg v = pure_contract_of q KWeb v by (exact (f_equal (fun f => f v) Heq)).
    rewrite /pure_contract_of in Heqv. subst v. unfold value_of in Heqv.
    symmetry in Heqv.
    assert (q ++ ".html"%go ≠ q ++ ".png"%go) by set_solver.
    assert ((q ++ ".html"%go = q ++ ".html"%go)) by done.
    assert (q ++ ".html"%go = q ++ ".png"%go).
    {
      rewrite Heqv in H1. done.
    }
    congruence.
  }
  {
    unfold pure_contract_of in Heq.
    assert (value_of q KImg = value_of q KVid) as Hbad.
    { apply (f_equal (fun f => f (value_of q KImg))) in Heq.
      unfold value_of in Heq. simpl in Heq.
      symmetry in Heq.
      assert (q ++ ".png"%go = q ++ ".mp4"%go).
      { rewrite Heq. reflexivity. }
      assumption.
    }
    unfold value_of in Hbad. simpl in Hbad.
    assert (q ++ ".png"%go ≠ q ++ ".mp4"%go) by set_solver.
    congruence.
  }
  {
  unfold pure_contract_of in Heq.
  assert (value_of q KVid = value_of q KWeb) as Hbad.
    { apply (f_equal (fun f => f (value_of q KVid))) in Heq.
      unfold value_of in Heq. simpl in Heq.
      symmetry in Heq.
      assert (q ++ ".mp4"%go = q ++ ".html"%go).
      { rewrite Heq. reflexivity. }
      assumption.
    }
  unfold value_of in Hbad. simpl in Hbad.
  assert (q ++ ".mp4"%go ≠ q ++ ".html"%go) by set_solver.
  congruence.
  }
  {
  unfold pure_contract_of in Heq.
  assert (value_of q KVid = value_of q KImg) as Hbad.
  { apply (f_equal (fun f => f (value_of q KVid))) in Heq.
    unfold value_of in Heq. simpl in Heq.
    symmetry in Heq.
    assert (q ++ ".mp4"%go = q ++ ".png"%go).
    { rewrite Heq. reflexivity. }
    assumption.
  }
  unfold value_of in Hbad. simpl in Hbad.
  assert (q ++ ".mp4"%go ≠ q ++ ".png"%go) by set_solver.
  congruence.
  }
Qed.

Definition pendingk : list kind := [KWeb; KImg; KVid].

Lemma pendingk_nodup : NoDup pendingk.
Proof. unfold pendingk. repeat constructor; set_solver. Qed.

Lemma contract_of_sound (q:go_string) (k:kind) (v:go_string) :
  contract_of q k v ⊢ ⌜v = value_of q k⌝.
Proof. iIntros "%Hv". iPureIntro. exact Hv. Qed.

Lemma mem_map_contract_of (q:go_string) (remk:list kind) (P:go_string→iProp Σ) :
  P ∈ map (contract_of q) remk →
  ∃ k, k ∈ remk ∧ P = contract_of q k.
Proof.
  intro HP.
  rewrite -(list_fmap_map (contract_of q) remk) in HP.
  apply (proj1 (list_elem_of_fmap _ _ _)) in HP.
  destruct HP as (k & -> & Hk). eauto.
Qed.

Lemma delete_middle {A} (l1 : list A) (x : A) (l2 : list A) :
  delete (length l1) (l1 ++ x :: l2) = l1 ++ l2.
Proof.
  induction l1 as [|a l1 IH]; simpl; [done|].
  by rewrite IH.
Qed.

Lemma wp_Google (q : go_string) :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.Google #q
  {{{ (sl : slice.t), RET #sl;
      ∃ xs, sl ↦* xs ∗ ⌜xs ≡ₚ google_expected q⌝ }}}.
Proof using All.
  wp_start. wp_auto.
  wp_apply (chan.wp_make2 (W64 3)); first done.
  iIntros (c γch) "(#Hchan & %Hcap3 & Hown)".
  simpl in *.
  iMod (start_future
          (V:=go_string)
          (t:=go.string)
          (ghost_mapG0:=H)
          c γch (chanstate.Buffered [])
        with "[$Hchan] [$Hown]") as (γmf) "(#Hmf & HAwait)".
  { right. done. }
  wp_auto.
  iMod (future_alloc_promise (t:=go.string) γmf c (contract_of q KWeb) []
        with "[$Hmf] [$HAwait]") as "(Hprom_web & HAwait)".
  iMod (future_alloc_promise (t:=go.string) γmf c (contract_of q KImg) _
        with "[$Hmf] [$HAwait]") as "(Hprom_img & HAwait)".
  iMod (future_alloc_promise (t:=go.string) γmf c (contract_of q KVid) _
        with "[$Hmf] [$HAwait]") as "(Hprom_vid & HAwait)".
  iPersist "c query".
  wp_apply (wp_fork with "[Hprom_web]").
  {
    wp_auto. wp_apply (wp_Web q).
    wp_apply (wp_future_fulfill
                (V:=go_string)
                (t:=go.string)
                (ghost_mapG0:=H)
                γmf c (value_of q KWeb)
              with "[$Hmf $Hprom_web]");done.
  }

  wp_apply (wp_fork with "[Hprom_img]").
  {
    wp_auto.
    wp_apply (wp_Image q).
    wp_apply (wp_future_fulfill
                (V:=go_string)
                (t:=go.string)
                (ghost_mapG0:=H)
                γmf c (value_of q KImg)
              with "[$Hmf $Hprom_img]");done.
  }

  wp_apply (wp_fork with "[Hprom_vid]").
  {
    wp_auto.
    wp_apply (wp_Video q).
    wp_apply (wp_future_fulfill
                (V:=go_string)
                (t:=go.string)
                (ghost_mapG0:=H)
                γmf c (value_of q KVid)
              with "[$Hmf $Hprom_vid]");done.
  }

  wp_apply (wp_slice_make3 (V:=go_string) (t:=go.string));first word.
  iIntros (sl) "[Hsl [Hcap_sl %Hcap]]".
  wp_auto.

  iAssert (∃ (i : Z) (xs : list go_string)
                  (donek remk : list kind) (sl0 : slice.t),
      "i"            ∷ i_ptr ↦ W64 i ∗
      "results"      ∷ results_ptr ↦ sl0 ∗
      "Hsl"          ∷ sl0 ↦* xs ∗
      "Hcap"         ∷ own_slice_cap go_string sl0 (DfracOwn 1) ∗
      "HAwait"       ∷ Await (V:=go_string) γmf (map (contract_of q) remk) ∗
      "%Hlen"        ∷ ⌜Z.of_nat (length xs) = i⌝ ∗
      "%Hi"          ∷ ⌜i ≤ 3⌝ ∗
      "%Hrem"        ∷ ⌜length remk = Z.to_nat (3 - i)⌝ ∗
      "%Hnodup_rem"  ∷ ⌜NoDup remk⌝ ∗
      "%Hsplit"      ∷ ⌜pendingk ≡ₚ donek ++ remk⌝ ∗
      "%Hperm"       ∷ ⌜xs ≡ₚ map (value_of q) donek⌝
    )%I
    with "[i $results $Hsl $Hcap_sl HAwait]" as "IH".
  {
    iExists 0, ([] : list kind).
    iFrame.
    iExists ([KWeb; KImg; KVid]).
    iSplitL "HAwait".
    { iNamedAccu. }
    repeat (iSplit; [iPureIntro; try reflexivity; try lia;
                     auto using pendingk_nodup|]).
    iPureIntro. simpl. reflexivity.
  }
  wp_for "IH".
  wp_if_destruct.
  - wp_apply (wp_future_await
                (V:=go_string)
                (t:=go.string)
                (ghost_mapG0:=H)
                γmf c (map (contract_of q) remk)
              with "[$Hmf $HAwait]").
    iIntros (v P pre post) "(%HsplitP & HPv & HAwait')".
    have HPmem : P ∈ map (contract_of q) remk
      by (rewrite HsplitP; set_solver).
    destruct (mem_map_contract_of q remk P HPmem)
      as (k & Hkin & ->).
    iDestruct (contract_of_sound q k v with "HPv") as %->.
    wp_auto.
    wp_apply wp_slice_literal as "% Hsl1".
    { iIntros. wp_auto. iFrame. }
    wp_apply (wp_slice_append with "[$Hsl $Hcap $Hsl1]").
    iIntros (sl') "[Hsl' Hcap']".
    wp_auto. set j := length pre. set remk' := delete j remk.
    have Hj_lt_map : j < length (map (contract_of q) remk).
    {
      subst j. rewrite HsplitP. rewrite app_length /=.
      lia.
    }

    have Hj_lt : j < length remk by rewrite length_map in Hj_lt_map.

    have Hlook_map :
      (map (contract_of q) remk) !! j = Some (contract_of q k).
    {
      subst j.
      rewrite HsplitP.
      rewrite lookup_app_r; last lia.
      replace (length pre - length pre)%nat with 0%nat by lia.
      simpl. done.
    }

    apply (list_lookup_fmap_Some
             (contract_of q) remk j (contract_of q k))
      in Hlook_map as (k0 & Hk0 & Hk0eq).
    apply (f_equal (fun f => f (value_of q k0))) in Hk0.
    iAssert (⌜value_of q k0 = value_of q k⌝)%I as "%Hbad".
    {
      unfold contract_of, pure_contract_of in Hk0.
      iEval (rewrite Hk0). done.
    }

    have Heq_k0_k : k0 = k.
    {
      apply (pure_contract_of_inj q).
      unfold contract_of, pure_contract_of in Hk0.
      unfold contract_of, pure_contract_of.
      by rewrite Hbad.
    }

    have Hlook_remk : remk !! j = Some k
      by (replace k with k0 by done; done).

    have Hdecomp :
      take j remk ++ k :: drop (S j) remk = remk
      by exact (take_drop_middle remk j k Hlook_remk).

    have Hrem' : Z.of_nat (length remk') = (3 - S (length xs)).
    {
      rewrite /remk' length_delete; [by len | ].
      apply lookup_lt_is_Some_2; lia.
    }

    have Hmap_remk' :
      map (contract_of q) remk' = pre ++ post.
    {
      subst remk' j.
      rewrite -!list_fmap_map list_fmap_delete list_fmap_map.
      by rewrite HsplitP delete_middle.
    }

    set donek' := donek ++ [k].
    have Hsplit' :
      pendingk ≡ₚ donek' ++ remk'.
    {
      unfold donek', remk'. subst j.
      eapply Permutation_trans; [exact Hsplit|].
      rewrite (delete_take_drop remk) -Hdecomp.
      repeat rewrite -app_assoc.
      apply Permutation_app_head.
      simpl.
      rewrite Permutation_middle Hdecomp.
      by rewrite Hdecomp.
    }

    have Hperm' :
      (xs ++ [value_of q k]) ≡ₚ map (value_of q) donek'.
    {
      unfold donek'.
      rewrite map_app /=.
      etransitivity; [|reflexivity].
      rewrite Hperm.
      reflexivity.
    }

    have Hnodup_rem' : NoDup remk'.
    {
      apply (sublist_NoDup _ _ Hnodup_rem).
      apply sublist_delete.
    }

    wp_for_post.
    iFrame "HΦ".
    iExists (S (length xs)),
            (xs ++ [value_of q k]),
            donek', remk', sl'.
    iFrame "#%".
    iFrame.

    iSplitL "i".
    {
      replace (W64 (S (length xs)))
        with (w64_word_instance.(word.add)
                (W64 (length xs)) (W64 1))
        by word.
        done.
    }

    iDestruct "Hcap'" as "[Hcap Hsl]".
    iFrame.

    iSplitL "HAwait'".
    { rewrite Hmap_remk'. done. }

    iSplit; [ by len | ].
    iSplit; [ by len | ].
    len.
  - iApply "HΦ". iExists xs.
    iFrame "Hsl". iPureIntro.

    have Hlenxs : Z.of_nat (length xs) = 3.
    { len. }

    have Hremk_nil : remk = [].
    {
      apply length_zero_iff_nil.
      rewrite Hrem.
      len.
    }

    have Hdone : pendingk ≡ₚ donek.
    {
      subst remk.
      rewrite app_nil_r in Hsplit.
      done.
    }

    have Hmap :
      map (value_of q) pendingk ≡ₚ
      map (value_of q) donek :=
      Permutation_map (value_of q) Hdone.

    have Hexp :
      map (value_of q) pendingk = google_expected q by reflexivity.

    etransitivity; [exact Hperm|].
    eapply Permutation_trans.
    { exact (Permutation_sym Hmap). }
    rewrite Hexp.
    apply Permutation_refl.
    Unshelve.
    all: try (typeclasses eauto).
Qed.

End google_example.
End proof.
