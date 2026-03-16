From New.proof.github_com.goose_lang.goose.testdata.examples Require Import channel_examples_init.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import idiom.base spsc.
From New.code Require Import github_com.goose_lang.goose.testdata.examples.channel.
From New.golang Require Import theory.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : chan_spec_raw_examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Section fibonacci_examples.

Fixpoint fib (n: nat) : w64 :=
  match n with
  | 0%nat => W64 0
  | 1%nat => W64 1
  | S (S n' as n'') => word.add (fib n'') (fib n')
  end.

Definition fib_list (n: nat) : list w64 :=
  map fib (seq 0 n).

Lemma fib_list_succ (n: nat) :
  fib_list (S n) = fib_list n ++ [fib n].
Proof.
  unfold fib_list.
  rewrite seq_S.
  rewrite map_app. done.
Qed.

Lemma fib_list_length (n: nat) :
  length (fib_list n) = n.
Proof.
  unfold fib_list. rewrite map_length. apply seq_length.
Qed.

Lemma fib_succ (k:nat) :
  fib (S k) =
    match k with 0%nat => W64 1 | S k' => word.add (fib (S k')) (fib k') end.
Proof. destruct k; simpl; reflexivity. Qed.

Open Scope Z_scope.

Lemma wp_fibonacci (n: w64) (c_ptr: loc) γ:
  0 < sint.Z n < 2^63 →
  {{{ is_pkg_init chan_spec_raw_examples ∗
      is_spsc γ c_ptr (λ i v, ⌜v = fib (Z.to_nat i)⌝)
                  (λ sent, ⌜sent = fib_list  (sint.nat n)⌝) ∗
      spsc_producer γ ([] : list w64)
  }}}
    @! chan_spec_raw_examples.fibonacci #n #c_ptr
  {{{ RET #(); True }}}.
Proof.
  intros Hn. wp_start.
  iDestruct "Hpre" as "(#Hspsc & Hprod)".
  rename c_ptr into c_ptr0.
  wp_alloc_auto. wp_auto.
  iAssert (∃ (i: nat) (sent: list w64),
              "Hprod" ∷ spsc_producer γ sent ∗
              "x"     ∷ x_ptr ↦ fib i ∗
              "y"     ∷ y_ptr ↦ fib (S i) ∗
              "i"     ∷ i_ptr ↦ W64 i ∗
              "c"     ∷ c_ptr ↦ c_ptr0 ∗
              "%Hil"  ∷ ⌜i = length sent⌝ ∗
              "%Hsl"  ∷ ⌜sent = fib_list i⌝ ∗
              "%Hi"   ∷ ⌜0 ≤ i ≤ sint.Z n⌝)%I
    with "[x y i c Hprod]" as "IH".
  {
    iFrame. iExists 0%nat.
    iFrame. iPureIntro. unfold fib_list.
    simpl. repeat (split;first done). lia.
  }

  wp_for "IH".
  wp_if_destruct.
  {
    wp_apply (wp_spsc_send with "[Hspsc Hprod]").
    { iFrame "#".  iFrame.
      replace (Z.to_nat (length sent)) with (length sent) by lia.
      word.
    }
    iIntros "Hprod". wp_auto.
    wp_for_post.
    iFrame. iExists ((length sent) + 1)%nat.
    replace (length sent + 1)%nat with (S (length sent)) by lia.
    destruct (length sent) eqn: H.
    {
      iFrame.  iPureIntro. rewrite app_length. rewrite H. simpl. unfold fib_list.
      split;first done.
      rewrite Hsl.
      split;first done. lia.
    }
    iFrame.

    replace   (w64_word_instance.(word.add)
                                   (fib (S n0))
                                   (w64_word_instance.(word.add)
                                                        (fib (S n0))
                                                        (fib n0)))
      with  (fib (S (S (S n0)))).
    {
      iFrame.
      replace ( w64_word_instance.(word.add) (W64 (S n0)) (W64 1)) with (W64 (S (S n0))) by word.
      {
        iFrame. iPureIntro.
        split.
        { rewrite length_app.  rewrite singleton_length.  rewrite H. lia. }
        split.
        {
          subst sent. rewrite <- fib_list_succ;done.
        }
        word.
      }
    }
    { rewrite !fib_succ;word. }
  }
  {
    wp_apply (wp_spsc_close with "[$Hspsc $Hprod]").
    { iFrame "#".   iPureIntro. rewrite Hsl.
      assert ((length sent) = sint.nat n).
      {
        assert (length sent < 2^64) by lia;word.
      }
      destruct (length sent);first word.
      set_solver.
    }
    iApply "HΦ". done.
  }
Qed.

Lemma wp_fib_consumer:
  {{{ is_pkg_init chan_spec_raw_examples
  }}}
   @! chan_spec_raw_examples.fib_consumer #()
  {{{ sl, RET #(sl);
      sl ↦* (fib_list 10)


  }}}.
Proof.
  wp_start. wp_auto. wp_apply chan.wp_make2; first done.
  iIntros (c γ) "(#Hchan & %Hcap_eq & Hown)".
  wp_auto.
  iMod (start_spsc c (λ i v, ⌜v = fib (Z.to_nat i)⌝%I)
          (λ sent, ⌜sent = fib_list 10 ⌝%I)  γ
         with "[$Hchan] [$Hown]") as (γspsc) "(#Hspsc & Hprod & Hcons)".
  wp_apply (chan.wp_cap with "[$Hchan]").
  wp_apply (wp_fork with "[Hprod]").
  {
    wp_apply ((wp_fibonacci) with "[$Hprod]");first word.
    {
      replace (sint.nat (γ.(chan_cap))) with 10%nat by word.
      iFrame "#".
    }
    done.
  }
  wp_apply wp_slice_literal as "% _".
  { iIntros. wp_auto. iFrame. }
  iAssert (∃ (i: nat) (i_v: w64) sl,
              "i" ∷ i_ptr ↦ i_v ∗
              "Hcons"  ∷ spsc_consumer γspsc (fib_list i) ∗
              "Hsl"  ∷ sl ↦* (fib_list i) ∗
              "results"  ∷ results_ptr ↦ sl ∗
              "oslc"  ∷ theory.slice.own_slice_cap w64 sl (DfracOwn 1)
          )%I
    with "[ i Hcons results]" as "IH".
  {
    iExists 0%nat. iFrame.
    unfold fib_list.
    iDestruct own_slice_empty as "$"; [done..|].
    iDestruct own_slice_cap_empty as "$"; done.
  }

  wp_for "IH". wp_apply (wp_spsc_receive with "[$Hcons $Hspsc]").
   iIntros (v ok). destruct ok.
   {
    iIntros "[%Hfib Hcons]". wp_auto.
    iDestruct (slice.own_slice_len with "Hsl") as "[%Hl %Hcap]".
    iDestruct (slice.own_slice_len with "Hsl") as "[%Hlen_slice %Hslgtz]".
    wp_apply wp_slice_literal. { iIntros. wp_auto. iFrame. }iIntros (sl0) "[Hsl0 _]".
    iDestruct (slice.own_slice_len with "Hsl0") as "[%Hl0 %Hcap0]".
    iDestruct (slice.own_slice_len with "Hsl0") as "[%Hlen_slice0 %Hslgtz0]".
    wp_auto. wp_apply (wp_slice_append with "[$Hsl $Hsl0 $oslc ]").
    iIntros (sl') "Hsl'". wp_auto. wp_for_post. iFrame.
    iExists (S i). iDestruct "Hsl'" as "(Hsl & Hcap3 & Hsl0)".
    rewrite Hfib.
    rewrite fib_list_length. rewrite Nat2Z.id. do 2 rewrite <- fib_list_succ.
    iFrame.
   }
  iIntros "%Hfl". wp_auto. wp_for_post. iApply "HΦ".
  destruct Hfl as [H1 H2]; first rewrite H1. done.
Qed.

End fibonacci_examples.
End proof.
