From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import pb.

Section common_proof.

Context `{!heapGS Σ}.

Lemma wp_min sl (l:list u64):
  {{{
       is_slice_small sl uint64T 1%Qp l
  }}}
    min (slice_val sl)
  {{{
       (m:u64), RET #m; ⌜length l > 0 → m ∈ l⌝ ∗ ⌜∀ n, n ∈ l → int.Z m ≤ int.Z n⌝ ∗
       is_slice_small sl uint64T 1%Qp l
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_lam.
  wp_apply (wp_ref_to).
  { naive_solver. }
  iIntros (m_ptr) "Hm".
  wp_pures.
  wp_apply (wp_forSlice (λ j, ∃ (m:u64),
                            "Hm" ∷ m_ptr ↦[uint64T] #m ∗
                            "%H" ∷ ⌜int.Z j = 0 → ∀ (a:u64), int.Z m >= int.Z a⌝ ∗
                            "%HinL" ∷ ⌜int.nat j > 0 → m ∈ l⌝ ∗
                            "%Hmmin" ∷ ⌜∀ n, n ∈ take (int.nat j) l → int.Z m ≤ int.Z n⌝
                        )%I with "[] [$Hpre Hm]").
  {
    iIntros.
    clear Φ.
    iIntros (Φ) "!# [Hpre %Hi] HΦ".
    destruct Hi as [Hi Hilookup].
    iNamed "Hpre".
    wp_pures.
    wp_load.
    wp_pures.
    wp_if_destruct.
    { (* decrease m *)
      admit.
    }
    { (* no need to decrease m *)
      iApply "HΦ".
      iModIntro.
      iExists _; iFrame.
      iPureIntro.
      split.
      {
        intros Hi2 ?.
        exfalso.
        replace (int.Z (word.add i 1)) with (int.Z i + 1) in Hi2 by word.
        word. (* Hi and Hi2 contradictory *)
      }
      split.
      {
        intros _.
        admit.
      }
      {
        intros.
        admit.
      }
    }
  }
  {
    iExists _.
    iFrame "Hm".
    iPureIntro.
    split.
    {
      intros.
      word.
    }
    split.
    {
      intros.
      by exfalso.
    }
    {
      intros.
      exfalso.
      rewrite take_0 in H.
      set_solver.
    }
  }
  iIntros "[HH Hslice]".
  iNamed "HH".
  wp_pures.
  wp_load.
  iApply "HΦ".
  iModIntro.
  iSplitL ""; first admit. (* FIXME: strengthen precond *)
  iDestruct (is_slice_small_sz with "Hslice") as "%Hsz".
  iFrame.
  rewrite -Hsz in Hmmin.
  rewrite firstn_all in Hmmin.
  iPureIntro.
  apply Hmmin.
Admitted.

End common_proof.
