From New.proof.sync_proof Require Import base.

Section proof.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!syncG Σ}.

Definition is_sema (x : loc) γ N : iProp Σ :=
  inv N (∃ (v : w32), x ↦ v ∗ ghost_var γ (1/2) v).
#[global] Opaque is_sema.
#[local] Transparent is_sema.

Global Instance is_sema_persistent x γ N  : Persistent (is_sema x γ N) := _.

Definition own_sema γ (v : w32) : iProp Σ := ghost_var γ (1/2) v.
#[global] Opaque own_sema.
#[local] Transparent own_sema.
Global Instance own_sema_timeless  γ v : Timeless (own_sema γ v) := _.

Lemma start_sema {E} N sema v :
  sema ↦ v ={E}=∗ ∃ γ, is_sema sema γ N ∗ own_sema γ v.
Proof.
  iIntros "Hs".
  iMod (ghost_var_alloc v) as "[%sema_gn [Hs1 Hs2]]".
  iMod (inv_alloc with "[Hs Hs1]") as "$"; by iFrame.
Qed.

Lemma wp_runtime_Semacquire (sema : loc) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (⌜ uint.nat v > 0 ⌝ → own_sema γ (word.sub v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP sync @ "runtime_Semacquire" #sema {{ Φ }}.
Proof.
  wp_start as "#Hsem".
  wp_for.
  wp_bind (! _)%E.
  iInv "Hsem" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hs Hv]".
  unshelve iApply (wp_typed_Load with "[$Hs]"); try tc_solve.
  { done. }
  iNext.
  iIntros "Hs".
  iMod ("Hclose" with "[$]") as "_".
  iModIntro.
  wp_auto.
  destruct bool_decide eqn:Hnz.
  { (* keep looping *)
    wp_auto.
    wp_for_post.
    iFrame.
  }

  (* try to acquire *)
  rewrite bool_decide_eq_false in Hnz.
  wp_auto.
  wp_bind (CmpXchg _ _ _).
  iInv "Hsem" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hs Hv]".
  destruct (decide (v = v0)).
  {
    subst. iMod "HΦ" as (?) "[Hv2 HΦ]".
    iCombine "Hv Hv2" as "Hv" gives %[_ <-].
    iMod (ghost_var_update with "Hv") as "[Hv Hv2]".
    unshelve iApply (wp_typed_cmpxchg_suc with "[$]"); try tc_solve; try done.
    iNext. iIntros "Hs".
    iMod ("HΦ" with "[] [$]") as "HΦ".
    { iPureIntro.
      (* FIXME: word *)
      assert (uint.nat v0 ≠ O).
      { intros ?. apply Hnz. word. }
      word.
    }
    iModIntro.
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_auto.
    wp_for_post.
    done.
  }
  { (* cmpxchg will fail *)
    unshelve iApply (wp_typed_cmpxchg_fail with "[$]"); try tc_solve.
    { done. }
    { naive_solver. }
    iNext. iIntros "Hs".
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_auto.
    wp_for_post.
    iFrame.
  }
Qed.

Lemma wp_runtime_SemacquireWaitGroup (sema : loc) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (⌜ uint.nat v > 0 ⌝ → own_sema γ (word.sub v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP sync @ "runtime_SemacquireWaitGroup" #sema {{ Φ }}.
Proof.
  wp_start as "#Hsem".
  wp_apply (wp_runtime_Semacquire with "[$]").
  iFrame.
Qed.

Lemma wp_runtime_Semrelease (sema : loc) γ N (_u1 : bool) (_u2 : w64):
  ∀ Φ,
  is_pkg_init sync ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (own_sema γ (word.add v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP sync @ "runtime_Semrelease" #sema #_u1 #_u2 {{ Φ }}.
Proof.
Admitted.

End proof.
