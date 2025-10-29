From iris.proofmode Require Import environments.
From New.proof.sync_proof Require Import base mutex.
From New.proof.sync Require Import atomic.

From iris_named_props Require Import custom_syntax.

Local Existing Instances tokG wg_totalG rw_ghost_varG rw_ghost_wlG rw_ghost_rwmutexG  wg_auth_inG.

(**
A [sync.Once] will perform exactly one action. The specification realizes this
by requiring a specification for that action (a pre- and post-condition), a
proof of the precondition (which is used only once), and a proof that the
post-condition is persistent.

Every call to [Once.Do(f)] returns [Q] as a postcondition (using its persistence
to duplicate the postcondition to the first call), but uses the pre-condition
only once.

It is valid to call [Once.Do(f)] with different values of [f], but they must all
satisfy [{P} #f #() {Q}].
*)

Section proof.
Context `{hG:heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Definition is_Once (o: loc) (P: iProp Σ) (Q: iProp Σ) : iProp Σ :=
  "#Q_persistent" ∷ □(Q -∗ □Q) ∗
  "Qinv" ∷ inv nroot (
    ∃ (done: bool),
    "done1" ∷ own_Uint32 (struct.field_ref_f sync.Once "done" o) (DfracOwn (1/2)) (W32 (if done then 1 else 0)) ∗
    "#HQ" ∷ □(⌜done = true⌝ -∗ Q)
  ) ∗
  "Hm" ∷ is_Mutex (struct.field_ref_f sync.Once "m" o) (
      ∃ (done: bool),
      "done2" ∷ own_Uint32 (struct.field_ref_f sync.Once "done" o) (DfracOwn (1/2)) (W32 (if done then 1 else 0)) ∗
      "HPQ" ∷ (if done then Q else P)
    )
 .
#[global] Opaque is_Once.
#[local] Transparent is_Once.

Lemma init_Once o P Q E :
  Persistent Q →
  o ↦ default_val sync.Once.t ∗ P ⊢ |={E}=> is_Once o P Q.
Proof.
  intros HQ.
  iIntros "[o HP]".
  iSplitR.
  { iModIntro.
    iIntros "!> #$". }
  iDestruct (struct_fields_split with "o") as "o". iNamed "o".
  simpl.
  iDestruct "Hdone" as "[done1 done2]".
  iMod (init_Mutex with "Hm [done2 HP]") as "$".
  {
    iExists (false). iFrame.
  }
  iMod (inv_alloc with "[done1]") as "$".
  {
    iExists (false). iFrame.
    iIntros (?). congruence.
  }
  done.
Qed.

Lemma wp_Once__doSlow o P Q (f: func.t) :
  {{{ is_pkg_init sync ∗ is_Once o P Q ∗ {{{ P }}} #f #() {{{ RET #(); Q }}} }}}
    o @ (ptrT.id sync.Once.id) @ "doSlow" #f
  {{{ RET #(); Q }}}.
Proof.
  wp_start as "[#@ #Hf]".
  wp_apply wp_with_defer as "%defer defer".
  simpl subst. wp_auto_lc 2.
  wp_apply (wp_Mutex__Lock with "[$Hm]").
  iIntros "[Hlocked @]".
  wp_auto.
  wp_apply wp_Uint32__Load.
  iInv "Qinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iNamedSuffix "Hi" "_inv".
  iApply fupd_mask_intro. { solve_ndisj. } iIntros "Hmask".
  iFrame "done1_inv"; iIntros "!> done1_inv".
  iCombine "done1_inv done2" gives %[? ?].
  assert (done0 = done) as ->.
  {
    destruct done0, done; auto; word.
  }
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[done1_inv]") as "_".
  {
    iModIntro. iExists _.
    iFrame "HQ_inv ∗".
  }
  iModIntro.
  wp_auto.
  destruct done.
  - rewrite bool_decide_eq_false_2; [ | word ]; wp_auto.
    iAssert (□Q)%I with "[HPQ]" as "#HQ".
    {
      by iApply "Q_persistent".
    }
    wp_apply (wp_Mutex__Unlock with "[$Hm done2 Hlocked]").
    { iFrame.
      iExists (true). iFrame. iFrame "HQ".
    }
    iApply "HΦ". iFrame.
  - wp_auto. wp_apply ("Hf" with "HPQ").
    iIntros "Q".
    iAssert (□Q)%I with "[Q]" as "#HQ".
    {
      by iApply "Q_persistent".
    }
    wp_auto.
    wp_apply wp_Uint32__Store.
    iInv "Qinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iNamedSuffix "Hi" "_inv2".
    iApply fupd_mask_intro. { solve_ndisj. } iIntros "Hmask".
    iCombine "done1_inv2 done2" gives %[? ?].
    assert (done = false); [ | subst ].
    {
      destruct done; auto; word.
    }
    iCombine "done1_inv2 done2" as "done".
    iFrame "done". iIntros "!> [done1 done2]".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[done1]") as "_".
    {
      iModIntro. iExists (true).
      iFrame.
      iIntros "!> _". done.
    }
    iModIntro.
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$Hm done2 Hlocked]").
    { iFrame.
      iExists (true). iFrame. iFrame "HQ".
    }
    iApply "HΦ". iFrame.
Qed.

Lemma wp_Once__Do o P Q (f: func.t) :
  {{{ is_pkg_init sync ∗ is_Once o P Q ∗ {{{ P }}} #f #() {{{ RET #(); Q }}} }}}
    o @ (ptrT.id sync.Once.id) @ "Do" #f
  {{{ RET #(); Q }}}.
Proof.
  wp_start as "[#@ #Hf]".
  wp_auto_lc 1.
  wp_apply wp_Uint32__Load.
  iInv "Qinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iNamedSuffix "Hi" "_inv".
  iApply fupd_mask_intro. { solve_ndisj. } iIntros "Hmask".
  iExists _.
  iFrame "done1_inv"; iIntros "!> done1_inv".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[done1_inv]") as "_".
  {
    iModIntro. iExists _.
    iFrame "HQ_inv ∗".
  }
  iModIntro.
  wp_auto.
  destruct done.
  - wp_if_destruct; [ exfalso; word | ].
    iApply "HΦ".
    iApply "HQ_inv".
    done.
  - wp_if_destruct; [ | exfalso; word ].
    wp_apply wp_Once__doSlow.
    { iFrame "#". }
    iIntros "HQ".
    wp_auto.
    by iApply "HΦ".
Qed.

End proof.
