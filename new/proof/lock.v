From New.code Require Import github_com.mit_pdos.gokv.lockservice.
From New.proof Require Import grove_prelude std kv.

Section defns.

Context `{!gooseGlobalGS Σ}.

(* KV points-to for the internal kv service *)
Record lockservice_params :=
  mk_lockservice_params {
    kvptsto_lock : string → string → iProp Σ
  }.

Definition lock_inv γ key R : iProp Σ :=
  ∃ b : bool, kvptsto_lock γ key (if b then "1" else "") ∗ if b then True else R.

Definition is_lock N `{invGS Σ} γ key R :=
  inv N (lock_inv γ key R).

End defns.

Section proof.
Context `{!heapGS Σ}.

Context (N: namespace).

Lemma lock_alloc `{invGS Σ} γ E key R :
  kvptsto_lock γ key "" -∗ R ={E}=∗ is_lock N γ key R.
Proof.
  iIntros "Hkv HR".
  iMod (inv_alloc _ _ (lock_inv γ key R) with "[Hkv HR]").
  { iNext. iExists false. iFrame. }
  eauto.
Qed.

Definition is_LockClerk (ck:loc) γ : iProp Σ :=
  ∃ (kv : val) E,
    "#Hkv_ptsto" ∷ ck ↦s[LockClerk :: "kv"]□ kv ∗
    "#Hkv_is" ∷ is_KvCput kv (kvptsto_lock γ) E ∗
    "%Hdisj" ∷ ⌜ E ## ↑N ⌝
.

Lemma wp_MakeLockClerk (kv : val) kvptsto E :
has_go_type kv interfaceT →
  {{{
       is_KvCput kv kvptsto E ∗
       ⌜ E ## ↑N ⌝
  }}}
    MakeLockClerk kv
  {{{
       (ck:loc), RET #ck; is_LockClerk ck (mk_lockservice_params kvptsto)
  }}}
.
Proof.
  intros ?.
  iIntros (?) "[#? %] HΦ".
  wp_rec.
  wp_alloc k as "?".
  wp_pures.
  wp_load. wp_pures.
  wp_apply wp_ref_ty.
  { (* FIXME: [solve_has_go_type] gets stuck *)
    econstructor. intros.
    repeat (destruct H1; [injection H1 as <- <-; repeat apply zero_val_has_go_type || done|]).
    destruct H1.
  }
  iIntros (?) "Hl".

  (* FIXME: automate splitting. *)
  iDestruct (struct_fields_split with "Hl") as "Hl".
  { done. }
  { apply _. }
  iEval (repeat (rewrite zero_val_eq || rewrite struct.val_unseal)) in "Hl".
  iNamed "Hl".

  wp_pures.
  iApply "HΦ".
  iMod (typed_pointsto_persist with "Hkv") as "#Hkv".
  iModIntro. iFrame "∗#". done.
Qed.

Lemma wp_LockClerk__Lock ck key γ R :
  {{{
       is_LockClerk ck γ ∗ is_lock N γ key R
  }}}
    LockClerk__Lock #ck #(str key)
  {{{
       RET #(); R
  }}}
.
Proof.
  iIntros (Φ) "(#Hck&#Hlock) HΦ".
  wp_rec.
  wp_pures.
  wp_alloc ck_ptr as "?".
  wp_alloc key_ptr as "?".
  wp_pures.
  wp_for.
  wp_pures.
  wp_load.
  wp_pure_credit "Hlc".
  wp_pures.
  wp_load.
  wp_pures.
  iNamed "Hck".
  wp_load.
  wp_pures.
  iNamed "Hkv_is".
  wp_apply ("HcputSpec" with "[//]").
  rewrite /is_lock.
  iInv "Hlock" as "Hlock_inner" "Hclo".
  iMod (lc_fupd_elim_later with "Hlc Hlock_inner") as "Hlock_inner".
  iDestruct "Hlock_inner" as (?) "(Hk&HR)".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _. iFrame "Hk".
  iIntros "Hk".
  iMod "Hmask".
  destruct b.
  - rewrite bool_decide_false //.
    iMod ("Hclo" with "[HR Hk]").
    { iExists true. iFrame. }
    iModIntro. iIntros "Hck". wp_pures. iModIntro. iLeft.
    iSplit; first by eauto.
    wp_pures.
    iModIntro. iApply wp_for_post_do.
    wp_pures. by iFrame.
  - rewrite bool_decide_true //.
    iMod ("Hclo" with "[Hk]").
    { iExists true. iFrame. }
    iModIntro. iIntros "Hck". wp_pures. iModIntro. iRight.
    iSplit; first by eauto.
    wp_pures. iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma wp_LockClerk__Unlock ck key γ R :
  {{{
       is_LockClerk ck γ ∗ is_lock N γ key R ∗ R
  }}}
    LockClerk__Unlock #ck #(str key)
  {{{
       RET #(); True
  }}}
.
Proof.
  iIntros (Φ) "(#Hck&#Hlock&HR) HΦ".
  wp_rec.
  wp_pure_credit "Hlc".
  wp_pures.
  iNamed "Hck".
  wp_alloc ck_ptr as "?".
  wp_alloc key_ptr as "?".
  iNamed "Hkv_is".
  wp_load.
  wp_pures.
  wp_load.
  wp_load.
  iNamed "Hkv".
  wp_apply ("HputSpec" with "[//]").
  rewrite /is_lock.
  iInv "Hlock" as "Hlock_inner" "Hclo".
  iMod (lc_fupd_elim_later with "Hlc Hlock_inner") as "Hlock_inner".
  iDestruct "Hlock_inner" as (?) "(Hk&_)".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _. iFrame "Hk".
  iIntros "Hk".
  iMod "Hmask".
  iMod ("Hclo" with "[HR Hk]").
  { iExists false. iFrame. }
  iModIntro. iIntros "Hck".
  wp_pures. by iApply "HΦ".
Qed.

End proof.
