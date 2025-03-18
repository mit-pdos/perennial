From New.code Require Import github_com.mit_pdos.gokv.lockservice.
From New.proof Require Import grove_prelude std kv.
Require Import New.generatedproof.github_com.mit_pdos.gokv.lockservice.

Section defns.

Context `{!gooseGlobalGS Σ}.

(* KV points-to for the internal kv service *)
Record lockservice_params :=
  mk_lockservice_params {
    kvptsto_lock : go_string → go_string → iProp Σ
  }.

Definition lock_inv γ key R : iProp Σ :=
  ∃ b : bool, kvptsto_lock γ key (if b then "1" else "")%go ∗ if b then True else R.

Definition is_lock N `{invGS Σ} γ key R :=
  inv N (lock_inv γ key R).

End defns.

Section proof.
Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

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
  ∃ kv E,
    "#Hkv_ptsto" ∷ ck ↦s[lockservice.LockClerk :: "kv"]□ kv ∗
    "#Hkv_is" ∷ is_KvCput kv (kvptsto_lock γ) E ∗
    "%Hdisj" ∷ ⌜ E ## ↑N ⌝
.

Global Instance is_LockClerk_pers ck γ : Persistent (is_LockClerk ck γ) := _.

Global Instance is_lock_pers N γ key R : Persistent (is_lock N γ key R) := _.

#[global]
Program Instance : IsPkgInit lockservice :=
  ltac2:(build_pkg_init ()).

Lemma wp_MakeLockClerk kv kvptsto E :
  {{{
       is_pkg_init lockservice ∗
       is_KvCput kv kvptsto E ∗
       ⌜ E ## ↑N ⌝
  }}}
    lockservice @ "MakeLockClerk" #kv
  {{{
       (ck:loc), RET #ck; is_LockClerk ck (mk_lockservice_params kvptsto)
  }}}
.
Proof.
  wp_start as "[#? %]".
  wp_auto.
  wp_alloc l as "l".
  iDestruct (struct_fields_split with "l") as "l".
  iNamed "l".
  iPersist "Hkv".
  wp_auto. iApply "HΦ". iFrame "∗#%".
Qed.

Lemma wp_LockClerk__Lock ck key γ R :
  {{{
      is_pkg_init lockservice ∗
      is_LockClerk ck γ ∗ is_lock N γ key R
  }}}
    ck @ lockservice @ "LockClerk'ptr" @ "Lock" #key
  {{{
       RET #(); R
  }}}
.
Proof.
  wp_start as "(#Hck&#Hlock)".
  iNamed "Hck".
  iNamed "Hkv_is".
  wp_auto_lc 1.
  wp_for.
  wp_apply ("HcputSpec" with "[//]").
  rewrite /is_lock.
  iInv "Hlock" as "Hlock_inner" "Hclo".
  iMod (lc_fupd_elim_later with "[$] Hlock_inner") as "Hlock_inner".
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
    iModIntro. iIntros "Hck". wp_auto_lc 1. rewrite decide_True //. wp_auto.
    wp_for_post. by iFrame.
  - rewrite bool_decide_true //.
    iMod ("Hclo" with "[Hk]").
    { iExists true. iFrame. }
    iModIntro. iIntros "Hck". wp_auto. rewrite bool_decide_true // decide_False //.
    2:{ naive_solver. } rewrite decide_True //.
    wp_auto. iApply "HΦ". iFrame.
Qed.

Lemma wp_LockClerk__Unlock ck key γ R :
  {{{
       is_pkg_init lockservice ∗ is_LockClerk ck γ ∗ is_lock N γ key R ∗ R
  }}}
    ck @ lockservice @ "LockClerk'ptr" @ "Unlock" #key
  {{{
       RET #(); True
  }}}
.
Proof.
  wp_start as "(#Hck&#Hlock&HR)".
  iNamed "Hck".
  iNamed "Hkv_is".
  iNamed "Hkv".
  wp_auto_lc 1.
  wp_apply ("HputSpec" with "[//]").
  rewrite /is_lock.
  iInv "Hlock" as "Hlock_inner" "Hclo".
  iMod (lc_fupd_elim_later with "[$] Hlock_inner") as "Hlock_inner".
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
  wp_auto. by iApply "HΦ".
Qed.

End proof.

Typeclasses Opaque is_lock is_LockClerk.
