From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv memkv.lockservice.
From Perennial.program_proof.memkv Require Export common_proof memkv_clerk_proof.

Section lockservice_proof.

Context `{!kvMapG Σ}.
Definition lock_inv (γkv : gname) key R : iProp Σ :=
  ∃ b : bool, kvptsto γkv key (if b then [W8 0] else []) ∗ if b then True else R.

Context (N: namespace).

Definition is_lock `{invGS Σ} γkv key R :=
  inv N (lock_inv γkv key R).

Lemma lock_alloc `{invGS Σ} E γkv key R :
  kvptsto γkv key [] -∗ R ={E}=∗ is_lock γkv key R.
Proof.
  iIntros "Hkv HR".
  iMod (inv_alloc _ _ (lock_inv γkv key R) with "[Hkv HR]").
  { iNext. iExists false. iFrame. }
  eauto.
Qed.

Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), !erpcG Σ, !urpcregG Σ}.

Definition own_LockClerk (ck:loc) (γ:gname) : iProp Σ :=
  ∃ (kvCk : loc),
    "HkvCk" ∷ ck ↦[LockClerk :: "kv"] #kvCk ∗
    "#Hclerk" ∷ is_KVClerk kvCk γ.

Lemma wp_MakeLockClerk (coord:u64) cm γ :
  {{{
       is_coord_server coord γ ∗ is_ConnMan cm
  }}}
    MakeLockClerk #coord #cm
  {{{
       (ck:loc), RET #ck; own_LockClerk ck γ.(coord_kv_gn)
  }}}
.
Proof.
  iIntros (Φ) "#[Hcoord Hcm] HΦ".
  rewrite /MakeLockClerk.
  wp_lam.
  wp_apply (wp_MakeKVClerk with "[$] [$]").
  iIntros (kvCk) "H".
  wp_apply wp_allocStruct; first val_ty.
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  iApply "HΦ".
  iExists _. iFrame.
Qed.

Lemma wp_LockClerk__Lock ck γkv key R :
  {{{
       own_LockClerk ck γkv ∗ is_lock γkv key R
  }}}
    LockClerk__Lock #ck #key
  {{{
       RET #(); own_LockClerk ck γkv ∗ R
  }}}
.
Proof.
  iIntros (Φ) "(Hck&#Hlock) HΦ".
  wp_lam.
  wp_pures.
  iCombine "Hck HΦ" as "H".
  wp_apply (wp_forBreak_cond' with "H").
  iModIntro. iIntros "(Hck&HΦ)".
  wp_pures.
  iNamed "Hck".
  wp_apply (typed_slice.wp_NewSlice (V:=u8)).
  iIntros (s1) "Hsl1".
  wp_apply (typed_slice.wp_NewSlice (V:=u8)).
  iIntros (s0) "Hsl0".
  wp_loadField.
  simpl.
  iDestruct (own_slice_to_small with "Hsl0") as "Hsl0".
  iDestruct (own_slice_to_small with "Hsl1") as "Hsl1".
  iMod (own_slice_small_persist with "Hsl0") as "#Hsl0".
  iMod (own_slice_small_persist with "Hsl1") as "#Hsl1".
  wp_apply (wp_KVClerk__ConditionalPut with "[$Hclerk]").
  { iFrame "#". }
  rewrite /is_lock.
  replace (⊤ ∖ ∅) with (⊤ : coPset) by set_solver+.
  iInv "Hlock" as "Hlock_inner" "Hclo".
  iDestruct "Hlock_inner" as (?) "(>Hk&HR)".
  iApply (fupd_mask_weaken ∅); first by set_solver+.
  iIntros "Hclo'".
  iModIntro.
  iExists _. iFrame "Hk".
  iIntros "Hk".
  iMod "Hclo'".
  destruct b.
  - rewrite bool_decide_false //.
    iMod ("Hclo" with "[HR Hk]").
    { iExists true. iFrame. }
    iModIntro. iIntros "Hck". wp_pures. iModIntro. iLeft.
    iSplit; first by eauto.
    iFrame "HΦ". iExists _. eauto with iFrame.
  - rewrite bool_decide_true //.
    iMod ("Hclo" with "[Hk]").
    { iExists true. iFrame. }
    iModIntro. iIntros "Hck". wp_pures. iModIntro. iRight.
    iSplit; first by eauto.
    wp_pures. iModIntro. iApply "HΦ".
    iFrame "HR". iExists _. eauto with iFrame.
Qed.

Lemma wp_LockClerk__Unlock ck γkv key R :
  {{{
       own_LockClerk ck γkv ∗ is_lock γkv key R ∗ R
  }}}
    LockClerk__Unlock #ck #key
  {{{
       RET #(); own_LockClerk ck γkv
  }}}
.
Proof.
  iIntros (Φ) "(Hck&#Hlock&HR) HΦ".
  wp_lam.
  wp_pures.
  iNamed "Hck".
  wp_apply (typed_slice.wp_NewSlice (V:=u8)).
  iIntros (s0) "Hsl0".
  wp_loadField.
  iDestruct (own_slice_to_small with "Hsl0") as "Hsl0".
  iMod (own_slice_small_persist with "Hsl0") as "#Hsl0".
  wp_apply (wp_KVClerk__Put with "[$Hclerk]").
  { iFrame "#". }
  rewrite /is_lock.
  replace (⊤ ∖ ∅) with (⊤ : coPset) by set_solver+.
  iInv "Hlock" as "Hlock_inner" "Hclo".
  iDestruct "Hlock_inner" as (?) "(>Hk&_)".
  iApply (fupd_mask_weaken ∅); first by set_solver+.
  iIntros "Hclo'".
  iModIntro.
  iExists _. iFrame "Hk".
  iIntros "Hk".
  iMod "Hclo'".
  iMod ("Hclo" with "[HR Hk]").
  { iExists false. iFrame. }
  iModIntro. iIntros "Hck". 
  wp_pures. iApply "HΦ". iExists _. eauto with iFrame.
Qed.

End lockservice_proof.
