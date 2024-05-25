From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.vrsm.apps Require Import vkv.
From Perennial.program_proof.vrsm Require Import kv_proof.
From Perennial.program_proof.kv Require Import interface.

Section clerkpool_proof.

Context `{!heapGS Σ, !ekvG Σ}.
Context {params:ekvParams.t}.
Definition own_ClerkPool c γkv : iProp Σ :=
  ∃ (cls:list loc) cls_sl,
  "Hcls" ∷ c ↦[ClerkPool :: "cls"] (slice_val cls_sl) ∗
  "Hcls_sl" ∷ own_slice cls_sl ptrT (DfracOwn 1) (cls) ∗
  "Hcls_own" ∷ ([∗ list] cl ∈ cls, own_Clerk cl γkv)
.

Definition is_ClerkPool c γkv : iProp Σ :=
  ∃ mu confHost_sl (confHosts:list u64),
  "#Hmu" ∷ readonly (c ↦[ClerkPool :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock nroot mu (own_ClerkPool c γkv) ∗
  "#HconfHosts" ∷ readonly (c ↦[ClerkPool :: "confHosts"] (slice_val confHost_sl)) ∗
  "#Hconf_sl" ∷ readonly (own_slice_small confHost_sl uint64T (DfracOwn 1) confHosts) ∗
  "#Hhost" ∷ is_kv_config_hosts confHosts γkv
.

Lemma wp_doWithClerk c γkv (f:val) Φ :
  is_ClerkPool c γkv -∗
  (∀ ck, own_Clerk ck γkv -∗
  WP f #ck {{ λ _, own_Clerk ck γkv ∗ Φ #() }}) -∗
  WP ClerkPool__doWithClerk #c f {{ Φ }}
.
Proof.
  iIntros "#Hck HΦ".
  iNamed "Hck".
  wp_lam.
  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (?) "Hl".
  wp_pures.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_if_destruct.
  {
    iDestruct (own_slice_sz with "[$]") as %Hsz.
    wp_loadField.
    destruct cls.
    { exfalso. simpl in *. word. }
    iDestruct (own_slice_small_acc with "Hcls_sl") as "[Hcls_sl Hcls_acc]".
    wp_apply (wp_SliceGet with "[$Hcls_sl]").
    { done. }
    iIntros "Hcls_sl".
    wp_store.
    wp_loadField.
    wp_apply (wp_SliceSkip).
    { word. }
    wp_storeField.
    wp_loadField.
    iDestruct "Hcls_own" as "[Hcl_own Hcls_own]".
    iDestruct ("Hcls_acc" with "[$]") as "Hcls_sl".
    rewrite own_slice_split.
    iDestruct "Hcls_sl" as "[H1 H2]".
    iDestruct (slice_small_split _ 1 with "[$]") as "[_ Hcls_sl]".
    { word. }
    iDestruct (own_slice_cap_skip _ _ 1 with "[$]") as "?".
    { word. }
    rewrite skipn_cons drop_0.
    wp_apply (release_spec with "[-HΦ Hcl_own Hl]").
    { iFrame "∗#". iNext. repeat iExists _. iFrame "∗#". }
    wp_pures.
    wp_load.
    wp_bind (f #_).
    wp_apply (wp_wand with "[HΦ Hcl_own]").
    { wp_apply ("HΦ"). iFrame. }
    iIntros (?) "[Hck HΦ]".
    wp_pures.
    wp_loadField.
    iClear "Hhost".
    clear.
    wp_apply (acquire_spec with "[$]").
    iIntros "[Hlocked Hown]".
    iNamed "Hown".
    wp_pures.
    wp_load.
    wp_loadField.
    wp_apply (wp_SliceAppend with "[$]").
    iIntros (?) "Hsl".
    wp_storeField.
    wp_loadField.
    wp_apply (release_spec with "[-HΦ Hl]").
    { iFrame "∗#". iNext. repeat iExists _. iFrame "∗#". done. }
    wp_pures.
    iApply "HΦ".
  }
  {
    wp_loadField.
    wp_apply (release_spec with "[-HΦ Hl]").
    { iFrame "∗#". iNext. repeat iExists _. iFrame "∗#". }
    wp_pures.
    wp_loadField.
    wp_apply (wp_MakeClerk with "[]").
    { iFrame "#%". }
    iIntros (?) "Hck".
    wp_store.
    wp_load.
    wp_bind (f #_).
    wp_apply (wp_wand with "[HΦ Hck]").
    { wp_apply ("HΦ"). iFrame. }
    iIntros (?) "[Hck HΦ]".
    wp_pures.
    wp_loadField.
    wp_apply (acquire_spec with "[$]").
    iIntros "[Hlocked Hown]".
    iNamed "Hown".
    wp_pures.
    wp_load.
    wp_loadField.
    wp_apply (wp_SliceAppend with "[$]").
    iIntros (?) "Hsl".
    wp_storeField.
    wp_loadField.
    wp_apply (release_spec with "[-HΦ Hl]").
    { iFrame "∗#". iNext. repeat iExists _. iFrame "∗#". done. }
    wp_pures.
    iApply "HΦ".
  }
Qed.

Lemma wp_MakeClerkPool γkv confHosts confHost_sl :
  {{{
        "#Hconf_sl" ∷ readonly (own_slice_small confHost_sl uint64T (DfracOwn 1) confHosts) ∗
        "#Hhost" ∷ is_kv_config_hosts confHosts γkv
  }}}
    MakeClerkPool (slice_val confHost_sl)
  {{{
        ck, RET #ck; is_ClerkPool ck γkv
  }}}
.
Proof.
  iIntros (?) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (?) "HmuInv".
  wp_apply wp_NewSlice.
  iIntros (?) "Hsl".
  iApply wp_fupd.
  wp_apply wp_allocStruct.
  { val_ty. }
  iIntros (?) "Hc".
  iDestruct (struct_fields_split with "Hc") as "HH".
  iNamed "HH".
  iMod (readonly_alloc_1 with "mu") as "#Hmu".
  iMod (readonly_alloc_1 with "confHosts") as "#HconfHosts".
  iApply "HΦ".
  repeat iExists _; iFrame "#".
  iMod (alloc_lock with "[$] [-]") as "$"; last done.
  iNext. repeat iExists _; iFrame. rewrite replicate_0. iApply big_sepL_nil. done.
Qed.

Definition vkvE : coPset := (↑protocol.pbN ∪ ↑definitions.prophReadN ∪ ↑proof.esmN ∪
                                     ↑stateN).
Lemma wp_MakeKv γkv confHost_sl confHosts :
  {{{
        "#Hconf_sl" ∷ readonly (own_slice_small confHost_sl uint64T (DfracOwn 1) confHosts) ∗
        "#Hhost" ∷ is_kv_config_hosts confHosts γkv
  }}}
    MakeKv (slice_val confHost_sl)
  {{{
        k, RET #k; is_Kv k (kv_ptsto γkv) vkvE

  }}}
.
Proof.
  iIntros (?) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_apply (wp_MakeClerkPool with "[]").
  { iFrame "#%". }
  iIntros (?) "#Hck".
  wp_pures.
  wp_lam. wp_pures.
  wp_lam. wp_pures.
  wp_lam. wp_pures.
  iApply wp_fupd.
  wp_apply (wp_allocStruct).
  { val_ty. }
  iIntros (?) "Hk".
  iDestruct (struct_fields_split with "Hk") as "HH".
  iNamed "HH".
  iApply "HΦ".
  iMod (readonly_alloc_1 with "Put") as "#?".
  iMod (readonly_alloc_1 with "Get") as "#?".
  iMod (readonly_alloc_1 with "ConditionalPut") as "#?".
  repeat iExists _; iFrame "#".
  iModIntro.
  iSplit.
  {
    clear Φ.
    iIntros (?) "* !# * _ Hau".
    wp_pures.
    wp_apply (wp_doWithClerk with "[$]").
    iIntros (?) "Hcl".
    wp_pures.
    wp_apply (wp_Clerk__Put with "[$] [Hau]").
    iNext.
    unfold vkvE.
    iMod "Hau" as (?) "[H1 Hau]".
    iModIntro. iExists _; iFrame.
    iIntros "H1". iMod ("Hau" with "[$]") as "Hau".
    iModIntro.
    iIntros "Hcl".
    wp_pures. iModIntro.
    iFrame. wp_pures. by iApply "Hau".
  }
  iSplit.
  {
    clear Φ.
    iIntros (?) "* !# * _ Hau".
    wp_pures.
    wp_apply (wp_ref_of_zero).
    { done. }
    iIntros (?) "Hl".
    wp_pures.
    wp_apply (wp_doWithClerk with "[$]").
    iIntros (?) "Hcl".
    wp_pures.
    wp_apply (wp_Clerk__Get with "[$]").
    unfold vkvE.
    iMod "Hau" as (?) "[H1 Hau]".
    iModIntro. iExists _; iFrame.
    iIntros "H1". iMod ("Hau" with "[$]") as "Hau".
    iModIntro.
    iIntros "Hcl".
    wp_pures. wp_store. iModIntro.
    iFrame. wp_pures. wp_load. by iApply "Hau".
  }
  {
    clear Φ.
    iIntros (?) "* !# * _ Hau".
    wp_pures.
    wp_apply (wp_ref_of_zero).
    { done. }
    iIntros (?) "Hl".
    wp_pures.
    wp_apply (wp_doWithClerk with "[$]").
    iIntros (?) "Hcl".
    wp_pures.
    wp_apply (wp_Clerk__CondPut with "[$]").
    unfold vkvE.
    iMod "Hau" as (?) "[H1 Hau]".
    iModIntro. iExists _; iFrame.
    iIntros "H1". iMod ("Hau" with "[$]") as "Hau".
    iModIntro.
    iIntros "Hcl".
    wp_pures. wp_store. iModIntro.
    iFrame. wp_pures. wp_load. by iApply "Hau".
  }
Qed.

End clerkpool_proof.
