From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat Require Import full.
From iris.unstable.base_logic Require Import mono_list.

Module msgT.
Record t :=
  mk {
    body: u64
  }.
End msgT.

Section lib.

Context `{!heapGS Σ, !mono_listG msgT.t Σ}.

Definition lockR_ChatCli γ (P : list msgT.t → iProp Σ) cp : iProp Σ :=
  ∃ (lg : Slice.t) (lloc : list loc) (lmsg : list msgT.t),
  (* Note: need □ P so Get() can simultaneously
  close lock inv and return P. *)
  "#HP" ∷ □ P lmsg ∗
  "Hl_auth" ∷ mono_list_auth_own γ 1 lmsg ∗
  "Hlg" ∷ cp ↦[ChatCli :: "log"] lg ∗
  "Hsl" ∷ own_slice lg ptrT 1 lloc ∗
  "#Hsep" ∷ ([∗ list] x1;x2 ∈ lloc;lmsg,
    readonly (x1 ↦[msgT :: "body"] #x2.(msgT.body))).

Definition is_ChatCli γ P cp : iProp Σ :=
  ∃ (lk : loc),
  "#Hlk" ∷ readonly (cp ↦[ChatCli :: "lock"] #lk) ∗
  "#Hlk_inv" ∷ is_lock nroot #lk (lockR_ChatCli γ P cp).

Lemma wp_init P :
  {{{
    (* Note: need □ P to establish lock inv with □ P. *)
    "#HP" ∷ □ P []
  }}}
  Init #()
  {{{
    γ cp,
    RET #cp;
    "#Htriv_lb" ∷ mono_list_lb_own γ [] ∗
    "#Hcli" ∷ is_ChatCli γ P cp
  }}}.
Proof.
  rewrite /Init.
  iIntros (Φ) "H HΦ".
  iNamed "H".

  wp_apply wp_allocStruct; [val_ty|].
  iIntros (cp) "Hcli".
  iDestruct (struct_fields_split with "Hcli") as "H".
  iNamed "H".

  wp_apply wp_NewSlice.
  iIntros (lg) "Hsl".
  wp_storeField.

  iMod (mono_list_own_alloc []) as (γ) "(Hauth & Hlb)".
  iAssert (lockR_ChatCli _ P _) with "[log Hsl Hauth]" as "HR".
  {
    rewrite /lockR_ChatCli.
    iExists _, _, _.
    iFrame.
    naive_solver.
  }

  wp_apply (newlock_spec nroot with "[HR]").
  1: iApply "HR".
  iIntros (?) "#Hlk_inv".
  wp_storeField.

  iApply "HΦ".
  iFrame.
  rewrite /is_ChatCli.
  iMod (readonly_alloc_1 with "lock") as "#Hlk".
  iExists _.
  by iFrame "#".
Qed.

Lemma wp_put cp γ P p m lmsg :
  {{{
    "#Hcli" ∷ is_ChatCli γ P cp ∗
    "#Hm" ∷ readonly (p ↦[msgT :: "body"] #m.(msgT.body)) ∗
    "#Hl_lb" ∷ mono_list_lb_own γ lmsg ∗
    (* Note: need □ on fupd RHS to establish lock inv with □ P. *)
    "Hfupd" ∷ (∀ l', ⌜lmsg `prefix_of` l'⌝ -∗ P l' ={⊤}=∗ □ P (l' ++ [m]))
  }}}
  ChatCli__Put #cp #p
  {{{ RET #(); True }}}.
Proof.
  rewrite /ChatCli__Put.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  rewrite /is_ChatCli.
  iNamed "Hcli".
  wp_apply (wp_loadField_ro with "[$Hlk]").

  wp_apply (acquire_spec with "[$]").
  iIntros "(Hlocked & HR)".
  rewrite /lockR_ChatCli.
  iNamed "HR".

  wp_loadField.
  wp_apply (wp_SliceAppend with "[$]").
  iIntros (lg') "Hsl".
  wp_storeField.
  wp_loadField.

  iDestruct (mono_list_auth_lb_valid with "[$] [$]") as %[_ Hpref].
  iDestruct ("Hfupd" $! lmsg0 Hpref with "[$]") as "> Hfupd".
  iMod (mono_list_auth_own_update_app [m] with "[$]") as "(Hl_auth & _)".

  wp_apply (release_spec with "[-HΦ $Hlk_inv $Hlocked]").
  {
    iExists _, _, _.
    iFrame "∗#".
    naive_solver.
  }

  wp_pures.
  by iApply "HΦ".
Qed.

Lemma wp_get cp γ P lold :
  {{{
    "#Hcli" ∷ is_ChatCli γ P cp ∗
    "#Hlold_lb" ∷ mono_list_lb_own γ lold
  }}}
  ChatCli__Get #cp
  {{{
    (lg : Slice.t) (lloc : list loc) (lmsg : list msgT.t),
    RET (slice_val lg);
    "#Hl_lb" ∷ mono_list_lb_own γ lmsg ∗
    "Hsl" ∷ own_slice_small lg ptrT 1 lloc ∗
    "%Hpref" ∷ ⌜lold `prefix_of` lmsg⌝ ∗
    "HP" ∷ P lmsg ∗
    "#Hsep" ∷ ([∗ list] x1;x2 ∈ lloc;lmsg,
      readonly (x1 ↦[msgT :: "body"] #x2.(msgT.body)))
  }}}.
Proof.
  rewrite /ChatCli__Get.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  iNamed "Hcli".

  wp_apply (wp_loadField_ro with "[$]").
  wp_apply (acquire_spec with "[$]").
  iIntros "(Hlocked & H)".
  iNamed "H".
  wp_loadField.
  wp_apply wp_slice_len.
  iDestruct (own_slice_sz with "[$]") as %Hlen.
  wp_apply wp_NewSlice.
  iIntros (ret) "Hret".
  wp_loadField.
  iDestruct (own_slice_small_read with "Hsl") as "(Hsl & Hsl_conv)".
  iDestruct (own_slice_to_small with "Hret") as "Hret".

  wp_apply (wp_SliceCopy_full_typed with "[$Hsl $Hret]").
  {
    iPureIntro.
    rewrite length_replicate.
    word.
  }
  iIntros "(Hsl & Hret)".
  iDestruct ("Hsl_conv" with "Hsl") as "Hsl".

  iDestruct (mono_list_auth_lb_valid with "[$] [$]") as %[_ Hpref].
  iDestruct (mono_list_lb_own_get with "Hl_auth") as "#Hl_lb".
  wp_loadField.
  wp_apply (release_spec with "[-HΦ Hret $Hlk_inv $Hlocked]").
  {
    iExists _, _, _.
    iFrame "∗#".
  }

  wp_pures.
  iApply "HΦ".
  by iFrame "∗#".
Qed.

End lib.
