From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat Require Import full.
From iris.unstable.base_logic Require Import mono_list.
From Perennial.algebra Require Import ghost_var.
From Perennial.program_proof.chat.full Require Import lib.

Section proof.

Context `{!heapGS Σ, !ghost_varG Σ nat, !mono_listG msgT.t Σ}.

Definition P γa γb (l : list msgT.t) : iProp Σ :=
  (⌜l = []⌝) ∨
  (⌜l = [msgT.mk 10]⌝ ∗ ghost_var γa DfracDiscarded 0) ∨
  (⌜l = [msgT.mk 10; msgT.mk 11]⌝ ∗
    ghost_var γa DfracDiscarded 0 ∗ ghost_var γb DfracDiscarded 0).

Ltac t_small :=
  simpl in *;
  word.

Ltac t_shot :=
  by iDestruct (ghost_var_valid_2 with "[$] [$]") as %[? _].

Lemma wp_alice (γ γa γb : gname) cp l :
  {{{
    "#Hcli" ∷ is_ChatCli γ (P γa γb) cp ∗
    "#Htriv_lb" ∷ mono_list_lb_own γ l ∗
    "Hγ" ∷ ghost_var γa (DfracOwn 1) 0
  }}}
  alice #cp
  {{{ RET #(); True }}}.
Proof.
  rewrite /alice.
  iIntros (Φ) "H HΦ".
  iNamed "H".

  wp_apply wp_allocStruct; [val_ty|].
  iIntros (a) "Ha".
  iDestruct (struct_fields_split with "Ha") as "H".
  iNamed "H".
  iMod (readonly_alloc_1 with "body") as "#Ha".

  wp_apply wp_allocStruct; [val_ty|].
  iIntros (b) "Hb".
  iDestruct (struct_fields_split with "Hb") as "H".
  iNamed "H".
  iMod (readonly_alloc_1 with "body") as "#Hb".

  wp_apply (wp_put with "[$Hcli $Htriv_lb Ha Hγ]").
  {
    instantiate (1:=msgT.mk _).
    iFrame "#".
    iIntros (?) "% #HP".
    iEval (rewrite /P) in "HP".
    iDestruct "HP" as "[->|[[-> #Hro]|[-> [#Hro _]]]]"; [|t_shot|t_shot].
    {
      iMod (ghost_var_persist with "[$]") as "#Hγ".
      iRight.
      iLeft.
      by iFrame "#".
    }
  }

  wp_apply (wp_get with "[$]").
  iIntros (???) "{Htriv_lb} H".
  iNamed "H".
  clear Hpref.
  wp_apply wp_slice_len.

  wp_if_destruct.
  2: by iApply "HΦ".

  iDestruct (own_slice_small_sz with "[$]") as %Hlen.
  iDestruct (big_sepL2_length with "Hsep") as %Hlen'.
  rewrite /P.
  iDestruct "HP" as "[->|[[-> _]|[-> _]]]"; [t_small|t_small|].
  clear Hlen' Heqb0.

  iDestruct (big_sepL2_cons_inv_r with "Hsep") as (??) "{Hsep} [-> (Hsep0 & Hsep)]".
  iDestruct (big_sepL2_cons_inv_r with "Hsep") as (? lnil) "{Hsep} [-> (Hsep1 & Hsep)]".
  destruct lnil; [|done].
  iClear "Hsep".

  wp_apply (wp_SliceGet with "[$Hsl]"); [done|].
  iIntros "Hsl".
  wp_apply (wp_loadField_ro with "[$Hsep0]").
  iClear "Hsep0".
  wp_apply (wp_loadField_ro with "[$Ha]").
  wp_apply wp_Assert; [done|].

  wp_apply (wp_SliceGet with "[$Hsl]"); [done|].
  iIntros "Hsl".
  wp_apply (wp_loadField_ro with "[$Hsep1]").
  iClear "Hsep1".
  wp_apply (wp_loadField_ro with "[$Hb]").
  wp_apply wp_Assert; [done|].

  wp_apply wp_slice_len.
  wp_apply wp_Assert.
  {
    simpl in *.
    rewrite bool_decide_eq_true.
    repeat f_equal.
    word.
  }
  iClear (Hlen) "Hsl".

  wp_apply (wp_get with "[$]").
  iIntros (???) "{Hl_lb} H".
  iNamed "H".
  apply prefix_length in Hpref.
  iDestruct "HP" as "[->|[[-> _]|[-> _]]]"; [t_small|t_small|].
  iClear (Hpref) "Hl_lb".

  iDestruct (big_sepL2_cons_inv_r with "Hsep") as (??) "{Hsep} [-> (Hsep0 & Hsep)]".
  iDestruct (big_sepL2_cons_inv_r with "Hsep") as (? lnil) "{Hsep} [-> (Hsep1 & Hsep)]".
  destruct lnil; [|done].
  iClear "Hsep".

  wp_apply (wp_SliceGet with "[$Hsl]"); [done|].
  iIntros "Hsl".
  wp_apply (wp_loadField_ro with "[$Hsep0]").
  iClear "Hsep0".
  wp_apply (wp_loadField_ro with "[$Ha]").
  wp_apply wp_Assert; [done|].

  wp_apply (wp_SliceGet with "[$Hsl]"); [done|].
  iIntros "Hsl".
  wp_apply (wp_loadField_ro with "[$Hsep1]").
  iClear "Hsep1".
  wp_apply (wp_loadField_ro with "[$Hb]").
  wp_apply wp_Assert; [done|].

  iDestruct (own_slice_small_sz with "[$]") as %Hlen.
  wp_apply wp_slice_len.
  wp_apply wp_Assert.
  {
    simpl in *.
    rewrite bool_decide_eq_true.
    repeat f_equal.
    word.
  }
  iClear (Hlen) "Hsl".

  wp_pures.
  by iApply "HΦ".
Qed.

Lemma wp_bob (γ γa γb : gname) cp l :
  {{{
    "#Hcli" ∷ is_ChatCli γ (P γa γb) cp ∗
    "#Htriv_lb" ∷ mono_list_lb_own γ l ∗
    "Hγ" ∷ ghost_var γb (DfracOwn 1) 0
  }}}
  bob #cp
  {{{ RET #(); True }}}.
Proof.
  rewrite /bob.
  iIntros (Φ) "H HΦ".
  iNamed "H".

  wp_apply wp_allocStruct; [val_ty|].
  iIntros (a) "Ha".
  iDestruct (struct_fields_split with "Ha") as "H".
  iNamed "H".
  iMod (readonly_alloc_1 with "body") as "#Ha".

  wp_apply wp_allocStruct; [val_ty|].
  iIntros (b) "Hb".
  iDestruct (struct_fields_split with "Hb") as "H".
  iNamed "H".
  iMod (readonly_alloc_1 with "body") as "#Hb".

  wp_apply (wp_get with "[$]").
  iIntros (???) "{Htriv_lb} H".
  iNamed "H".
  clear Hpref.
  wp_apply wp_slice_len.

  wp_if_destruct.
  2: by iApply "HΦ".

  iDestruct (own_slice_small_sz with "[$]") as %Hlen.
  iDestruct (big_sepL2_length with "Hsep") as %Hlen'.
  rewrite /P.
  iDestruct "HP" as "[->|[[-> _]|[-> [_ #Hro]]]]"; [t_small|..|t_shot].
  clear Hlen' Heqb0.

  iDestruct (big_sepL2_cons_inv_r with "Hsep") as (? lnil) "{Hsep} [-> (Hsep0 & Hsep)]".
  destruct lnil; [|done].
  iClear "Hsep".

  wp_apply (wp_SliceGet with "[$Hsl]"); [done|].
  iIntros "Hsl".
  wp_apply (wp_loadField_ro with "[$Hsep0]").
  iClear "Hsep0".
  wp_apply (wp_loadField_ro with "[$Ha]").
  wp_apply wp_Assert; [done|].

  wp_apply wp_slice_len.
  wp_apply wp_Assert.
  {
    simpl in *.
    rewrite bool_decide_eq_true.
    repeat f_equal.
    word.
  }
  iClear (Hlen) "Hsl".

  wp_apply (wp_put with "[$Hcli $Hl_lb Hb Hγ]").
  {
    instantiate (1:=msgT.mk _).
    iFrame "#".
    iIntros (?) "%Hpref #HP".
    apply prefix_length in Hpref.
    iDestruct "HP" as "[->|[[-> #Hro]|[-> [_ #Hro]]]]"; [t_small|..|t_shot].
    {
      iMod (ghost_var_persist with "[$]") as "#Hγ".
      iRight.
      iRight.
      by iFrame "#".
    }
  }

  wp_pures.
  by iApply "HΦ".
Qed.

Lemma wp_main :
  {{{ True }}}
  main #()
  {{{ RET #(); True }}}.
Proof using ghost_varG0 heapGS0 mono_listG0 Σ.
  rewrite /main.
  iIntros (Φ) "_ HΦ".

  iMod (ghost_var_alloc 0) as (γa) "Hγa".
  iMod (ghost_var_alloc 0) as (γb) "Hγb".

  wp_apply (wp_init (P γa γb)).
  {
    rewrite /P.
    naive_solver.
  }
  iIntros (??) "H".
  iNamed "H".

  wp_apply (wp_fork with "[Hγa]").
  {
    iModIntro.
    by wp_apply (wp_alice with "[$]").
  }
  wp_apply (wp_bob with "[$]").

  wp_pures.
  by iApply "HΦ".
Qed.

End proof.
