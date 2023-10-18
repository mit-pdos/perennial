From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat Require Import full.
From iris.unstable.base_logic Require Import mono_list.

Context `{!heapGS Σ}.

Module msgT.
Record t :=
  mk {
    body: u64
  }.

Definition own (p : loc) (v : t) : iProp Σ :=
  "Hbody" ∷ p ↦[msgT :: "body"] #v.(body).

#[refine] #[global] Instance IntoVal : IntoVal t :=
  {
    to_val := λ x, (#x.(body), #())%V;
    from_val := λ x,
      match x with
      | (#(LitInt x'), #())%V => Some (mk x')
      | _ => None
      end;
    IntoVal_def := mk 0;
    IntoVal_inj' := _;
  }.
Proof. Admitted.
End msgT.

Context `{!mono_listG msgT.t Σ}.

Section chat_lib.

Lemma wp_put (P : list msgT.t  → iProp Σ) p m γ l:
  {{{
    msgT.own p m ∗
    mono_list_lb_own γ l ∗
    (∀ l', ⌜l `prefix_of` l'⌝ -∗ □ P l' -∗ □ P (m :: l'))
  }}}
  Put #p
  {{{
    RET #();
    msgT.own p m
  }}}.
Proof. Admitted.

Lemma wp_get (P : list msgT.t  → iProp Σ) γ l:
  {{{
    mono_list_lb_own γ l
  }}}
  Get #()
  {{{
    (sl : Slice.t) (l' : list msgT.t),
    RET (slice_val sl);
    own_slice sl (structTy msgT) 1 l' ∗
    mono_list_lb_own γ l' ∗
    ⌜l `prefix_of` l'⌝ ∗
    □ P l'
  }}}.
Proof. Admitted.
End chat_lib.

Section proof.

Lemma wp_contains sl (l : list msgT.t) mloc (m : msgT.t):
  {{{
    own_slice sl (structTy msgT) 1 l ∗
    msgT.own mloc m
  }}}
  contains (slice_val sl) #mloc
  {{{
    (isIn : bool),
    RET #isIn;
    own_slice sl (structTy msgT) 1 l ∗
    msgT.own mloc m ∗
    ⌜if isIn then m ∈ l else m ∉ l⌝
  }}}.
Proof. Admitted.

Definition P (l : list msgT.t) : iProp Σ :=
  ⌜msgT.mk 11 ∈ l → msgT.mk 10 ∈ l⌝.

Lemma wp_alice:
  {{{ True }}}
  alice #()
  {{{ RET #(); True }}}.
Proof.
  rewrite /alice.
  iIntros (Φ) "_ HΦ".
  wp_apply wp_allocStruct.
  { val_ty. }
  iIntros (a) "Ha".
  iDestruct (struct_fields_split with "Ha") as "HH".
  iNamed "HH".
  iRename "body" into "Ha".
  wp_apply wp_allocStruct.
  { val_ty. }
  iIntros (b) "Hb".
  iDestruct (struct_fields_split with "Hb") as "HH".
  iNamed "HH".
  iRename "body" into "Hb".
  iMod (mono_list_own_alloc []) as (γ) "(Hl_auth & #Hl_lb)".
  wp_apply (wp_put P _ _ γ [] with "[Ha $Hl_lb]").
  {
    instantiate (1:=msgT.mk _).
    rewrite /msgT.own /P /=.
    iFrame.
    iIntros (?) "%Hpref %Hold !%".
    intros Hb.
    apply elem_of_cons.
    naive_solver.
  }
  iIntros "Ha".
  wp_apply (wp_get P γ [] with "[$Hl_lb]").
  iIntros (??) "(Hsl_own & Hl_lb' & %Hpref & %HP)".
  wp_apply (wp_contains with "[$Hsl_own Hb]").
  {
    instantiate (1:=msgT.mk _).
    rewrite /msgT.own /=.
    iFrame.
  }
  iIntros (?) "(Hsl_own & Hb & %HisInB)".
  wp_if_destruct.
  {
    wp_apply (wp_contains with "[$Hsl_own Ha]").
    {
      instantiate (1:=msgT.mk _).
      rewrite /msgT.own /=.
      iFrame.
    }
    iIntros (?) "(Hsl_own & Ha & %HisInA)".
    destruct isIn0.
    {
      wp_pures.
      wp_apply wp_Assert; try done.
      wp_pures.
      by iApply "HΦ".
    }
    {
      specialize (HP HisInB).
      naive_solver.
    }
  }
  by iApply "HΦ".
Qed.

Lemma wp_bob:
  {{{ True }}}
  bob #()
  {{{ RET #(); True }}}.
Proof.
  rewrite /bob.
  iIntros (Φ) "_ HΦ".
  wp_apply wp_allocStruct.
  { val_ty. }
  iIntros (a) "Ha".
  iDestruct (struct_fields_split with "Ha") as "HH".
  iNamed "HH".
  iRename "body" into "Ha".
  wp_apply wp_allocStruct.
  { val_ty. }
  iIntros (b) "Hb".
  iDestruct (struct_fields_split with "Hb") as "HH".
  iNamed "HH".
  iRename "body" into "Hb".
  iMod (mono_list_own_alloc []) as (γ) "(Hl_auth & #Hl_lb)".
  wp_apply (wp_get P γ [] with "[$Hl_lb]").
  iIntros (??) "(Hsl_own & Hl_lb' & %Hpref & %HP)".
  wp_apply (wp_contains with "[$Hsl_own Ha]").
  {
    instantiate (1:=msgT.mk _).
    rewrite /msgT.own /=.
    iFrame.
  }
  iIntros (?) "(Hsl_own & Ha & %HisInA)".
  wp_if_destruct.
  {
    wp_apply (wp_put P _ _ γ l' with "[Hb $Hl_lb']").
    {
      instantiate (1:=msgT.mk _).
      rewrite /msgT.own /P /=.
      iFrame.
      iIntros (?) "%Hpref' %Hold !%".
      intros Hb.
      apply elem_of_cons.
      right.
      apply (elem_of_prefix l' l'0); assumption.
    }
    iIntros "_".
    wp_pures.
    by iApply "HΦ".
  }
  by iApply "HΦ".
Qed.

End proof.
