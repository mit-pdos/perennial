From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat Require Import full.
From iris.unstable.base_logic Require Import mono_list.
From Perennial.algebra Require Import ghost_var.

Context `{!heapGS Σ}.
Context `{!ghost_varG Σ nat}.

Module msgT.

Record t :=
  mk {
    body: u64
  }.

Definition own (p : loc) (v : t) : iProp Σ :=
  "Hbody" ∷ p ↦[msgT :: "body"] #v.(body).

Global Instance IntoVal : IntoVal t.
Proof.
  refine {|
    to_val := λ x, (#x.(body), #())%V;
    from_val := λ x,
      match x with
      | (#(LitInt x'), #())%V => Some (mk x')
      | _ => None
      end;
    IntoVal_def := mk 0;
  |}.
  intros []. auto.
Defined.

End msgT.

Context `{!mono_listG msgT.t Σ}.

Section chat_lib.

Definition valid_chat (γ : gname) (P : list msgT.t → iProp Σ) : iProp Σ.
Proof. Admitted.

Global Instance valid_chat_persistent γ P : Persistent (valid_chat γ P).
Proof. Admitted.

Lemma wp_init (P : list msgT.t → iProp Σ) :
  {{{ True }}}
  Init #()
  {{{
    γ,
    RET #();
    mono_list_lb_own γ [] ∗
    valid_chat γ P
  }}}.
Proof. Admitted.

Lemma wp_put γ P p m l :
  {{{
    valid_chat γ P ∗
    msgT.own p m ∗
    mono_list_lb_own γ l ∗
    (∀ l', ⌜l `prefix_of` l'⌝ -∗ □ P l' ={⊤}=∗ □ P (l' ++ [m]))
  }}}
  Put #p
  {{{
    RET #();
    msgT.own p m
  }}}.
Proof. Admitted.

Lemma wp_get γ P l :
  {{{
    valid_chat γ P ∗
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

Definition P γa γb (l : list msgT.t) : iProp Σ :=
  (⌜l = []⌝) ∨
  (⌜l = [msgT.mk 10]⌝ ∗ ghost_var γa DfracDiscarded 0) ∨
  (⌜l = [msgT.mk 10; msgT.mk 11]⌝ ∗
    ghost_var γa DfracDiscarded 0 ∗ ghost_var γb DfracDiscarded 0).

Lemma wp_alice (γa γb : gname) :
  {{{ ghost_var γa (DfracOwn 1) 0 }}}
  alice #()
  {{{ RET #(); True }}}.
Proof.
  rewrite /alice.
  iIntros (Φ) "Hγa HΦ".

  wp_apply (wp_init (P γa γb)).
  iIntros (γl) "[#Hl_lb #Hvalid]".

  wp_apply wp_allocStruct; [val_ty|].
  iIntros (a) "Ha".
  iDestruct (struct_fields_split with "Ha") as "HH".
  iNamed "HH".
  iRename "body" into "Ha".

  wp_apply wp_allocStruct; [val_ty|].
  iIntros (b) "Hb".
  iDestruct (struct_fields_split with "Hb") as "HH".
  iNamed "HH".
  iRename "body" into "Hb".

  wp_apply (wp_put with "[$Hvalid Ha $Hl_lb Hγa]").
  {
    instantiate (1:=msgT.mk _).
    rewrite /msgT.own /P /=.
    iFrame.
    iIntros (?) "%Hpref #HP".
    iDestruct "HP" as "[->|[[-> #Hro]|[-> [#Hro _]]]]".
    {
      iMod (ghost_var_persist with "Hγa") as "#Hγa".
      iIntros "!>!>".
      iRight.
      iLeft.
      iSplit; [done|].
      iAssumption.
    }
    (* TODO: `all:` or `1-2:` not working here for some reason. *)
    1: by iDestruct (ghost_var_valid_2 with "Hγa Hro") as %[? _].
    1: by iDestruct (ghost_var_valid_2 with "Hγa Hro") as %[? _].
  }
  iIntros "Ha".

  wp_apply (wp_get with "[$Hvalid $Hl_lb]").
  iIntros (??) "(Hsl_own & #Hl_lb' & %Hpref & #HP)".
  wp_apply wp_slice_len.

  wp_if_destruct.
  2: by iApply "HΦ".

  iDestruct (own_slice_sz with "Hsl_own") as "%Hsz".
  iDestruct (own_slice_to_small with "Hsl_own") as "Hsl_own".
  rewrite /P.
  iDestruct "HP" as "[->|[[-> _]|[-> _]]]".
  1: replace (length _) with (0) in Hsz; [word|auto].
  1: replace (length _) with (1) in Hsz; [word|auto].
  replace (length _) with (2) in Hsz; [|auto].

  wp_apply (wp_SliceGet with "[$Hsl_own]"); [done|].
  iIntros "Hsl_own".
  rewrite /to_val.
  rewrite /msgT.IntoVal.
  wp_loadField.
  wp_apply wp_Assert; [done|].

  wp_apply (wp_SliceGet with "[$Hsl_own]"); [done|].
  iIntros "Hsl_own".
  wp_loadField.
  wp_apply wp_Assert; [done|].

  wp_apply wp_slice_len.
  wp_apply wp_Assert.
  {
    (* TODO: should be simpler proof. *)
    assert (U64 2 = sl.(Slice.sz)) by word.
    rewrite <-H.
    done.
  }

  wp_apply (wp_get with "[$Hvalid $Hl_lb']").
  iIntros (??) "(Hsl_own' & _ & %Hpref' & #HP)".
  rewrite /P.
  iDestruct "HP" as "[->|[[-> _]|[-> _]]]".
  {
    (* TODO: should be simpler proof. *)
    exfalso.
    apply prefix_nil_inv in Hpref'.
    discriminate Hpref'.
  }
  {
    exfalso.
    apply prefix_cons_inv_2 in Hpref'.
    apply prefix_nil_inv in Hpref'.
    discriminate Hpref'.
  }

  iDestruct (own_slice_sz with "Hsl_own'") as "%Hsz'".
  replace (length _) with (2) in Hsz'; [|auto].
  iDestruct (own_slice_to_small with "Hsl_own'") as "Hsl_own'".
  wp_apply (wp_SliceGet with "[$Hsl_own']"); [done|].
  iIntros "Hsl_own'".
  wp_loadField.
  wp_apply wp_Assert; [done|].

  wp_apply (wp_SliceGet with "[$Hsl_own']"); [done|].
  iIntros "Hsl_own'".
  wp_loadField.
  wp_apply wp_Assert; [done|].

  wp_apply wp_slice_len.
  wp_apply wp_Assert.
  {
    assert (U64 2 = sl0.(Slice.sz)) by word.
    rewrite <-H.
    done.
  }

  wp_pures.
  by iApply "HΦ".
Qed.

Lemma wp_bob (γa γb : gname) :
  {{{ ghost_var γb (DfracOwn 1) 0 }}}
  bob #()
  {{{ RET #(); True }}}.
Proof.
  rewrite /bob.
  iIntros (Φ) "Hγb HΦ".

  wp_apply (wp_init (P γa γb)).
  iIntros (γl) "[#Hl_lb #Hvalid]".

  wp_apply wp_allocStruct; [val_ty|].
  iIntros (a) "Ha".
  iDestruct (struct_fields_split with "Ha") as "HH".
  iNamed "HH".
  iRename "body" into "Ha".

  wp_apply wp_allocStruct; [val_ty|].
  iIntros (b) "Hb".
  iDestruct (struct_fields_split with "Hb") as "HH".
  iNamed "HH".
  iRename "body" into "Hb".

  wp_apply (wp_get with "[$Hvalid $Hl_lb]").
  iIntros (??) "(Hsl_own & #Hl_lb' & %Hpref & #HP)".
  wp_apply wp_slice_len.

  wp_if_destruct.
  2: by iApply "HΦ".

  iDestruct (own_slice_sz with "Hsl_own") as "%Hsz".
  iDestruct (own_slice_to_small with "Hsl_own") as "Hsl_own".
  rewrite /P.
  iDestruct "HP" as "[->|[[-> _]|[-> [_ #Hro]]]]".
  1: replace (length _) with (0) in Hsz; [word|auto].
  2: by iDestruct (ghost_var_valid_2 with "Hγb Hro") as %[? _].

  wp_apply (wp_SliceGet with "[$Hsl_own]"); [done|].
  iIntros "Hsl_own".
  rewrite /to_val.
  rewrite /msgT.IntoVal.
  wp_loadField.
  wp_apply wp_Assert; [done|].

  wp_apply (wp_put with "[$Hvalid Hb $Hl_lb' Hγb]").
  {
    instantiate (1:=msgT.mk _).
    rewrite /msgT.own /P /=.
    iFrame.
    iIntros (?) "%Hpref' #HP".
    iDestruct "HP" as "[->|[[-> #Hro]|[-> [_ #Hro]]]]".
    {
      exfalso.
      apply prefix_nil_inv in Hpref'.
      discriminate Hpref'.
    }
    2: by iDestruct (ghost_var_valid_2 with "Hγb Hro") as %[? _].
    {
      iMod (ghost_var_persist with "Hγb") as "#Hγb".
      iIntros "!>!>".
      iRight.
      iRight.
      iSplit; [done|].
      iSplit; iAssumption.
    }
  }
  iIntros "_".

  wp_pures.
  by iApply "HΦ".
Qed.

End proof.
