From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_logic Require Import atomic. (* prefer the ncfupd atomics *)
From Goose.github_com.mit_pdos.rsm Require Import mpaxos.

(* TODO: move to mpaxos_ghost.v once stable *)
Class mpaxos_ghostG (Σ : gFunctors).

Record mpaxos_names := {}.

Section consensus.
  Context `{!mpaxos_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : mpaxos_names).

  (* Definitions. *)
  Definition own_consensus γ (l : list string) : iProp Σ.
  Admitted.

  Definition own_consensus_half γ (l : list string) : iProp Σ.
  Admitted.

  Definition is_consensus_lb γ (l : list string) : iProp Σ.
  Admitted.

  Definition own_candidates γ (vs : gset string) : iProp Σ.
  Admitted.

  Definition own_candidates_half γ (vs : gset string) : iProp Σ.
  Admitted.

  (* Type class instances. *)
  #[global]
  Instance is_consensus_lb_persistent γ l :
    Persistent (is_consensus_lb γ l).
  Admitted.

  (* Rules. *)
  Lemma consensus_update {γ} l1 l2 vs :
    Forall (λ x, x ∈ vs) l2 ->
    prefix l1 l2 ->
    own_consensus γ l1 -∗
    own_candidates_half γ vs ==∗
    own_consensus γ l2 ∗ own_candidates_half γ vs.
  Admitted.

  Lemma consensus_witness {γ l} :
    own_consensus_half γ l -∗
    is_consensus_lb γ l.
  Admitted.

  Lemma consensus_combine {γ l1 l2} :
    own_consensus_half γ l1 -∗
    own_consensus_half γ l2 -∗
    own_consensus γ l1 ∧ ⌜l1 = l2⌝.
  Admitted.

  Lemma consensus_split {γ l} :
    own_consensus γ l -∗
    own_consensus_half γ l ∗ own_consensus_half γ l.
  Admitted.

  Lemma consensus_prefix {γ l1 l2} :
    own_consensus_half γ l1 -∗
    is_consensus_lb γ l2 -∗
    ⌜prefix l2 l1⌝.
  Admitted.

  Lemma consensus_lb_prefix {γ l1 l2} :
    is_consensus_lb γ l1 -∗
    is_consensus_lb γ l2 -∗
    ⌜prefix l1 l2 ∨ prefix l2 l1⌝.
  Admitted.

  Lemma candidates_update {γ vs1} vs2 :
    vs1 ⊆ vs2 ->
    own_candidates γ vs1 ==∗
    own_candidates γ vs2.
  Admitted.

  Lemma candidates_combine {γ vs1 vs2} :
    own_candidates_half γ vs1 -∗
    own_candidates_half γ vs2 -∗
    own_candidates γ vs1 ∧ ⌜vs1 = vs2⌝.
  Admitted.

  Lemma candidates_split {γ vs} :
    own_candidates γ vs -∗
    own_candidates_half γ vs ∗ own_candidates_half γ vs.
  Admitted.

  Lemma consensus_incl {γ l vs} :
    own_consensus_half γ l -∗
    own_candidates_half γ vs -∗
    ⌜Forall (λ x, x ∈ vs) l⌝.
  Admitted.
End consensus.
(* TODO: move to mpaxos_ghost.v once stable *)

(* TODO: move to mpaxos_propose/lookup.v once stable *)
Section prog.
  Context `{!heapGS Σ, !mpaxos_ghostG Σ}.

  Definition mpaxosN := nroot .@ "mpaxos".

  Definition is_paxos (paxos : loc) (nid : u64) (sc : nat) (γ : mpaxos_names) : iProp Σ.
  Admitted.

  (* TODO: remove this once is_paxos defined. *)
  #[global]
  Instance is_paxos_persistent px nid sc γ :
    Persistent (is_paxos px nid sc γ).
  Admitted.

  Theorem wp_Paxos__Propose (px : loc) (v : string) nid sc γ :
  is_paxos px nid sc γ -∗
  {{{ True }}}
  <<< ∀∀ vs, own_candidates_half γ vs >>>
    Paxos__Propose #px #(LitString v) @ ↑mpaxosN
  <<< own_candidates_half γ ({[v]} ∪ vs) >>>
  {{{ (lsn : u64) (term : u64), RET (#lsn, #term); True }}}.
  Admitted.

  Theorem wp_Paxos__Lookup (px : loc) (i : u64) nid sc γ :
    is_paxos px nid sc γ -∗
    {{{ True }}}
    <<< ∀∀ l, own_consensus_half γ l >>>
      Paxos__Lookup #px #i @ ↑mpaxosN
    <<< ∃∃ l', own_consensus_half γ l' >>>
    {{{ (v : string) (ok : bool), RET (#(LitString v), #ok);
        ⌜if ok then l' !! (uint.nat i) = Some v else True⌝
    }}}.
  Admitted.

  Definition paxos_init px γ : iProp Σ :=
  "Hvs"  ∷ own_candidates_half γ ∅ ∗
  "Hv"   ∷ own_consensus_half γ [] ∗
  "#Hpx" ∷ is_paxos px (W64 0) 3%nat γ.

  Theorem wp_MkPaxos :
    {{{ True }}}
      MkPaxos #()
      {{{ (γ : mpaxos_names) (px : loc), RET #px; paxos_init px γ }}}.
  Proof.
    (*@ func MkPaxos() *Paxos {                                                 @*)
    (*@     var px *Paxos                                                       @*)
    (*@                                                                         @*)
    (*@     return px                                                           @*)
    (*@ }                                                                       @*)
  Admitted.

End prog.
(* TODO: move to mpaxos_propose/lookup.v once stable *)

(* TODO: move to mpaxos_examples.v once stable *)

(* example1 *)
Definition of_length_five s := String.length s = 5%nat.

Definition length_of_consensus l :=
  Forall of_length_five l.

Definition length_of_candidates (vs : gset string) :=
  set_Forall of_length_five vs.

Lemma prefix_lookup_same_index {A : Type} {l1 l2 : list A} {i v1 v2} :
  prefix l1 l2 ∨ prefix l2 l1 ->
  l1 !! i = Some v1 ->
  l2 !! i = Some v2 ->
  v1 = v2.
Admitted.

Section prog.
  Context `{!heapGS Σ, !mpaxos_ghostG Σ}.

  Definition inv_example1 γ : iProp Σ :=
    ∃ l vs,
      "Hl"  ∷ own_consensus_half γ l ∗
      "Hvs" ∷ own_candidates_half γ vs ∗
      "%Hlenl"  ∷ ⌜length_of_consensus l⌝ ∗
      "%Hlenvs" ∷ ⌜length_of_candidates vs⌝.

  #[global]
  Instance inv_example1_timeless γ :
    Timeless (inv_example1 γ).
  Admitted.

  Definition example1N := nroot .@ "example1N".
  Definition know_inv_example1 γ : iProp Σ :=
    inv example1N (inv_example1 γ).

  Theorem wp_example1 :
    {{{ True }}}
      example1 #()
    {{{ RET #(); True }}}.
  Proof using heapGS0 mpaxos_ghostG0 Σ.
    iIntros (Φ) "_ HΦ".
    wp_call.

    (*@ func example1() {                                                       @*)
    (*@     px := MkPaxos()                                                     @*)
    (*@                                                                         @*)
    wp_apply wp_MkPaxos.
    iIntros (γ px) "Hinit".
    iNamed "Hinit".
    wp_pures.
    iMod (inv_alloc example1N _ (inv_example1 γ) with "[Hv Hvs]") as "#Hinvapp".
    { do 2 iExists _. iFrame. unfold length_of_consensus. set_solver. }

    (*@     i1, _ := px.Propose("hello")                                        @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__Propose with "Hpx").
    iInv "Hinvapp" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iExists vs. iFrame.
    iIntros "Hvs".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Hl Hvs]") as "_".
    { do 2 iExists _. iFrame.
      iPureIntro. split; first done.
      unfold length_of_candidates.
      apply set_Forall_union; last done.
      by rewrite set_Forall_singleton.
    }
    iIntros "!>" (lsn term) "_".
    wp_pures.
    clear Hlenl Hlenvs l vs.

    (*@     px.Propose("world")                                                 @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__Propose with "Hpx").
    iInv "Hinvapp" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iExists vs. iFrame.
    iIntros "Hvs".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Hl Hvs]") as "_".
    { do 2 iExists _. iFrame.
      iPureIntro. split; first done.
      unfold length_of_candidates.
      apply set_Forall_union; last done.
      by rewrite set_Forall_singleton.
    }
    iIntros "!>" (lsn' term') "_".
    wp_pures.
    clear Hlenl Hlenvs l vs lsn' term'.

    (*@     // Notice in the proof how we transfer the invariant from the candidate set @*)
    (*@     // to the consensus.                                                @*)
    (*@     v1, ok1 := px.Lookup(i1)                                            @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__Lookup with "Hpx").
    iInv "Hinvapp" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iExists l. iFrame.
    iIntros (l1) "Hl1".
    iDestruct (consensus_witness with "Hl1") as "#Hlb1".
    iMod "Hmask" as "_".
    iDestruct (consensus_incl with "Hl1 Hvs") as %Hin1.
    iMod ("HinvC" with "[Hl1 Hvs]") as "_".
    { do 2 iExists _. iFrame.
      iPureIntro. split; last done.
      unfold length_of_consensus.
      unfold length_of_candidates in Hlenvs.
      rewrite Forall_forall.
      intros x Hx.
      rewrite Forall_forall in Hin1.
      specialize (Hin1 _ Hx).
      by specialize (Hlenvs _ Hin1).
    }
    iIntros "!>" (v1 ok1 Hv1).
    assert (Hlenv1 : if ok1 then of_length_five v1 else True).
    { destruct ok1; last done.
      apply elem_of_list_lookup_2 in Hv1.
      rewrite Forall_forall in Hin1.
      specialize (Hin1 _ Hv1).
      by specialize (Hlenvs _ Hin1).
    }
    wp_pures.
    clear Hin1 Hlenl Hlenvs l vs.

    (*@     v2, ok2 := px.Lookup(i1)                                            @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__Lookup with "Hpx").
    iInv "Hinvapp" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iExists l. iFrame.
    iIntros (l2) "Hl2".
    iDestruct (consensus_witness with "Hl2") as "#Hlb2".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Hl2 Hvs]") as "_".
    { iDestruct (consensus_incl with "Hl2 Hvs") as %Hin.
      do 2 iExists _. iFrame.
      iPureIntro. split; last done.
      unfold length_of_consensus.
      unfold length_of_candidates in Hlenvs.
      rewrite Forall_forall.
      intros x Hx.
      rewrite Forall_forall in Hin.
      specialize (Hin _ Hx).
      by specialize (Hlenvs _ Hin).
    }
    iIntros "!>" (v2 ok2 Hv2).
    wp_pures.
    clear Hlenl Hlenvs l vs.

    (*@     if ok1 && ok2 {                                                     @*)
    (*@         machine.Assert(v1 == v2)                                        @*)
    (*@         machine.Assert(len(v1) == 5)                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_and_pure (ok1 = true) (ok2 = true)).
    { wp_pures. iPureIntro.
      case_bool_decide as H; first by rewrite H.
      rewrite not_true_iff_false in H. by rewrite H.
    }
    { iIntros (_). wp_pures. iPureIntro.
      case_bool_decide as H; first by rewrite H.
      rewrite not_true_iff_false in H. by rewrite H.
    }
    wp_if_destruct; last by iApply "HΦ".
    destruct Heqb as [Hok1 Hok2]. subst ok1 ok2.
    iDestruct (consensus_lb_prefix with "Hlb1 Hlb2") as %Hprefix.
    rewrite -(prefix_lookup_same_index Hprefix Hv1 Hv2).
    wp_apply wp_Assert; first by rewrite bool_decide_eq_true.
    wp_pures.
    wp_apply wp_Assert; first by rewrite Hlenv1.
    wp_pures.
    by iApply "HΦ".
  Qed.

End prog.

(* example2 *)
Fixpoint hello_then_world (l : list string) :=
  match l with
  | [] => True
  | hd :: tl => if decide (hd = "hello")
              then True
              else if decide (hd = "world")
                   then False
                   else hello_then_world tl
  end.

Lemma htw_no_world l :
  "world" ∉ l ->
  hello_then_world l.
Proof.
  intros Hnotin.
  induction l as [| hd tl]; first done.
  simpl.
  case_decide; first done.
  case_decide; first set_solver.
  apply IHtl. set_solver.
Qed.

Theorem htw_inv_app_no_world l1 l2 :
  "world" ∉ l2 ->
  hello_then_world l1 ->
  hello_then_world (l1 ++ l2).
Proof.
  intros Hnotin Hhtw.
  induction l1 as [| hd tl].
  { simpl. by apply htw_no_world. }
  rewrite -app_comm_cons. simpl.
  simpl in Hhtw.
  case_decide; first done.
  case_decide; first done.
  by apply IHtl.
Qed.

Theorem htw_inv_snoc l1 l2 :
  "hello" ∈ l1 ->
  hello_then_world l1 ->
  hello_then_world (l1 ++ l2).
Proof.
  intros Hin Hhtw.
  induction l1 as [| hd tl]; first set_solver.
  rewrite -app_comm_cons. simpl.
  simpl in Hhtw.
  case_decide; first done.
  case_decide; first done.
  apply IHtl; [set_solver | done].
Qed.

Definition contain_hello (l : list string) (vs : gset string) :=
  "world" ∈ vs -> "hello" ∈ l.

Section prog.
  Context `{!heapGS Σ, !mpaxos_ghostG Σ}.

  Definition inv_example2 γ : iProp Σ :=
    ∃ l vs,
      "Hl"  ∷ own_consensus_half γ l ∗
      "Hvs" ∷ own_candidates_half γ vs ∗
      "%Hhtw" ∷ ⌜hello_then_world l⌝ ∗
      "%Hch"  ∷ ⌜contain_hello l vs⌝.

  #[global]
  Instance inv_example2_timeless γ :
    Timeless (inv_example2 γ).
  Admitted.

  Definition example2N := nroot .@ "example2N".
  Definition know_inv_example2 γ : iProp Σ :=
    inv example2N (inv_example2 γ).

  Theorem wp_example2 :
  {{{ True }}}
    example2 #()
  {{{ RET #(); True }}}.
  Proof using heapGS0 mpaxos_ghostG0 Σ.
    iIntros (Φ) "_ HΦ".
    wp_call.

    (*@ func example2() {                                                       @*)
    (*@     px := MkPaxos()                                                     @*)
    (*@                                                                         @*)
    wp_apply wp_MkPaxos.
    iIntros (γ px) "Hinit".
    iNamed "Hinit".
    wp_pures.
    iMod (inv_alloc example1N _ (inv_example2 γ) with "[Hv Hvs]") as "#Hinvapp".
    { do 2 iExists _. iFrame. set_solver. }

    (*@     i, _ := px.Propose("hello")                                         @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__Propose with "Hpx").
    iInv "Hinvapp" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iExists vs. iFrame.
    iIntros "Hvs".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Hl Hvs]") as "_".
    { do 2 iExists _. iFrame.
      iPureIntro. split; first done.
      unfold contain_hello. intros Hworld. apply Hch.
      set_solver.
    }
    iIntros "!>" (lsn term) "_".
    wp_pures.
    clear Hhtw Hch l vs.

    (*@     v, ok := px.Lookup(i)                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__Lookup with "Hpx").
    iInv "Hinvapp" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iDestruct (consensus_witness with "Hl") as "#Hlb".
    iExists l. iFrame.
    iIntros (l') "Hl'".
    iDestruct (consensus_prefix with "Hl' Hlb") as %Hprefix.
    iClear "Hlb".
    iDestruct (consensus_witness with "Hl'") as "#Hlb".
    iMod "Hmask" as "_".
    iDestruct (consensus_incl with "Hl' Hvs") as %Hin.
    iMod ("HinvC" with "[Hl' Hvs]") as "_".
    { do 2 iExists _. iFrame.
      iPureIntro. split; last first.
      { unfold contain_hello.
        intros Hvs.
        specialize (Hch Hvs).
        by apply (elem_of_prefix l).
      }
      destruct Hprefix as [k Hprefix]. subst l'.
      destruct (decide ("world" ∈ k)) as [Hk | Hk].
      { apply htw_inv_snoc; last done.
        apply Hch.
        rewrite Forall_forall in Hin.
        apply Hin.
        set_solver.
      }
      { by apply htw_inv_app_no_world. }
    }
    iIntros "!>" (v ok Hlsn).
    wp_pures.
    clear Hhtw Hch Hin Hprefix l vs.

    (*@     if ok && v == "hello" {                                             @*)
    (*@         px.Propose("world")                                             @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_and_pure (ok = true) (v = "hello")).
    { wp_pures. iPureIntro.
      case_bool_decide as H; first by rewrite H.
      rewrite not_true_iff_false in H. by rewrite H.
    }
    { iIntros "_". wp_pures. iPureIntro.
      case_bool_decide as Ev.
      - by inversion Ev.
      - by case_bool_decide as Ev'; first subst v.
    }
    wp_if_destruct.
    { destruct Heqb as [Hok Hv]. subst ok. subst v.
      wp_apply (wp_Paxos__Propose with "Hpx").
      iInv "Hinvapp" as "> HinvO" "HinvC".
      iNamed "HinvO".
      iApply ncfupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iExists vs. iFrame.
      iIntros "Hvs".
      iDestruct (consensus_prefix with "Hl Hlb") as %Hprefix.
      iMod "Hmask" as "_".
      iMod ("HinvC" with "[Hl Hvs]") as "_".
      { do 2 iExists _. iFrame.
        iPureIntro. split; first done.
        unfold contain_hello. intros _.
        by apply (elem_of_prefix l'); first eapply elem_of_list_lookup_2.
      }
      iIntros "!>" (lsn' term') "_".
      wp_pures.
      by iApply "HΦ".
    }
    by iApply "HΦ".
  Qed.

End prog.

(* TODO: move to mpaxos_examples.v once stable *)
