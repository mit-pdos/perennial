From iris.base_logic.lib Require Import saved_prop ghost_map.
From New.proof Require Export proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import chan_au_base chan_au_send chan_au_recv simple.
From New.proof Require Import time sync tok_set.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.

Set Default Proof Using "Type".

Section auth_prop.

Class authPropG Σ :=
  {
    #[local] savedPred_inG :: savedPropG Σ;
    #[local] gnameSet_inG :: ghost_mapG Σ gname ();
  }.

Context `{!authPropG Σ}.

Definition own_aprop_auth γ (P : iProp Σ) (n : nat) : iProp Σ :=
  ∃ gns,
    "Hgns" ∷ ghost_map_auth γ 1 (gset_to_gmap () gns) ∗
    "Hused" ∷ ([∗ set] γprop ∈ gns, ∃ Q, saved_prop_own γprop DfracDiscarded Q) ∗
    "HimpliesP" ∷ (([∗ set] γprop ∈ gns, ∃ Q, saved_prop_own γprop DfracDiscarded Q ∗ ▷ Q) ∗-∗ ▷ P) ∗
    "%Hn" ∷ ⌜ size gns = n ⌝.
#[global] Opaque own_aprop_auth.
#[local] Transparent own_aprop_auth.

Definition own_aprop_frag γ (P : iProp Σ) (n : nat) : iProp Σ :=
  ∃ gns,
    "Hgns" ∷ ([∗ set] γprop ∈ gns, γprop ↪[γ] ()) ∗
    "HimpliesP" ∷ (([∗ set] γprop ∈ gns, ∃ Q, saved_prop_own γprop DfracDiscarded Q ∗ ▷ Q) ∗-∗ ▷ P) ∗
    "%Hn" ∷ ⌜ size gns = n ⌝.
#[global] Opaque own_aprop_frag.
#[local] Transparent own_aprop_frag.

Definition own_aprop γ (P : iProp Σ) : iProp Σ := own_aprop_frag γ P 1.
#[global] Opaque own_aprop.
#[local] Transparent own_aprop.

Lemma own_aprop_auth_alloc :
  ⊢ |==> ∃ γ, own_aprop_auth γ True 0.
Proof.
  iMod (ghost_map_alloc ∅) as (γ) "[H _]".
  iExists γ. unfold own_aprop_auth. iExists ∅.
  rewrite gset_to_gmap_empty. iFrame. rewrite !big_sepS_empty //.
  iModIntro. repeat iSplitL; try done; iIntros "_ "; done.
Qed.

Lemma own_aprop_auth_add γ P Q n :
  ⊢ own_aprop_auth γ P n ==∗ own_aprop_auth γ (P ∗ Q) (S n) ∗ own_aprop γ Q.
Proof.
  iNamed 1.
  iMod (saved_prop_alloc Q (DfracOwn 1)) as (γprop) "HQ"; first done.
  destruct (decide (γprop ∈ gns)).
  { iDestruct (big_sepS_elem_of_acc _ _ γprop with "Hused") as "[[% Hbad] _]"; first done.
    iCombine "Hbad HQ" gives "[%Hbad _]". done. }
  iMod (ghost_map_insert γprop () with "Hgns") as "[Hgns_auth Hgns']".
  { rewrite lookup_gset_to_gmap_None //. }
  rewrite -gset_to_gmap_union_singleton.
  iMod (saved_prop_persist with "HQ") as "#HQ".
  iModIntro. iSplitR "Hgns'".
  { iFrame. assert ({[γprop]} ## gns) by set_solver.
    repeat rewrite !big_sepS_union // !big_sepS_singleton. iFrame "∗#".
    subst. rewrite size_union // size_singleton /=. iSplitL; last done.
    iSplit.
    - iIntros "[HQ' HPs]". iSpecialize ("HimpliesP" with "HPs"). iFrame.
      iDestruct "HQ'" as (?) "[HQ' HQfact]". iCombine "HQ HQ'" gives "[_ H]".
      iNext. iRewrite "H". iFrame.
    - iIntros "[HPfact HQfact]". iSplitR "HPfact HimpliesP".
      + iExists _; iFrame "#∗".
      + by iApply "HimpliesP".
  }
  iExists {[ _ ]}. rewrite !big_sepS_singleton. iFrame. rewrite size_singleton.
  iSplitL; last done. iSplit.
  - iIntros "(% & HQ' & HQfact)". iCombine "HQ HQ'" gives "[_ Heq]".
    iNext. iRewrite "Heq". iFrame.
  - iIntros "?". iFrame "#∗".
Qed.

Lemma own_aprop_auth_agree γ P P' n :
  ⊢ own_aprop_auth γ P n -∗ own_aprop_frag γ P' n -∗ (▷ P ∗-∗ ▷ P').
Proof.
  iNamed 1. iNamedSuffix 1 "'".
  iDestruct (ghost_map_lookup_big with "Hgns [Hgns']") as "%Hsub".
  { instantiate (1:=gset_to_gmap () gns0). rewrite big_sepM_gset_to_gmap. iFrame. }
  apply subseteq_dom in Hsub. rewrite !dom_gset_to_gmap in Hsub.
  apply set_subseteq_size_eq in Hsub as Heq; last lia. subst. clear Hn' Hsub.
  iSplit.
  - iIntros "HP". iApply "HimpliesP" in "HP". iApply "HimpliesP'" in "HP". iFrame.
  - iIntros "HP'". iApply "HimpliesP'" in "HP'". iApply "HimpliesP" in "HP'". iFrame.
Qed.

Lemma own_aprop_frag_combine γ P P' n n' :
  ⊢ own_aprop_frag γ P n -∗ own_aprop_frag γ P' n' -∗ own_aprop_frag γ (P ∗ P') (n + n').
Proof.
  iNamed 1. iNamedSuffix 1 "'". rename gns0 into gns'.
  destruct (decide (gns ∩ gns' = ∅)) as [Hdisj|Hbad].
  2:{
    apply set_choose_L in Hbad. destruct Hbad as [γprop Hbad].
    iDestruct (big_sepS_elem_of_acc _ _ γprop with "Hgns") as "[H1 _]";
      first set_solver.
    iDestruct (big_sepS_elem_of_acc _ _ γprop with "Hgns'") as "[H2 _]";
      first set_solver.
    iCombine "H1 H2" gives %[Hbad' _]. done.
  }
  apply disjoint_intersection_L in Hdisj.
  iExists (gns ∪ gns'). rewrite big_sepS_union //. iFrame.
  rewrite big_sepS_union //. rewrite size_union //.
  iSplitL; last word. iSplit.
  - iIntros "[H H']". iApply "HimpliesP" in "H". iApply "HimpliesP'" in "H'". iFrame.
  - iIntros "[H H']". iApply "HimpliesP" in "H". iApply "HimpliesP'" in "H'". iFrame.
Qed.

End auth_prop.

Section waitgroup_idiom.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!syncG Σ}.

Record WaitGroup_join_names :=
  {
    wg : WaitGroup_names;
    wg_added : gname;
  }.

Implicit Types γ : WaitGroup_join_names.

Print auth_set_auth.
AuthProp :

  P : iProp
  n, k : nat

 own_auth P n
 own_frag P k

 own_frag P k ∗ own_frag P' k' -∗ own_frag (P ∗ P') (k + k')

 own_auth P n ∗ own_frag P' n -∗ ▷(P ≡ P')
 own_auth P n ∗ own_frag P' n -∗ own_auth P'' 0

Definition wg_inv γ : iProp Σ :=
  inv nroot (
      ∃ ctr added done,
        "Hwg_ctr" ∷ own_WaitGroup γ.(wg) ctr ∗
        "Hadded" ∷ own_tok_auth_dfrac γ.(wg_added) (DfracOwn (1/2)) added ∗
        "Hdone" ∷ own_tok_auth_dfrac γ.(wg_added) (DfracOwn (1/2)) done ∗
        "" ∷ ⌜ uint.nat ctr = added + done ⌝
    )
.

(** Permission to call `Add`. Calling `Add` will extend `A` with a caller-chosen
    proposition, as long as `num_added` doesn't overflow. *)
Definition own_Adder γ (num_added : w32) (P : iProp Σ) : iProp Σ :=
  "Hno_waiters" ∷ own_WaitGroup_waiters γ.(wg) (W32 0)
.

(** Permission to call `Wait`, knowing that `P` will be true afterwards. *)
Definition own_Waiter γ (P : iProp Σ) : iProp Σ :=
  "Hwaiters" ∷ own_WaitGroup_waiters γ.(wg) (W32 1)
.

(** Permission to call `Done` as long as `P` is passed in. *)
Definition own_Done γ (P : iProp Σ) : iProp Σ :=
  True
.


End waitgroup_idiom.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!syncG Σ}.
Context `{!chanGhostStateG Σ slice.t}.

#[global] Instance : IsPkgInit strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf strings := build_get_is_pkg_init_wf.
#[global] Instance : IsPkgInit chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf chan_spec_raw_examples := build_get_is_pkg_init_wf.

Record SearchReplace_names :=
  {
    wg: WaitGroup_names;
    wg_added : gname;
  }.

Implicit Types γ : SearchReplace_names.

Definition search_replace (x y: w64) : list w64 → list w64 :=
  fmap (λ a, if decide (a = x) then y else a).

Definition wg_inv γ : iProp Σ :=
  inv nroot (
      ∃ ctr added done,
        "Hwg_ctr" ∷ own_WaitGroup γ.(wg) ctr ∗
        "Hadded" ∷ own_tok_auth_dfrac γ.(wg_added) (DfracOwn (1/2)) added ∗
        "Hdone" ∷ own_tok_auth_dfrac γ.(wg_added) (DfracOwn (1/2)) done ∗
        "" ∷ ⌜ uint.nat ctr = added + done ⌝
    )
.

(* SearchReplace will own own_WaitGroup_waiters.
   Invariant for counter will say
 *)
Definition chanP (x y: w64) (s: slice.t) : iProp Σ :=
  (* TODO: somehow this slice needs to be exactly the data in some subslice of
  the original list; does that need to be connected with a ghost variable? *)
  ∃ (xs: list w64),
    "Hxs" ∷ s ↦* xs ∗
    "Hwg_done" ∷ (s ↦* (search_replace x y xs) ={⊤}=∗ own_wg_done_tok)
.
  (* TODO: need permission to send back ownership of s ↦* search_replace x y
  xs on the waitgroup *)
.


Allocate
(s ↦* (search_replace x y xs) ={⊤}=∗ own_wg_done_tok)
(own_wg_done_tok ={⊤}=∗ s ↦* (search_replace x y xs))
when calling Add.

Definition waitgroupN := nroot .@ "waitgroup".

Lemma wp_worker (γs: simple_names) (γwg: WaitGroup_names) (ch: loc) (wg: loc) (x y: w64) :
  {{{ is_pkg_init chan_spec_raw_examples ∗
        "#Hchan" ∷ is_simple γs ch 4 (chanP x y) ∗
        "Hwg" ∷ is_WaitGroup wg γwg waitgroupN }}}
    @! chan_spec_raw_examples.worker #ch #wg #x #y
  {{{ RET #(); True }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  wp_apply (wp_simple_receive with "[$Hchan]").
  iIntros (s) "Hrcv".
  iDestruct "Hrcv" as (xs) "Hs".
  wp_auto.
  wp_for.
  (* TODO: prove inner loop does search-replace for s *)
Admitted.

Lemma wp_SearchReplace (s: slice.t) (xs: list w64) (x y: w64) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ s ↦* xs }}}
    @! chan_spec_raw_examples.SearchReplace #s #x #y
  {{{ RET #(); s ↦* (search_replace x y xs) }}}.
Proof.
  wp_start as "Hs".
  wp_auto.
  iDestruct (own_slice_len with "Hs") as %Hlen.
  wp_if_destruct.
  {
    assert (length xs = 0%nat) by word.
    destruct xs; simpl in *; [ | congruence ].
    iApply "HΦ".
    iFrame.
  }
  wp_apply wp_NewChannel.
  { done. }
  iIntros (ch γch_names) "[#His_chan Hoc]".
  change (4 =? 0) with false; simpl.
  iMod (start_simple_buffered _ _ _ (chanP x y) with "[$His_chan] [$Hoc]") as (γch) "#Hchan".
  wp_auto.
Admitted.

End proof.
