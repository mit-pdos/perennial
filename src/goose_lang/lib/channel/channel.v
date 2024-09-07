From iris.proofmode Require Import coq_tactics reduction.
From Perennial.goose_lang Require Import notation proofmode.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Import wp_store.
(* From Perennial.goose_lang.lib Require Import control. *)
From Perennial.goose_lang.lib Require Export channel.impl.
From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode.
From Perennial.program_proof Require Import proof_prelude.
Import uPred.


Set Default Proof Using "Type".

Section heap.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types z : Z.
Implicit Types t : ty.
Implicit Types stk : stuckness.
Implicit Types off : nat.

Fixpoint chan_contents (zero: val) (l : list val): val :=
    match l with
    | nil => InjLV zero
    | cons x l' => InjRV (x, (chan_contents zero l'))
    end.

Definition peek (zero: val) (l : list val): val :=
    match l with
    | nil => zero
    | cons x l' => x
    end.

Definition valid_return (closed : bool) (l : list val): bool :=
    orb closed
    (match l with
    | nil => false
    | cons x l' => true
    end).

Definition tail (l : list val): list val :=
    match l with
    | nil => l
    | cons x l' => l'
    end.

Definition own_chan chanref (cap: Z) (eff_cap: Z) (closed: bool) ty (l: list val): iProp Σ :=
    (if closed then 
      "Hchanref" ∷ chanref ↦ ChannelClosedV (zero_val ty) ∗ 
      "%Hempty" ∷ ⌜l = nil⌝
    else chanref ↦ ChannelOpenV #cap #eff_cap (chan_contents (zero_val ty) l)
    )%I.
    (* ([∗ list] _ ↦ elem ∈ l, P elem). *)

Definition is_channel_alloc chanref lk closed ty (P : val -> iProp Σ): iProp Σ :=
  is_lock nroot lk (∃ cap eff_cap l, own_chan chanref cap eff_cap closed ty l ∗
        ([∗ list] _ ↦ elem ∈ l, P elem)).

Definition is_channel c closed ty (P : val -> iProp Σ): iProp Σ :=
  ⌜c = InjLV #()⌝ ∨ (∃ chanref lk, is_channel_alloc chanref lk closed ty P ∗ ⌜c = InjRV (#chanref, lk)⌝).

Theorem wp_NewChan E t (cap : Z) P:
  {{{ True }}}
    NewChan t #(cap) @ E
  {{{ c chanref lk, RET (c);
    is_channel_alloc chanref lk false t P ∗
    ⌜c = InjRV (#chanref, lk)⌝}}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec.
  wp_apply wp_alloc_untyped.
  { eauto. }
  iIntros (chanref) "Hc".
  wp_pures.
  wp_apply (wp_newMutex with "[Hc]").
  2: { 
    iIntros (lk) "Hlk".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    unfold is_channel_alloc.
    iFrame.
    eauto.
  }
  iExists cap, _, nil.
  unfold own_chan.
  iModIntro.
  unfold chan_contents.
  iFrame.
  eauto.
Qed.

Theorem wp_IncCap chanref cap (eff_cap: Z) closed ty l:
    {{{ own_chan chanref cap eff_cap closed ty l}}}
        IncCap #chanref
    {{{ RET #(); own_chan chanref cap (uint.Z (word.add 1 eff_cap)) closed ty l}}}.
Proof.
    iIntros (Φ) "HPre HΦ".
    wp_rec.
    destruct closed.
    - iNamed "HPre". 
      wp_untyped_load.
      wp_pures.
      iApply "HΦ".
      iModIntro.
      iFrame.
      done.
    - wp_untyped_load.
      wp_pures.
      wp_untyped_store.
      iApply "HΦ".
      iModIntro.
      unfold own_chan.
      rewrite u64_Z.
      iFrame.
Qed.


Theorem wp_DecCap chanref cap (eff_cap: Z) closed ty l:
    {{{ own_chan chanref cap eff_cap closed ty l}}}
        DecCap #chanref
    {{{ RET #(); own_chan chanref cap (uint.Z (word.sub eff_cap 1)) closed ty l}}}.
Proof.
    iIntros (Φ) "HPre HΦ".
    wp_rec.
    destruct closed.
    - iNamed "HPre".
      wp_untyped_load.
      wp_pures.
      iApply "HΦ".
      iModIntro.
      iFrame.
      done.
    - wp_untyped_load.
      wp_pures.
      wp_untyped_store.
      iApply "HΦ".
      iModIntro.
      unfold own_chan.
      rewrite u64_Z.
      iFrame.
Qed.

Theorem wp_InnerReceive chanref cap eff_cap closed ty l:
    {{{ own_chan chanref cap eff_cap closed ty l}}}
        InnerReceive #chanref
    {{{RET ((peek (zero_val ty) l, #(negb closed), #(valid_return closed l))); own_chan chanref cap eff_cap closed ty (tail l)}}}.
Proof.
    iIntros (Φ) "HPre HΦ".
    wp_rec.
    destruct closed.
    - iNamed "HPre".
      wp_untyped_load.
      wp_pures.
      subst.
      simpl.
      iApply "HΦ".
      iModIntro.
      iFrame.
      done.
    - wp_untyped_load.
      wp_pures.
      destruct l.
      + simpl.
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iFrame.
      + simpl.
        wp_pures.
        wp_untyped_store.
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iFrame.
Qed.

Lemma closed_nil chanref cap eff_cap ty l :
  own_chan chanref cap eff_cap true ty l -∗ ⌜l = nil⌝.
Proof.
  iIntros "HPre".
  unfold own_chan.
  iNamed "HPre".
  done.
Qed.

Theorem wp_TryReceive (chanref : loc) lk closed ty P:
    {{{ is_channel_alloc chanref lk closed ty P}}}
        TryReceive (InjRV(#chanref, lk))
    {{{(a : val) (open : bool) (valid : bool),
        RET ((a, #(open), #(valid))); if (andb valid open) then P a else ⌜a = zero_val ty⌝}}}.
Proof.
  iIntros (Φ) "HPre HΦ".
  wp_rec.
  wp_pures.
  iDestruct "HPre" as "#Hlock".
  wp_apply wp_Mutex__Lock.
  - iFrame "Hlock".
  - iIntros "[H0 H1]".
    wp_pures.
    iNamed "H1".
    destruct closed.
    + iDestruct "H1" as "[H1 H2]".
      iNamed "H1".
      wp_untyped_load.
      wp_pures.
      wp_apply (wp_InnerReceive _ _ _ true _ _ with "[Hchanref]").
      * unfold own_chan.
        iFrame.
        iPureIntro.
        reflexivity.
      * iIntros "H3".
        wp_pures.
        wp_apply (wp_Mutex__Unlock with "[H0 H2 H3]").
        { unfold is_channel_alloc. iFrame "Hlock". iFrame. iNext. iExists _, _, l. iFrame. simpl. iNamed "H3". iFrame. done. }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        done.
    + iDestruct "H1" as "[H1 H2]".
      iNamed "H1".
      wp_untyped_load.
      wp_pures.
      wp_apply (wp_IncCap chanref cap eff_cap _ ty l with "H1").
      iIntros "H1".
      wp_pures.
      wp_apply (wp_Mutex__Unlock with "[H0 H2 H1]").
      { unfold is_channel_alloc. iFrame "Hlock". iFrame. iNext. iExists cap, _, l. iFrame. }
      wp_pures.
      wp_apply wp_Mutex__Lock.
      { unfold is_channel_alloc. iFrame "Hlock". }
      iIntros "[H0 H1]".
      wp_pures.
      iNamed "H1".
      iDestruct "H1" as "[H1 H2]".
      wp_apply (wp_InnerReceive _ _ _ _ _ _ with "[H1]").
      { iFrame. }
      iIntros "H1".
      wp_pures.
      wp_apply (wp_DecCap chanref _ _ _ ty _ with "[H1]").
      { iFrame. }
      iIntros "H1".
      wp_pures.
      destruct l0.
      * wp_apply (wp_Mutex__Unlock with "[H0 H2 H1]").
        { unfold is_channel_alloc. 
          iFrame "Hlock".
          iFrame.
          iNext.
          iExists _, _, _.
          iFrame.
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        done.
      * simpl.
        iDestruct "H2" as "[H2 H3]".
        wp_apply (wp_Mutex__Unlock with "[H0 H3 H1]").
        { unfold is_channel_alloc. 
          iFrame "Hlock".
          iFrame.
          iNext.
          iExists _, _, _.
          iFrame.
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iFrame.
        Unshelve.
        all: exact 0.
Qed.

Theorem wp_ChannelReceive (chanref : loc) lk closed ty P:
    {{{ is_channel_alloc chanref lk closed ty P}}}
      ChannelReceive (InjRV(#chanref, lk))
    {{{(a : val) (open : bool),
      RET ((a, #(open))); if (open) then P a else ⌜a = zero_val ty⌝}}}.
Proof.
  iIntros (Φ) "#HPre HΦ".
  wp_rec.
  wp_pures.
  iLöb as "IH" forall (Φ).
  wp_apply (wp_TryReceive with "[HPre]").
  - eauto.
  - iIntros (a open valid) "Ha".
    wp_pures.
    destruct valid.
    + wp_pures.
      iModIntro.
      iApply "HΦ".
      done.
    + wp_pures.
      wp_apply ("IH" with "[Ha HΦ]").
      iApply "HΦ".
Qed.

Lemma wp_ChanLen' ty (l : list val):
    {{{ True }}}
        ChanLen' (chan_contents (zero_val ty) l)
    {{{(len : Z), RET (#(len)); ⌜len = length l⌝}}}.
Proof.
  iIntros (Φ) "HPre HΦ".
  wp_rec.
  wp_pures.
  iInduction l as [|] "IH" forall (Φ).
  - wp_pures.
    iModIntro.
    iApply "HΦ".
    done.
  - wp_pures.
    wp_apply "IH".
    iIntros (len) "%Hlen".
    subst.
    wp_pures.
    iModIntro.
    rewrite -word.ring_morph_add.
    iApply "HΦ".
    iPureIntro.
    simpl.
    lia.
Qed.

Lemma wp_ChanLen (chanref : loc) closed lk ty P:
    {{{ is_channel_alloc chanref lk closed ty P}}}
        ChanLen (#chanref, lk)%V
    {{{(len : Z) (success : bool), RET (#(len), #(success)); True}}}.
Proof.
  iIntros (Φ) "HPre HΦ".
  wp_pures.
  wp_rec.
  wp_pures.
  iDestruct "HPre" as "#Hlock".
  wp_apply wp_Mutex__Lock.
  - iFrame "Hlock".
  - iIntros "[H0 H1]".
    wp_pures.
    iNamed "H1".
    iDestruct "H1" as "[H1 H2]".
    destruct closed.
    + unfold own_chan.
      iDestruct "H1" as "[H1 H3]".
      wp_untyped_load.
      wp_pures.
      wp_apply (wp_Mutex__Unlock with "[Hlock H0 H1 H3 H2]").
      * iFrame "Hlock".
        iFrame.
        iNext.
        iExists _, _, l.
        iFrame.
      * wp_pures.
        iModIntro.
        iApply "HΦ".
        done.
    + unfold own_chan.
      wp_untyped_load.
      wp_pures.
      wp_apply wp_ChanLen'.
      iIntros (len) "Hlen".
      wp_pures.
      wp_apply (wp_Mutex__Unlock with "[Hlock H0 H1 H2]").
      { iFrame "Hlock".
        iFrame.
        iNext.
        iExists cap, eff_cap, l.
        iFrame. 
      }
      wp_pures.
      iModIntro.
      iApply "HΦ".
      done.
      Unshelve.
      { eauto. }
      eauto.
Qed.

Lemma wp_ChanAppend ty (l : list val) v:
    {{{ True }}}
        ChanAppend (chan_contents (zero_val ty) l) v
    {{{RET (chan_contents (zero_val ty) (l ++ [v])); True}}}.
Proof.
  iIntros (Φ) "HPre HΦ".
  wp_rec.
  wp_pures.
  iInduction l as [|] "IH" forall (Φ).
  - wp_pures.
    iModIntro.
    iApply "HΦ".
    done.
  - wp_pures.
    wp_apply "IH".
    unfold chan_contents.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    done.
Qed.

Theorem wp_TrySend (chanref : loc) (v : val) lk ty P:
    {{{ is_channel_alloc chanref lk false ty P ∗ P v}}}
        TrySend (InjRV(#chanref, lk)) v
    {{{(success : bool), RET (#(success)); if success then True else P v}}}.
Proof.
  iIntros (Φ) "[HPre Hv] HΦ".
  wp_pures.
  wp_rec.
  wp_pures.
  iDestruct "HPre" as "#Hlock".
  wp_apply wp_Mutex__Lock.
    - iFrame "Hlock".
    - iIntros "[H0 H1]".
      wp_pures.
      iNamed "H1".
      iDestruct "H1" as "[H1 H2]".
      unfold own_chan.
      wp_untyped_load.
      wp_pures.
      wp_apply wp_ChanLen.
      { iExact "Hlock". }
      iIntros (len success) "_".
      wp_pures.
      wp_if_destruct.
      + wp_apply wp_ChanAppend.
        wp_pures.
        wp_untyped_store.
        wp_apply (wp_Mutex__Unlock with "[Hlock Hv H0 H1 H2]").
        { iFrame "Hlock".
          iFrame.
          iNext.
          iExists cap, eff_cap, (l ++ [v]).
          iFrame.
          done.
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        done.
      + wp_apply (wp_Mutex__Unlock with "[Hlock H0 H1 H2]").
        { iFrame "Hlock".
          iFrame.
          iNext.
          iExists cap, eff_cap, l.
          iFrame.
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        done.
Qed.

(* Try iLob induction *)
Theorem wp_ChannelSend (chanref : loc) (v : val) lk ty P:
    {{{ is_channel_alloc chanref lk false ty P ∗ P v}}}
        ChannelSend (InjRV(#chanref, lk)) v
    {{{(success : bool), RET (#(success)); True}}}.
Proof.
  iIntros (Φ) "[#HPre Hv] HΦ".
  wp_rec.
  wp_pures.
  iLöb as "IH" forall (Φ).
  wp_apply (wp_TrySend with "[HPre Hv]").
  - eauto.
  - iIntros (success) "Hv".
    wp_pures.
    destruct success.
    + wp_pures.
      iModIntro.
      iApply "HΦ".
      done.
    + wp_pures.
      wp_apply ("IH" with "Hv").
      iApply "HΦ".
Qed.

End heap.