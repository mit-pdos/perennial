From stdpp Require Import countable.
From iris.algebra Require Import gmap_view view.
From Perennial.algebra Require Import mlist.
From Perennial.base_logic Require Import lib.iprop.
From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import tactics.
From Perennial.Helpers Require Import Map.
From Perennial.algebra Require Import log_heap own_discrete.

Set Default Proof Using "Type".

Class asyncG Σ (K V: Type) `{Countable K, EqDecision V} := {
  async_listG :> fmlistG (gmap K V) Σ;
  async_mapG :> inG Σ (gmap_viewR K natO);
}.

Definition asyncΣ K V `{Countable K, EqDecision V} : gFunctors :=
  #[ fmlistΣ (gmap K V); GFunctor (gmap_viewR K natO) ].

Instance subG_asyncΣ Σ K V `{Countable K, EqDecision V} : subG (asyncΣ K V) Σ → asyncG Σ K V.
Proof.
  intros.
  apply subG_inv in H0 as [? ?]. (* FIXME(tej): why is this needed? *)
  solve_inG.
Qed.

(** We need two ghost names. *)
Record async_gname := {
  async_list : gname;
  async_map : gname;
}.

Section async.
Context {K V: Type} `{Countable K, EqDecision V, asyncG Σ K V}.

Implicit Types (γ:async_gname) (k:K) (v:V) (i:nat) (σ: gmap K V) (σs: async (gmap K V)) (last: gmap K nat).

Definition lookup_async σs i k : option V :=
  σ ← possible σs !! i; σ !! k.


Local Definition is_last σs k i : Prop :=
  ∃ v, lookup_async σs i k = Some v ∧
    ∀ i', i ≤ i' → i' < length (possible σs) → lookup_async σs i' k = Some v.
Local Definition own_last_auth γ q σs : iProp Σ :=
  ∃ (last: gmap K nat), ⌜map_Forall (is_last σs) last⌝ ∗ own γ.(async_map) (gmap_view_auth q last).
Local Definition own_last_frag γ k i : iProp Σ :=
  own γ.(async_map) (gmap_view_frag k (DfracOwn 1) i).

(* The possible states in [σs] are tracked in a regular append-only list.
Additionally, there is a way to control which was the last transaction that changed
a certain key, which ensures that the key stayed unchanged since then.

 Durability is orthogonal to this library: separately from the async we know
 that some index is durable, which guarantees that facts about that index and
 below can be carried across a crash. *)
Definition async_ctx γ q σs : iProp Σ :=
   own_last_auth γ q σs ∗
      (* Everything has the same domain *)
      ⌜Forall (λ σ, dom (gset _) σ = dom (gset _) (latest σs)) (possible σs)⌝ ∗
      (* We also have the [lb] in here to avoid some update modalities below. *)
      fmlist γ.(async_list) q (possible σs) ∗ fmlist_lb γ.(async_list) (possible σs).

(* We support two-step initialziation, where the γ is picked in the first step and
the initial σs are picked in the second step. [async_pre_ctx] is the output of the
first step and the input to the second. *)
Definition async_pre_ctx γ : iProp Σ :=
  own γ.(async_map) (gmap_view_auth 1 ∅) ∗ fmlist γ.(async_list) 1 [].

Definition async_lb γ σs : iProp Σ :=
  fmlist_lb γ.(async_list) (possible σs).

(* ephemeral_txn_val owns only a single point in the ephemeral transactions.
It is persistent. *)
Definition ephemeral_txn_val γ (i:nat) (k: K) (v: V) : iProp Σ :=
  ∃ σ, ⌜σ !! k = Some v⌝ ∗ fmlist_idx γ.(async_list) i σ.

(* ephemeral_val_from owns ephemeral transactions from i onward (including
future transactions); this is what makes it possible to use ephemeral
maps-to facts to append a new gmap with those addresses updated (see
[map_update_predicate] for the kind of thing we should be able to do) *)
Definition ephemeral_val_from γ (i:nat) (k: K) (v: V) : iProp Σ :=
  ephemeral_txn_val γ i k v ∗ own_last_frag γ k i.

(* exactly like [ephemeral_txn_val] except owning a half-open range of
transactions [lo, hi) *)
Definition ephemeral_txn_val_range γ (lo hi:nat) (k: K) (v: V): iProp Σ :=
  [∗ list] i ∈ seq lo (hi-lo), ephemeral_txn_val γ i k v.

Global Instance ephemeral_txn_val_discretizable γ i k v: Discretizable (ephemeral_txn_val γ i k v).
Proof. apply _. Qed.

Global Instance ephemeral_val_from_discretizable γ i k v: Discretizable (ephemeral_val_from γ i k v).
Proof. apply _. Qed.

Global Instance ephemeral_txn_val_range_discretizable γ lo hi k v: Discretizable (ephemeral_txn_val_range γ lo hi k v).
Proof. apply _. Qed.

Global Instance async_ctx_discretizable γ q l: Discretizable (async_ctx γ q l).
Proof. apply _. Qed.

Lemma own_last_frag_conflict γ k i1 i2 :
  own_last_frag γ k i1 -∗
  own_last_frag γ k i2 -∗
  False.
Proof.
  rewrite /own_last_frag.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %Hvalid%gmap_view_frag_op_valid_L.
  iPureIntro.
  destruct Hvalid as [Hdfrac _].
  rewrite dfrac_op_own in Hdfrac.
  apply (iffLR (dfrac_valid_own _)) in Hdfrac.
  contradiction.
Qed.

Lemma ephemeral_txn_val_agree γ i k v1 v2 :
  ephemeral_txn_val γ i k v1 -∗
  ephemeral_txn_val γ i k v2 -∗
  ⌜ v1 = v2 ⌝.
Proof.
  iDestruct 1 as (? Hlookup1) "Hidx1".
  iDestruct 1 as (? Hlookup2) "Hidx2".
  iDestruct (fmlist_idx_agree_1 with "[$] [$]") as %->; iPureIntro; congruence.
Qed.

Lemma ephemeral_val_from_conflict γ i1 i2 k v1 v2 :
  ephemeral_val_from γ i1 k v1 -∗
  ephemeral_val_from γ i2 k v2 -∗
  False.
Proof.
  iIntros "[_ H1] [_ H2]".
  iApply (own_last_frag_conflict with "H1 H2").
Qed.

Global Instance async_ctx_timeless γ q σs : Timeless (async_ctx γ q σs).
Proof. apply _. Qed.

Global Instance async_ctx_fractional γ σs : Fractional (λ q, async_ctx γ q σs).
Proof.
  apply fractional_sep; [ | apply _ ].
  intros p q.
  rewrite /own_last_auth.
  iSplit.
  - iDestruct 1 as (last ?) "[H1 H2]".
    iSplitL "H1"; rewrite /own_last_auth; eauto.
  - iDestruct 1 as "[H1 H2]".
    iDestruct "H1" as (last1 ?) "H1".
    iDestruct "H2" as (last2 ?) "H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid%gmap_view_auth_frac_op_inv_L.
    subst.
    iCombine "H1 H2" as "H".
    eauto.
Qed.

Local Lemma lookup_async_insert_ne k k' v' m σs j :
  k ≠ k' →
  lookup_async (async_put (<[k:=v']> m) σs) j k' = lookup_async (async_put m σs) j k'.
Proof.
  intros Hne. rewrite /lookup_async /possible /=.
  destruct (lt_eq_lt_dec j (length (possible σs))) as [[Hlt | ->]|Hlt].
  - rewrite lookup_app_l //. rewrite lookup_app_l //.
  - rewrite !list_lookup_middle //=.
    rewrite lookup_insert_ne //.
  - rewrite !lookup_ge_None_2 // app_length /=; lia.
Qed.

(* Just shift the "last" transaction i without changing the value. *)
Local Lemma own_last_shift γ σs k i i' :
  (i ≤ i')%nat →
  (i' < length (possible σs))%nat →
  own_last_auth γ 1 σs -∗
  own_last_frag  γ k i ==∗
  own_last_auth γ 1 σs ∗ own_last_frag γ k i'.
Proof.
  iIntros (Hle Hi') "Halast Hflast".
  iDestruct "Halast" as (last Hlast) "Hmap".
  iDestruct (own_valid_2 with "Hmap Hflast") as %[_ Hk]%gmap_view_both_valid_L.
  iMod (own_update_2 with "Hmap Hflast") as "[Hmap Hflast]".
  { apply (gmap_view_update _ k i i'). }
  iModIntro. iFrame "Hflast".
  iExists _. iFrame. iPureIntro. intros k' j.
  destruct (decide (k=k')) as [->|Hne].
  - rewrite lookup_insert=>[=<-]. destruct (Hlast _ _ Hk) as (v & Hv & Htail).
    exists v. split.
    + apply Htail; lia.
    + intros i'' Hi''. apply Htail. lia.
  - rewrite lookup_insert_ne // => Hk'.
    destruct (Hlast _ _ Hk') as (v & Hv & Htail).
    exists v. done.
Qed.

Local Lemma own_last_put γ σs :
  own_last_auth γ 1 σs -∗ own_last_auth γ 1 (async_put (latest σs) σs).
Proof.
  iIntros "Hlast". iDestruct "Hlast" as (last Hlast) "Hmap".
  iExists last. iFrame. iPureIntro.
  intros k i Hk. destruct (Hlast _ _ Hk) as (v & Hv & Htail).
  assert (i < length (possible σs)).
  { apply lookup_lt_is_Some_1. rewrite /lookup_async in Hv.
    destruct (possible σs !! i); last done. eauto. }
  exists v. split.
  - rewrite /lookup_async possible_async_put lookup_app_l //.
  - intros i' Hle Hlen.
    rewrite /lookup_async possible_async_put.
    destruct (decide (i' = length (possible σs))) as [->|Hne].
    + rewrite list_lookup_middle //.
      rewrite -lookup_possible_latest'.
      assert (length (possible σs) > 0).
      { rewrite /possible app_length /=. lia. }
      eapply Htail; lia.
    + rewrite length_possible_async_put in Hlen.
      rewrite lookup_app_l; last lia.
      apply Htail; lia.
Qed.

(* As far as just [own_last] is concerned, we can change the value of the
last transaction. *)
Local Lemma own_last_update γ σs k v' m i :
  own_last_auth γ 1 (async_put m σs) -∗
  own_last_frag γ k i ==∗
  own_last_auth γ 1 (async_put (<[k:=v']> m) σs) ∗
    own_last_frag γ k (S (length (possible σs)) - 1).
Proof.
  iIntros "Halast Hflast". iDestruct "Halast" as (last Hlast) "Hmap".
  assert ((S (length (possible σs)) - 1) = length (possible σs)) as -> by lia.
  iMod (own_update_2 with "Hmap Hflast") as "[Hmap $]".
  { apply (gmap_view_update _ k _ (length (possible σs))). }
  iExists _. iFrame "Hmap". iPureIntro.
  intros k' j. destruct (decide (k = k')) as [<-|Hne].
  - rewrite lookup_insert=>[=<-]. exists v'.
    assert (lookup_async (async_put (<[k:=v']> m) σs) (length (possible σs)) k = Some v').
    { rewrite /lookup_async possible_async_put.
      rewrite list_lookup_middle //=. rewrite lookup_insert. done. }
    split; first done.
    intros i'. rewrite length_possible_async_put=>??.
    assert (i' = length (possible σs)) as -> by lia. done.
  - rewrite lookup_insert_ne // => Hk'.
    destruct (Hlast _ _ Hk') as (v & Hv & Htail).
    exists v. split.
    + rewrite lookup_async_insert_ne //.
    + intros j' Hle Hlen . rewrite lookup_async_insert_ne //.
      apply Htail; first lia.
      move:Hlen. rewrite /possible /= !app_length /=. lia.
Qed.

Theorem ephemeral_txn_val_range_acc γ lo hi k v i :
  (lo ≤ i < hi)%nat →
  ephemeral_txn_val_range γ lo hi k v -∗
  (* does not return the range under the assumption we make these persistent *)
  ephemeral_txn_val γ i k v.
Proof.
  iIntros (Hbound) "Hrange".
  rewrite /ephemeral_txn_val_range.
  assert (seq lo (hi - lo)%nat !! (i - lo)%nat = Some i).
  { apply lookup_seq; lia. }
  iDestruct (big_sepL_lookup with "Hrange") as "$"; eauto.
Qed.

Theorem ephemeral_val_from_in_bounds γ q σs i k v :
  async_ctx γ q σs -∗
  ephemeral_val_from γ i k v -∗
  (* if equal, only owns the new transactions and no current ones *)
  ⌜i < length (possible σs)⌝%nat.
Proof.
  iIntros "(Halast & _ & Halist & _) [Hval Hflast]".
  iDestruct "Halast" as (last Hlast) "Hmap".
  iDestruct "Hval" as (σ Hσ) "Hflist".
  iDestruct (fmlist_idx_agree_2 with "Halist Hflist") as %Hi.
  iPureIntro.
  apply lookup_lt_is_Some. rewrite Hi. eauto.
Qed.

Theorem ephemeral_txn_val_lookup γ q σs i k v :
  async_ctx γ q σs -∗
  ephemeral_txn_val γ i k v -∗
  ⌜lookup_async σs i k = Some v⌝.
Proof.
  iIntros "(Halast & _ & Halist & _) Hval".
  iDestruct "Halast" as (last Hlast) "Hmap".
  iDestruct "Hval" as (σ Hσ) "Hflist".
  iDestruct (fmlist_idx_agree_2 with "Halist Hflist") as %Hi.
  rewrite /lookup_async Hi /=. done.
Qed.

Lemma async_ctx_lb_prefix γ q σs σs' :
  async_ctx γ q σs -∗
  async_lb γ σs' -∗
  ⌜ async_prefix σs' σs ⌝.
Proof.
  iIntros "H1 H2".
  iDestruct "H1" as "(?&?&?&?)".
  iDestruct (fmlist_agree_2 with "[$] [$]") as "$".
Qed.

Lemma async_ctx_to_lb γ q σs :
  async_ctx γ q σs -∗
  async_lb γ σs.
Proof. iIntros "H1". iDestruct "H1" as "(?&?&?&$)". Qed.

Theorem async_ctx_doms γ q σs i σ :
  possible σs !! i = Some σ →
  async_ctx γ q σs -∗
  ⌜ dom (gset K) σ = dom (gset K) σs.(latest) ⌝.
Proof.
  iIntros (Hi) "(_ & %Hdoms & _)". iPureIntro.
  eapply Forall_lookup_1 in Hdoms; done.
Qed.

Theorem async_ctx_doms_prefix_latest γ q σs' σs :
  async_prefix σs' σs →
  async_ctx γ q σs -∗
  ⌜ dom (gset K) σs'.(latest) = dom (gset K) σs.(latest) ⌝.
Proof.
  iIntros (Hprefix) "Hctx".
  iDestruct (async_ctx_doms _ _ _ (length (possible σs') - 1) (σs'.(latest)) with "Hctx")
            as %Hdom.
  {
    destruct Hprefix as (?&->).
    rewrite lookup_app_l; first apply lookup_possible_latest'.
    rewrite /possible app_length /=. lia.
  }
  eauto.
Qed.

Theorem ephemeral_lookup_txn_val γ q σs i k v :
  lookup_async σs i k = Some v →
  async_ctx γ q σs -∗
  ephemeral_txn_val γ i k v.
Proof.
  rewrite /lookup_async /ephemeral_txn_val.
  iIntros (Hlookup) "(_ & _ & _ & Hflist)".
  destruct (possible σs !! i) as [σ|] eqn:Hσ; last done.
  simpl in Hlookup.
  iExists _. iSplit; first done.
  iApply fmlist_lb_to_idx; done.
Qed.

Theorem emphemeral_lookup_all_txn_val γ q σs i σ:
  possible σs !! i = Some σ →
  async_ctx γ q σs -∗
  [∗ map] k↦v ∈ σ, ephemeral_txn_val γ i k v.
Proof.
  iIntros (Hi) "Hctx".
  (* Arrange induction hypothesis. *)
  remember σ as σ' eqn:Hσeq. rewrite Hσeq in Hi.
  assert (σ' ⊆ σ) as Hσ by rewrite Hσeq //.
  clear Hσeq.
  (* Perform induction *)
  iInduction σ' as [|a v σ'] "IH" using map_ind.
  { done. }
  iApply big_sepM_insert; first done.
  iSplit.
  - iApply ephemeral_lookup_txn_val; last done.
    rewrite /lookup_async Hi /=. eapply lookup_weaken; last done.
    rewrite lookup_insert. done.
  - iApply "IH"; last done. iPureIntro. etrans; last exact Hσ.
    apply insert_subseteq. done.
Qed.

(** All transactions since [i] have the value given by [ephemeral_val_from γ i]. *)
Theorem ephemeral_val_from_val γ q σs i i' k v :
  (i ≤ i') →
  (i' < length (possible σs))%nat →
  async_ctx γ q σs -∗
  ephemeral_val_from γ i k v -∗
  ephemeral_txn_val γ i' k v.
Proof.
  iIntros (??) "Hauth [Hval Hlast]".
  iDestruct (ephemeral_txn_val_lookup with "Hauth Hval") as %Hlookup.
  iClear "Hval".
  iDestruct "Hauth" as "(Halast & Halist & Hflist)".
  iDestruct "Halast" as (last Hlast) "Hmap".
  iDestruct (own_valid_2 with "Hmap Hlast") as %(_  & _ & Hmap)%gmap_view_both_frac_valid_L.
  destruct (Hlast _ _ Hmap) as (v' & Hlookup' & Htail).
  rewrite Hlookup in Hlookup'. injection Hlookup' as [=<-].
  iApply ephemeral_lookup_txn_val; last first.
  - rewrite /async_ctx. iFrame. iExists last. iFrame. done.
  - apply Htail; done.
Qed.

Theorem ephemeral_val_from_val_at_same γ i k v :
  ephemeral_val_from γ i k v -∗
  ephemeral_txn_val γ i k v.
Proof. iDestruct 1 as "(#?&?)". eauto. Qed.

Theorem ephemeral_val_from_agree_latest γ q σs i k v :
  async_ctx γ q σs -∗
  ephemeral_val_from γ i k v -∗
  ⌜latest σs !! k = Some v⌝.
Proof.
  iIntros "Hctx Hval".
  iDestruct (ephemeral_val_from_in_bounds with "Hctx Hval") as %Hbound.
  iDestruct (ephemeral_val_from_val _ _ _ _ (length (possible σs) - 1) with "Hctx Hval") as "#Hval_latest".
  { lia. }
  { lia. }
  iDestruct (ephemeral_txn_val_lookup with "Hctx Hval_latest") as %Hlookup.
  iPureIntro.
  rewrite /lookup_async lookup_possible_latest' /= in Hlookup.
  auto.
Qed.

Theorem ephemeral_val_from_agree_latest_map γ q σs i σ :
  async_ctx γ q σs -∗
  ([∗ map] k↦v ∈ σ, ephemeral_val_from γ i k v) -∗
  ⌜σ ⊆ latest σs⌝.
Proof.
  iIntros "Hctx Hvals".
  iInduction σ as [|a v σ] "IH" using map_ind.
  { iPureIntro. apply map_empty_subseteq. }
  rewrite big_sepM_insert; last done.
  iDestruct "Hvals" as "[Hval Hvals]".
  iDestruct (ephemeral_val_from_agree_latest with "Hctx Hval") as %?.
  iDestruct ("IH" with "Hctx Hvals") as %?.
  iPureIntro. apply insert_subseteq_l; done.
Qed.

(** Move the "from" resource from i to i', and obtain a
[ephemeral_txn_val_range] for the skipped range and including [i']. *)
Theorem ephemeral_val_from_split i' γ i k v σs :
  (i ≤ i')%nat →
  (i' < length (possible σs))%nat →
  async_ctx γ 1 σs -∗
  ephemeral_val_from γ i k v ==∗
  async_ctx γ 1 σs ∗ ephemeral_txn_val_range γ i (S i') k v ∗ ephemeral_val_from γ i' k v.
Proof.
  iIntros (Hle Hi') "Hauth Hfromi".

  (* Get some things from [async_ctx] before we take it apart. *)
  iAssert (ephemeral_txn_val_range γ i (S i') k v) with "[Hauth Hfromi]" as "#$".
  { rewrite /ephemeral_txn_val_range. iInduction Hle as [|i' Hle] "IH".
    - assert (S i-i = 1) as -> by lia. rewrite big_sepL_singleton.
      iDestruct "Hfromi" as "[$ _]".
    - assert (S (S i') - i = S (S i'-i)) as -> by lia. rewrite seq_S.
      rewrite big_sepL_app. iSplit.
      { iApply ("IH" with "[] Hauth Hfromi"). iPureIntro. lia. }
      rewrite big_sepL_singleton.
      iApply (ephemeral_val_from_val with "Hauth Hfromi"); lia. }
  iAssert (ephemeral_txn_val γ i' k v) with "[Hauth Hfromi]" as "#Hvali'".
  { iApply (ephemeral_val_from_val with "Hauth Hfromi"); lia. }

  iDestruct "Hauth" as "(Halast & Halist & Hflist)".
  iDestruct "Hfromi" as "[#Hvali Hlast]".
  iMod (own_last_shift with "Halast Hlast") as "[$ $]"; [done..|].
  by iFrame "∗#".
Qed.

Theorem async_pre_ctx_init:
  ⊢ |==> ∃ γ, async_pre_ctx γ.
Proof.
  iMod (fmlist_alloc []) as (γlist) "Hlist".
  iMod (own_alloc (gmap_view_auth 1 ∅)) as (γmap) "Hmap".
  { apply gmap_view_auth_valid. }
  iModIntro. iExists (Build_async_gname γlist γmap).
  rewrite /async_pre_ctx /=. iFrame.
Qed.

Theorem async_ctx_init γ σs :
  Forall (λ σ, dom (gset _) σ = dom (gset _) (latest σs)) (pending σs) →
  async_pre_ctx γ ==∗
  async_ctx γ 1 σs ∗
  ([∗ map] k↦v ∈ (latest σs), ephemeral_val_from γ (length (possible σs) - 1) k v).
Proof.
  iIntros (Hdom) "[Hmap Hlist]".
  rewrite /async_ctx /possible /=.
  set (last := (λ _, length (pending σs)) <$> (latest σs)).
  iMod (fmlist_update (possible σs) with "Hlist") as "[$ #Hlb]".
  { apply prefix_nil. }
  iFrame "Hlb".
  iMod (own_update with "Hmap") as "Hmap".
  { eapply (gmap_view_alloc_big _ last (DfracOwn 1)); last done.
    apply map_disjoint_empty_r. }
  iDestruct "Hmap" as "[Hmap Hfrag]".
  iModIntro. iSplitR "Hfrag"; first iSplit.
  - iExists last. rewrite right_id. iFrame.
    iPureIntro. subst last. intros k i.
    rewrite lookup_fmap. destruct ((latest σs) !! k) as [v|] eqn:Hlatest; last done.
    simpl=>[=<-]. exists v. split.
    + rewrite /lookup_async lookup_possible_latest /=. done.
    + intros i'. rewrite length_possible_pending=>??.
      assert (i' = length (pending σs)) as -> by lia.
      rewrite /lookup_async lookup_possible_latest /=. done.
  - iPureIntro. apply Forall_app. split; first done.
    apply Forall_singleton. done.
  - rewrite big_opM_own_1. subst last.
    rewrite big_sepM_fmap.
    iApply (big_sepM_impl with "Hfrag"). iIntros "!#" (k v Hk) "Hfrag".
    rewrite app_length /=.
    replace (length (pending σs) + 1 - 1) with (length (pending σs)); last by lia.
    iSplitR.
    + iExists (latest σs). iSplit; first done.
      iApply fmlist_lb_to_idx; last done.
      rewrite lookup_possible_latest. done.
    + rewrite /own_last_frag. done.
Qed.

Theorem async_ctx_init_nopending γ σ :
  async_pre_ctx γ ==∗
  async_ctx γ 1 (Build_async σ []) ∗
  ([∗ map] k↦v ∈ σ, ephemeral_val_from γ 0 k v).
Proof.
  iIntros "Hpre". iMod (async_ctx_init with "Hpre") as "[$ $]"; last done.
  simpl. apply Forall_nil. done.
Qed.

Theorem async_ctx_init_set_prefix γ γ' q σs σs' :
  async_prefix σs' σs →
  async_ctx γ q σs -∗
  async_pre_ctx γ' ==∗
  async_ctx γ q σs ∗ async_ctx γ' 1 σs' ∗
  ([∗ map] k↦v ∈ latest σs',
     ephemeral_txn_val γ (length (possible σs') - 1) k v ∗
     ephemeral_val_from γ' (length (possible σs') - 1) k v).
Proof.
  iIntros (Hprefix) "Hctxold Hprenew".
  iAssert (⌜Forall (λ σ, dom (gset _) σ = dom (gset _) (latest σs)) (possible σs)⌝)%I with "[Hctxold]" as %Hdom.
  { iDestruct "Hctxold" as "(_ & $ & _)". }
  iDestruct (async_ctx_doms_prefix_latest with "Hctxold") as %Hlatestdom; first done.
  rewrite big_sepM_sep.
  iMod (async_ctx_init with "Hprenew") as "[$ $]".
  { destruct Hprefix as [l' Hl']. rewrite Hl' /possible -assoc in Hdom.
    apply Forall_app in Hdom as [Hdom _].
    eapply Forall_impl; first exact Hdom.
    simpl. intros σ ->. done. }
  iModIntro. iSplit; first done.
  iApply big_sepM_forall. iIntros (k v Hk).
  iApply (ephemeral_lookup_txn_val with "Hctxold").
  rewrite /lookup_async.
  destruct Hprefix as [l' Hl']. rewrite Hl'.
  rewrite lookup_app_l; last first.
  { assert (length (possible σs') > 0); last by lia.
    rewrite /possible app_length /=. lia. }
  rewrite lookup_possible_latest' /=. done.
Qed.

Theorem async_update_map m' γ σs m0 :
  dom (gset _) m' = dom (gset _) m0 →
  async_ctx γ 1 σs -∗
  ([∗ map] k↦v ∈ m0, ephemeral_val_from γ (length (possible σs) - 1) k v) -∗
  |==> let σs' := (async_put (m' ∪ latest σs) σs) in
     async_ctx γ 1 σs' ∗
       ([∗ map] k↦v ∈ m', ephemeral_val_from γ (length (possible σs') - 1) k v).
       (* We could also make this [length (possible σs)]; not sure what is more useful. *)
Proof.
  iIntros (Hdom) "Hctx Hm".
  iDestruct (ephemeral_val_from_agree_latest_map with "Hctx Hm") as %Hm0.
  iDestruct "Hctx" as "(Halast & %Hdoms & Halist & _)".
  rewrite /async_ctx.
  iMod (fmlist_update with "Halist") as "[$ #Hflist]".
  { apply prefix_app_r. reflexivity. }
  iFrame "Hflist".

  (* Take care of the "all domains are equal" part of the goal. *)
  rewrite /ephemeral_val_from [(own_last_auth _ _ _ ∗ _)%I]comm.
  iEval (rewrite -assoc). iSplitR.
  { iPureIntro. rewrite possible_async_put /async_put /=.
    apply Forall_app. split.
    - eapply Forall_impl; first exact Hdoms.
      simpl. intros σ ->. rewrite dom_union_L Hdom.
      eapply subseteq_dom in Hm0.
      set_solver +Hm0.
    - apply Forall_singleton. done. }

  (* Take care of the [ephemeral_txn_val] part of the goal. *)
  rewrite /ephemeral_val_from [(own_last_auth _ _ _ ∗ _)%I]comm.
  iEval (rewrite big_sepM_sep -assoc). iSplitR.
  { iApply big_sepM_forall.
    iIntros "!>" (k v Hm').
    iExists (m' ∪ latest σs). iSplit.
    - iPureIntro. rewrite lookup_union Hm'.
      destruct (latest σs !! k); done.
    - iApply fmlist_lb_to_idx; last done.
      rewrite lookup_possible_latest'. done. }
  iClear "Hflist".

  iDestruct (own_last_put with "Halast") as "Halast".
  rewrite length_possible_async_put. clear Hm0.
  iInduction m' as [|a v m] "IH" using map_ind forall (m0 Hdom).
  - assert (m0 = ∅) as ->.
    { apply dom_empty_iff. rewrite -Hdom dom_empty. done. }
    rewrite !big_sepM_empty. rewrite !left_id. by iFrame.
  - rewrite big_sepM_insert //.
    assert (is_Some (m0 !! a)) as [v0 Hv0].
    { apply elem_of_dom. rewrite -Hdom dom_insert. set_solver+. }
    iDestruct (big_sepM_delete with "Hm") as "[[_ Hlast] Hm]"; first done.
    iMod ("IH" with "[] Hm Halast") as "[$ Halast]".
    { iPureIntro. rewrite dom_delete_L -Hdom dom_insert_L.
      assert (a ∉ dom (gset K) m) as Hnotm.
      { apply not_elem_of_dom. done. }
      set_solver +Hnotm. }
    iClear "IH".
    iMod (own_last_update with "Halast Hlast") as "[Halast Hlast]".
    rewrite insert_union_l /ephemeral_val_from. iFrame. done.
Qed.

(* this splits off an [ephemeral_val_from] at exactly the last transaction *)
Theorem async_ctx_ephemeral_val_from_split γ σs i k v :
  async_ctx γ 1 σs -∗
  ephemeral_val_from γ i k v ==∗
  async_ctx γ 1 σs ∗ ephemeral_txn_val_range γ i (length (possible σs)) k v ∗
    ephemeral_val_from γ (length (possible σs) - 1) k v.
Proof.
  iIntros "Hctx Hi+".
  iDestruct (ephemeral_val_from_in_bounds with "Hctx Hi+") as %Hinbounds.
  iMod (ephemeral_val_from_split (length (possible σs) - 1) with "Hctx Hi+")
    as "(Hctx & Hold & H+)"; [lia..|].
  assert (S (length (possible σs) - 1) = length (possible σs)) as -> by lia.
  by iFrame.
Qed.

(* this splits off several [ephemeral_val_from] all at the last transaction *)
Theorem async_ctx_ephemeral_val_from_map_split γ σs i m :
  async_ctx γ 1 σs -∗
  big_opM bi_sep (ephemeral_val_from γ i) m ==∗
  async_ctx γ 1 σs ∗ big_opM bi_sep (ephemeral_txn_val_range γ i (length (possible σs))) m ∗
  big_opM bi_sep (ephemeral_val_from γ (length (possible σs) - 1)) m.
Proof.
  iIntros "Hctx Hm".
  iInduction m as [|a v m] "IH" using map_ind.
  - rewrite !big_sepM_empty.
    by iFrame.
  - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; auto.
    iMod (async_ctx_ephemeral_val_from_split with "Hctx Hi") as "(Hctx&Hrange&H+)".
    iMod ("IH" with "Hctx Hm") as "(Hctx&Hmrange&Hm+)".
    iFrame.
    rewrite !big_sepM_insert //; by iFrame.
Qed.

End async.
