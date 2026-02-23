Require Import New.proof.proof_prelude.
From New.golang.theory Require Import chan.
From New.proof.github_com.goose_lang.goose.model.channel.idiom Require Export base.
From New.golang.theory Require Import chan.
From iris.base_logic Require Import ghost_map.


(** Future Channel

    This file provides the future idiom - a pattern where
    multiple workers fulfill promises independently and a single consumer awaits all results.

    ** Go Pattern

    This idiom is designed for code where you launch multiple independent
    goroutines to compute results concurrently, then collect all their results
    without caring about the order they complete. A canonical example is the
    replicated search pattern from Rob Pike's "Go Concurrency Patterns"
    (https://go.dev/talks/2012/concurrency.slide#46) talk:


    func Google(query string) (results []Result) {
        c := make(chan Result, 3)
        go func() { c <- Web(query) }()
        go func() { c <- Image(query) }()
        go func() { c <- Video(query) }()

        for i := 0; i < 3; i++ {
            result := <-c
            results = append(results, result)
        }
        return
    }

    ** How to Use

    1. Initialize a channel for use as a future with [start_future]
    2. For each producer, allocate a [Fulfill] with [future_alloc_promise],
       giving it a predicate contract P_i that describes what that producer will provide
    3. Each worker sends its result using [wp_future_fulfill], providing
       [Fulfill γ contract ∗ contract v], bundled as [Fulfilled γ v]
    4. The consumer receives using [wp_future_await]; each receive resolves
       one contract from [pending], returning [P v] for some [P] that was
       removed from [pending]
    5. When [pending] is empty, all contracts have been satisfied

    ** Understanding the Protocol

    Matching happens *at receive time*. Each receive identifies which contract
    was fulfilled (via ghost state agreement) and removes it from [pending].

    The postcondition of [wp_future_await] tells you:
    - [pending] splits as [pre ++ P :: post]
    - You get [P v] — the contract applied to the received value
    - You get [Await γ (pre ++ post)] — the remaining pending contracts
    - You don't know *which* [P] was resolved — that depends on scheduling
*)

Section future.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Context `{!inG Σ unitR}.

Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].
Context `{!ghost_mapG Σ gname (V → iProp Σ)}.
Set Default Proof Using "All".


Record future_names := {
  chan_name : chan_names;
  contracts_name : gname
}.

(** [Fulfill γ contract] is a token representing a registered contract.
    The holder commits to eventually sending a value [v] satisfying [contract v].
    Internally, it holds half of a ghost map fragment. *)
Definition Fulfill (γ : future_names) (contract : V → iProp Σ) : iProp Σ :=
  ∃ (gn : gname),
    gn ↪[γ.(contracts_name)]{#1/2} contract.

(** [Fulfilled γ v] bundles a [Fulfill] with evidence that the contract is
    satisfied. This is what gets transferred through the channel. *)
Definition Fulfilled (γ : future_names) (v: V) : iProp Σ :=
  ∃ contract,
    Fulfill γ contract ∗ contract v.

(** [Await γ pending] is the consumer's tracking state.
    [pending] is the list of contracts not yet matched to a received value.

    Internally, a ghost map tracks which ghost names correspond to pending
    contracts. The map's values (up to permutation) equal [pending]. *)
Definition Await (γ : future_names)
    (pending : list (V → iProp Σ)) : iProp Σ :=
  ∃ (pending_map : gmap gname (V → iProp Σ)),
    ghost_map_auth γ.(contracts_name) 1 pending_map ∗
    ⌜(map_to_list pending_map).*2 ≡ₚ pending⌝ ∗
    [∗ map] gn ↦ P ∈ pending_map,
      gn ↪[γ.(contracts_name)]{#1/2} P.

(** [is_future γ ch] is the persistent channel invariant. The channel
    carries [Fulfilled] tokens — values bundled with their contract evidence. *)
Definition is_future (γ : future_names) (ch : loc) : iProp Σ :=
  is_chan ch γ.(chan_name) V ∗
  inv nroot (
    ∃ (s : chanstate.t V),
      "Hch" ∷ own_chan  γ.(chan_name) V s ∗
      match s with
      | chanstate.Buffered msgs => [∗ list] v ∈ msgs, Fulfilled γ v
      | chanstate.SndPending v => Fulfilled γ v
      | chanstate.SndCommit v => Fulfilled γ v
      | chanstate.Idle | chanstate.RcvPending | chanstate.RcvCommit => True
      | _ => False
      end
  )%I.

Local Lemma map_to_list_snd_insert {K} `{Countable K} {A}
  (m : gmap K A) (k : K) (v : A) :
  m !! k = None →
  (map_to_list (<[k := v]> m)).*2 ≡ₚ v :: (map_to_list m).*2.
Proof.
  intros Hlookup.

  have Hperm_pairs :
      map_to_list (<[k:=v]> m) ≡ₚ (k, v) :: map_to_list m.
  { 
    exact (map_to_list_insert (K:=K) (M:=gmap K) (A:=A) m k v Hlookup).
  }

  have Hperm_vals :
      map snd (map_to_list (<[k:=v]> m)) ≡ₚ map snd ((k,v) :: map_to_list m) :=
    Permutation_map snd Hperm_pairs.
    done.

Qed.

Local Lemma map_to_list_snd_delete {K} `{Countable K} {A}
  (m : gmap K A) (k : K) (v : A) :
  m !! k = Some v →
  (map_to_list m).*2 ≡ₚ v :: (map_to_list (delete k m)).*2.
Proof.
  intros Hlookup.

  have Hperm_pairs :
      map_to_list m ≡ₚ (k, v) :: map_to_list (delete k m).
  { exact (Permutation_sym (map_to_list_delete m k v Hlookup)). }

  have Hperm_vals :
      map snd (map_to_list m) ≡ₚ map snd ((k, v) :: map_to_list (delete k m)) :=
    Permutation_map snd Hperm_pairs.

    done.
Qed.

Local Lemma Permutation_cons_split {A} (x : A) (l l' : list A) :
  l ≡ₚ x :: l' →
  ∃ pre post, l = pre ++ x :: post ∧ l' ≡ₚ pre ++ post.
Proof.
  intros Hperm.
  destruct (Permutation_cons_inv_r l' l x Hperm) as [pre [post [Hl Hperm']]].
  exists pre, post. split; [exact Hl | exact Hperm'].
Qed.

Lemma start_future (ch : loc) (γ : chan_names) (s : chanstate.t V) :
s = chanstate.Idle ∨ s = chanstate.Buffered [] ->
  is_chan ch γ V -∗
  own_chan γ V s
 ={⊤}=∗
  ∃ γmf, is_future γmf ch ∗ Await γmf [].
Proof.
  intros Hs.
  iIntros "#Hch Hoc".
  iMod (ghost_map_alloc_empty) as (γcontracts) "Hmap_auth".
  set (γmf := {|
    chan_name := γ;
    contracts_name := γcontracts
  |}).
  iMod (inv_alloc nroot _ (
    ∃ s',
      "Hch" ∷ own_chan γ V s' ∗
      match s' with
      | chanstate.Buffered msgs => [∗ list] v ∈ msgs, Fulfilled γmf v
      | chanstate.SndPending v => Fulfilled γmf v
      | chanstate.SndCommit v => Fulfilled γmf v
      | chanstate.Idle | chanstate.RcvPending | chanstate.RcvCommit => True
      | _ => False
      end
  )%I with "[Hoc]") as "#Hinv".
  {
    iNext. iExists s. iFrame.
    destruct Hs as [-> | ->]; simpl; done.
  }
  iModIntro. iExists γmf.
  iSplitL "".
  { iFrame "#". }
  iExists ∅.
  iFrame. iSplitL "". { iPureIntro. rewrite map_to_list_empty. done. }
  simpl. done.
Qed.

Lemma future_alloc_promise γ ch (contract : V → iProp Σ)
    (pending : list (V → iProp Σ)) :
  is_future γ ch -∗
  Await γ pending ={⊤}=∗
  Fulfill γ contract ∗ Await γ (pending ++ [contract]).
  Proof .
  iIntros "#Hmf HAwait".
  iDestruct "HAwait" as (pending_map) "(Hauth & %Hperm & Hfrags)".
  iMod (own_alloc_cofinite () (dom pending_map)) as (gn) "[%Hfresh _]".
  { done. }
  apply not_elem_of_dom in Hfresh.
  iMod (ghost_map_insert gn contract with "Hauth") as "[Hauth Hfrag]".
  { done. }
  iDestruct "Hfrag" as "[Hfrag1 Hfrag2]".
  iModIntro.
  iSplitL "Hfrag1".
  { iExists gn. iFrame. }
  iExists (<[gn := contract]> pending_map).
  iFrame "Hauth".
  iSplitR "Hfrags Hfrag2".
  - iPureIntro.
    etrans; first apply map_to_list_snd_insert; first done.
    rewrite Hperm. apply Permutation_cons_append.
  - iApply big_sepM_insert; first done.
    iFrame.
Qed.

Lemma future_fulfill_au γ ch (v : V) :
  ∀ (Φ: iProp Σ),
  is_future γ ch -∗
  £1 ∗ £1 ∗ £1 ∗ Fulfilled γ v -∗
  ▷ (True -∗ Φ) -∗
  send_au γ.(chan_name) v Φ.
Proof.
  iIntros (Φ) "#Hmf (Hlc1 & Hlc2 & Hlc3 & HFulfilled) Hau".
  rewrite /is_future.
  iDestruct "Hmf" as "[#Hisch #Hinv]".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iExists s. iFrame "Hch".
  destruct s; try done.
  - iIntros "Hoc".
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc Hinv_open HFulfilled]") as "_".
    {
      iNext. iFrame.
      rewrite big_sepL_app. iFrame. simpl. done.
    }
    iModIntro. iApply "Hau". done.
  - iIntros "Hoc".
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc HFulfilled]") as "_".
    {
      iNext. iExists (chanstate.SndPending v). iFrame.
    }
    iModIntro.
    unfold send_nested_au.
    iInv "Hinv" as "Hinv_open2" "Hinv_close2".
    iMod (lc_fupd_elim_later with "Hlc2 Hinv_open2") as "Hinv_open2".
    iNamed "Hinv_open2".
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask2"].
    iNext. iExists s. iFrame "Hch".
    destruct s; try done.
    + iIntros "Hoc".
      iMod "Hmask2".
      iMod ("Hinv_close2" with "[Hoc Hinv_open2]") as "_".
      {
        iNext. iExists chanstate.Idle. iFrame.
      }
      iModIntro. iApply "Hau". done.
  - iIntros "Hoc".
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc HFulfilled]") as "_".
    {
      iNext. iExists (chanstate.SndCommit v). iFrame.
    }
    iModIntro. iApply "Hau". done.
Qed.

Lemma wp_future_fulfill γ ch (v : V) :
  {{{ is_future γ ch ∗ Fulfilled γ v }}}
    chan.send t #ch #v
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(#Hmf & HFulfilled) HΦ".
  rewrite /is_future.
  iDestruct "Hmf" as "[#Hch #Hinv]".
  iApply (chan.wp_send ch v γ.(chan_name) with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & _)".
  iApply (future_fulfill_au with "[$Hch $Hinv] [$Hlc1 $Hlc2 $Hlc3 $HFulfilled]").
  done.
Qed.

(** The core receive lemma. Each receive:
    1. Pulls a [Fulfilled γ v] from the channel invariant
    2. Uses ghost map agreement to identify which contract was fulfilled
    3. Removes the matched contract from [pending]
    4. Returns [P v] directly to the caller *)
Lemma future_await_au γ ch
    (pending : list (V → iProp Σ)) :
  ∀ (Φ: V → bool → iProp Σ),
  is_future γ ch -∗
  £1 ∗ £1 ∗ Await γ pending -∗
  ▷ (∀ (v : V) (P : V → iProp Σ) (pre post : list (V → iProp Σ)),
      ⌜pending = pre ++ P :: post⌝ -∗
      P v -∗
      Await γ (pre ++ post) -∗
      Φ v true) -∗
  recv_au γ.(chan_name) V (λ (v:V) (ok:bool), Φ v ok).
Proof.
  iIntros (Φ) "#Hmf (Hlc1 & Hlc2 & HAwait) Hau".
  rewrite /is_future.
  iDestruct "Hmf" as "[#isHch #Hinv]".

  iAssert (
    ∀ (v_rcv : V),
      Fulfilled γ v_rcv -∗
      Await γ pending -∗
      |==> ∃ (P : V → iProp Σ) (pre post : list (V → iProp Σ)),
        ⌜pending = pre ++ P :: post⌝ ∗ P v_rcv ∗ Await γ (pre ++ post)
  )%I as "Hmatch".
  {
    iIntros (v_rcv) "HFulfilled HAwait".
    iDestruct "HFulfilled" as (contract_f) "[HFulfill Hcontract_v]".
    iDestruct "HFulfill" as (gn_f) "Hfrag_f".
    iDestruct "HAwait" as (pending_map) "(Hauth & %Hperm & Hfrags)".
    iDestruct (ghost_map_lookup with "Hauth Hfrag_f") as %Hlookup.
    iDestruct (big_sepM_delete _ _ gn_f with "Hfrags")
      as "[Hfrag_p Hfrags_rest]"; first done.
    iCombine "Hfrag_f Hfrag_p" as "Hfrag_full".
    iMod (ghost_map_delete with "Hauth Hfrag_full") as "Hauth".
    pose proof (map_to_list_snd_delete _ _ _ Hlookup) as Hmap_perm.
    assert (pending ≡ₚ contract_f :: (map_to_list (delete gn_f pending_map)).*2) as Hcons.
    { rewrite -Hmap_perm. done. }
    apply Permutation_cons_split in Hcons
      as (pre & post & Hsplit & Hrest_perm).
    iModIntro. iExists contract_f, pre, post.
    iFrame "Hcontract_v".
    iSplitR; first done.
    iExists (delete gn_f pending_map).
    iFrame "Hauth Hfrags_rest". iPureIntro.
    by symmetry.
  }

  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iExists s. iFrame "Hch".
  destruct s; try done.
  - (* Buffered *)
    destruct buff as [|v_rcv msgs'] eqn:Hmsgs; simpl.
    + done.
    + iDestruct "Hinv_open" as "[HFulfilled_v HFulfilleds]".
      iIntros "Hoc".
      iMod "Hmask".
      iMod ("Hinv_close" with "[Hoc HFulfilleds]") as "_".
      { iNext. iExists (chanstate.Buffered msgs'). iFrame. }
      iMod ("Hmatch" with "HFulfilled_v HAwait")
        as (P pre post) "(%Hsplit & HP & HAwait')".
      iModIntro.
      iApply ("Hau" with "[%] HP HAwait'"). done.
  - (* RcvPending *)
    iIntros "Hoc".
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc]") as "_".
    { iNext. iExists chanstate.RcvPending. iFrame. }
    iModIntro.
    iInv "Hinv" as "Hinv_open2" "Hinv_close2".
    iMod (lc_fupd_elim_later with "Hlc2 Hinv_open2") as "Hinv_open2".
    iNamed "Hinv_open2".
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask2"].
    iNext. iExists s. iFrame "Hch".
    destruct s; try done.
    + 
      iIntros "Hoc".
      iMod "Hmask2".
      iMod ("Hinv_close2" with "[Hoc]") as "_".
      { iNext. iExists chanstate.Idle. iFrame. }
      iMod ("Hmatch" with "Hinv_open2 HAwait")
        as (P pre post) "(%Hsplit & HP & HAwait')".
      iModIntro.
      iApply ("Hau" with "[%] HP HAwait'"). done.
  - 
    iIntros "Hoc".
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc]") as "_".
    { iNext. iFrame. }
    iMod ("Hmatch" with "Hinv_open HAwait")
      as (P pre post) "(%Hsplit & HP & HAwait')".
    iModIntro.
    iApply ("Hau" with "[%] HP HAwait'"). done.
Qed.

Lemma wp_future_await γ ch
    (pending : list (V → iProp Σ)) :
  {{{ is_future γ ch ∗ Await γ pending }}}
    chan.receive t #ch
  {{{ (v : V) (P : V → iProp Σ) (pre post : list (V → iProp Σ)),
      RET (#v, #true);
      ⌜pending = pre ++ P :: post⌝ ∗ P v ∗ Await γ (pre ++ post) }}}.
Proof.
  iIntros (Φ) "(#Hmf & HAwait) HΦ".
  rewrite /is_future.
  iDestruct "Hmf" as "[#Hch #Hinv]".
  iApply (chan.wp_receive ch γ.(chan_name) with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  iApply (future_await_au with "[$Hch $Hinv] [$Hlc1 $Hlc2 $HAwait]").
  iNext. iIntros (v P pre post) "%Hsplit HP HAwait".
  iApply ("HΦ" $! v P pre post).
  iFrame. done.
Qed.

End future.