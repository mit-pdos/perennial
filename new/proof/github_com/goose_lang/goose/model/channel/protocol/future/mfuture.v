Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel.protocol Require Export base.
From New.golang.theory Require Import chan.
From iris.base_logic Require Import ghost_map.
From iris.base_logic.lib Require Import saved_prop.
From Perennial.algebra Require Import ghost_var.

(** Future Channel

    This file provides the future idiom - a pattern where
    multiple workers fulfill values independently and a single consumer awaits
    all results.

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

    1. Create a future channel with [start_mfuture]
    2. For each producer, allocate a [Promise] with [mfuture_alloc_promise],
       giving it a predicate P_i that describes what that producer will provide
    3. Each worker sends its result using [wp_mfuture_fulfill], providing P_i(v_i)
    4. The consumer receives N times using [wp_mfuture_await], building up the
       [Await] predicate which tracks registered contracts and seen values
    5. When all results are received, use [mfuture_complete] to obtain [Fulfilled]

    ** Understanding Fulfilled (The Bijection)

    [Fulfilled contracts seen] means:
    - You registered predicates P₁, P₂, ..., Pn (the contracts)
    - You received values v₁, v₂, ..., vn (seen, in arrival order)
    - There exists some reordering of the contracts such that each predicate
      is satisfied by a distinct value from seen

    You know that every predicate is satisfied by exactly one value, and every
    value satisfies exactly one predicate, but you don't know which specific
    pairing occurred. This captures the inherent non-determinism of concurrent
    completion - you don't control which goroutine finishes first.

    For the single-worker case (n=1), there's only one possible pairing,
    so Fulfilled P v directly gives you P(v).
*)

Section mfuture.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!chan_protocolG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!savedPredG Σ V}.
Context `{!ghost_mapG Σ gname (V → iProp Σ)}.
Context `{!ghost_varG Σ nat}.

Record mfuture_names := {
  chan_name : chan_names;
  contracts_name : gname
}.

Definition Promise (γ : mfuture_names) (contract : V → iProp Σ) : iProp Σ :=
  ∃ (prop_gname : gname),
    prop_gname ↪[γ.(contracts_name)]{#1/2} contract ∗
    saved_pred_own prop_gname (DfracOwn (1/2)) contract.

Definition Fulfill (γ : mfuture_names) (v: V) : iProp Σ :=
  ∃ contract,
    Promise γ contract ∗ contract v.

Definition Await (γ : mfuture_names) (contracts : list (V -> iProp Σ)) (seen : list V) : iProp Σ :=
  ∃ (contracts_names: gmap gname (V -> iProp Σ)),
    ghost_map_auth γ.(contracts_name) 1 contracts_names ∗
    ⌜size contracts_names = length contracts⌝ ∗
    ([∗ list] contract ∈ contracts, Promise γ contract) ∗
    [∗ list] v ∈ seen, Fulfill γ v.

Definition Fulfilled (contracts : list (V → iProp Σ)) (seen : list V) : iProp Σ :=
  ∃ order_applied,
    ⌜Permutation seen order_applied⌝ ∗
    [∗ list] contract;v ∈ contracts;order_applied, contract v.

Definition is_mfuture (γ : mfuture_names) (ch : loc) : iProp Σ :=
  is_channel ch γ.(chan_name) ∗
  inv nroot (
    ∃ (s : chan_rep.t V),
      "Hch" ∷ own_channel ch s γ.(chan_name) ∗
      match s with
      | chan_rep.Buffered msgs => [∗ list] v ∈ msgs, Fulfill γ v
      | chan_rep.SndPending v => Fulfill γ v
      | chan_rep.SndCommit v => Fulfill γ v
      | chan_rep.Idle | chan_rep.RcvPending | chan_rep.RcvCommit => True
      | _ => False
      end
  )%I.

Lemma start_mfuture (ch : loc) (γ : chan_names) (s : chan_rep.t V) :
  is_channel ch γ -∗
  own_channel ch s γ -∗
  ⌜s = chan_rep.Idle ∨ s = chan_rep.Buffered []⌝ ={⊤}=∗
  ∃ γmf, is_mfuture γmf ch ∗ Await γmf [] [].
Proof.
  iIntros "#Hch Hoc %Hs".
  iMod (ghost_map_alloc_empty) as (γcontracts) "Hmap_full".
  set (γmf := {|
    chan_name := γ;
    contracts_name := γcontracts
  |}).
  iMod (inv_alloc nroot _ (
    ∃ s',
      "Hch" ∷ own_channel ch s' γ ∗
      match s' with
      | chan_rep.Buffered msgs => [∗ list] v ∈ msgs, Fulfill γmf v
      | chan_rep.SndPending v => Fulfill γmf v
      | chan_rep.SndCommit v => Fulfill γmf v
      | chan_rep.Idle | chan_rep.RcvPending | chan_rep.RcvCommit => True
      | _ => False
      end
  )%I with "[Hoc]") as "#Hinv".
  {
    iNext. iExists s. iFrame.
    destruct Hs as [-> | ->]; simpl; done.
  }
  iModIntro. iExists γmf.
  iSplitL ""; first by iFrame "#".
  unfold Await. iExists ∅.
  iFrame. iSplitL ""; first by iPureIntro; rewrite map_size_empty.
  iSplitL ""; first done.
  done.
Qed.

Lemma mfuture_alloc_promise γ ch (contract : V → iProp Σ) (contracts : list (V → iProp Σ)) (seen : list V) :
  is_mfuture γ ch -∗
  Await γ contracts seen ={⊤}=∗
  Promise γ contract ∗
  Await γ (contracts ++ [contract]) seen.
Proof.
  iIntros "#Hmf HAwait".
  unfold Await. iNamed "HAwait".
  iMod (saved_pred_alloc_cofinite (dom contracts_names) contract 1) as (prop_gname) "Hpred"; first done.
  iDestruct "Hpred" as "(%Hnin & Hpred1 & Hpred2)".
  iDestruct "HAwait" as "(Hnames & %Hcont & Hpromises & Hfulfilled)".
  iMod (ghost_map_insert prop_gname contract with "Hnames") as "[Hauth Hfrag]".
  { by apply not_elem_of_dom. }
  iDestruct "Hfrag" as "[Hfrag1 Hfrag2]".
  iFrame.
  iModIntro. simpl.
  iSplitR "".
  {
    iPureIntro. rewrite map_size_insert_None.
    - rewrite app_length /=. lia.
    - apply not_elem_of_dom. done.
  }
  iFrame.
Qed.

Lemma mfuture_fulfill_au γ ch (v : V) :
  ∀ (Φ: iProp Σ),
  is_mfuture γ ch -∗
  £1 ∗ £1 ∗ £1 ∗ Fulfill γ v -∗
  ▷ (True -∗ Φ) -∗
  send_au_slow ch v γ.(chan_name) Φ.
Proof.
  iIntros (Φ) "#Hmf (Hlc1 & Hlc2 & Hlc3 & HFulfill) Hau".
  rewrite /is_mfuture.
  iDestruct "Hmf" as "[#Hisch #Hinv]".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iExists s. iFrame "Hch".
  destruct s; try done.
  - iIntros "Hoc".
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc Hinv_open HFulfill]") as "_".
    {
      iNext. iFrame.
      rewrite big_sepL_app. iFrame. simpl. done.
    }
    iModIntro. iApply "Hau". done.
  - iIntros "Hoc".
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc HFulfill]") as "_".
    {
      iNext. iExists (chan_rep.SndPending v). iFrame.
    }
    iModIntro.
    unfold send_au_inner.
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
        iNext. iExists chan_rep.Idle. iFrame.
      }
      iModIntro. iApply "Hau". done.
  - iIntros "Hoc".
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc HFulfill]") as "_".
    {
      iNext. iExists (chan_rep.SndCommit v). iFrame.
    }
    iModIntro. iApply "Hau". done.
Qed.

Lemma wp_mfuture_fulfill γ ch (v : V) :
  {{{ is_mfuture γ ch ∗ Fulfill γ v }}}
    chan.send #t #ch #v
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(#Hmf & HFulfill) HΦ".
  rewrite /is_mfuture.
  iDestruct "Hmf" as "[#Hch #Hinv]".
  iApply (chan.wp_send ch v γ.(chan_name) with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & _)".
  iApply (mfuture_fulfill_au with "[$Hch $Hinv] [$Hlc1 $Hlc2 $Hlc3 $HFulfill]").
  done.
Qed.

Lemma mfuture_await_au γ ch (contracts : list (V → iProp Σ)) (seen : list V) :
  ∀ (Φ: V → bool → iProp Σ),
  is_mfuture γ ch -∗
  £1 ∗ £1 ∗ Await γ contracts seen -∗
  ▷ (∀ v, Await γ contracts (seen ++ [v]) -∗ Φ v true) -∗
  rcv_au_slow ch γ.(chan_name) (λ (v:V) (ok:bool), Φ v ok).
Proof.
  iIntros (Φ) "#Hmf (Hlc1 & Hlc2 & HAwait) Hau".
  rewrite /is_mfuture.
  iDestruct "Hmf" as "[#isHch #Hinv]".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iExists s. iFrame "Hch".
  destruct s; try done.
  - destruct buff as [|v_rcv msgs'] eqn:Hmsgs; simpl.
    + done.
    + iDestruct "Hinv_open" as "[HFulfill_v HFulfills]".
      iIntros "Hoc".
      iMod "Hmask".
      iMod ("Hinv_close" with "[Hoc HFulfills]") as "_".
      {
        iNext. iExists (chan_rep.Buffered msgs'). iFrame.
      }
      iModIntro.
      iApply "Hau".
      unfold Await. iNamed "HAwait".
      iExists contracts_names. iFrame.
      iDestruct "HAwait" as "(Hauth & %Hsize & Hcontracts & Hfulfilled)".
      iFrame.
      simpl.
      iSplitR ""; first by iPureIntro.
      done.
  - iIntros "Hoc".
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc]") as "_".
    {
      iNext. iExists chan_rep.RcvPending. iFrame.
    }
    iModIntro.
    iInv "Hinv" as "Hinv_open2" "Hinv_close2".
    iMod (lc_fupd_elim_later with "Hlc2 Hinv_open2") as "Hinv_open2".
    iNamed "Hinv_open2".
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask2"].
    iNext. iExists s. iFrame "Hch".
    destruct s; try done.
    + iIntros "Hoc".
      iMod "Hmask2".
      iMod ("Hinv_close2" with "[Hoc]") as "_".
      {
        iNext. iExists chan_rep.Idle. iFrame.
      }
      iModIntro.
      iApply "Hau".
      unfold Await. iNamed "HAwait".
      iExists contracts_names. iFrame.
      iDestruct "HAwait" as "(Hauth & %Hsize & Hcontracts & Hfulfilled)".
      iFrame.
      iSplitR ""; first done.
      done.
  - iIntros "Hoc".
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc]") as "_".
    {
      iNext. iFrame.
    }
    iModIntro.
    iApply "Hau".
    unfold Await. iNamed "HAwait".
    iExists contracts_names. iFrame.
    iDestruct "HAwait" as "(Hauth & %Hsize & Hcontracts & Hfulfilled)".
    iFrame.
    iSplitR ""; first done.
    done.
Qed.

Lemma wp_mfuture_await γ ch (contracts : list (V → iProp Σ)) (seen : list V) :
  {{{ is_mfuture γ ch ∗ Await γ contracts seen }}}
    chan.receive #t #ch
  {{{ (v : V), RET (#v, #true); Await γ contracts (seen ++ [v]) }}}.
Proof.
  iIntros (Φ) "(#Hmf & HAwait) HΦ".
  rewrite /is_mfuture.
  iDestruct "Hmf" as "[#Hch #Hinv]".
  iApply (chan.wp_receive ch γ.(chan_name) with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  iApply (mfuture_await_au with "[$Hch $Hinv] [$Hlc1 $Hlc2 $HAwait]").
  done.
Qed.

Lemma mfuture_complete γ ch (contracts : list (V → iProp Σ)) (seen : list V) :
  is_mfuture γ ch -∗
  Await γ contracts seen -∗
  ⌜length contracts = length seen⌝ ={⊤}=∗
  Fulfilled contracts seen.
Proof.
  iIntros "#Hmf HAwait %Hlen".
  unfold Await. iNamed "HAwait".
  iDestruct "HAwait" as "(Hauth & %Hsize & Hpromises & Hfulfills)".

  iAssert (∃ (order_applied : list V),
    ([∗ list] contract;v ∈ contracts;order_applied, contract v))%I
    with "[Hpromises Hfulfills]" as (order_applied) "Hpairs".
  {
    clear Hlen Hsize.
    iInduction contracts as [|c contracts'] "IH".
    - iExists []. simpl. done.
    - rewrite big_sepL_cons.
      iDestruct "Hpromises" as "[Hp Hrest]".
      unfold Promise.
      iDestruct "Hp" as (g) "[Hcont Hsp]".
      iDestruct ("IH" with "[$Hrest]") as "Hpairs".
    (* Not sure how to prove *)
    admit.
  }

  iModIntro.
  unfold Fulfilled.
  iExists order_applied.
  iFrame.
Admitted.

End mfuture.
