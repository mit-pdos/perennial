From New.proof Require Import proof_prelude.
From New.proof Require Import sync sync.atomic strings fmt
  chan_proof.closeable.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples.channel
  Require Import workq.

From New.proof.github_com.goose_lang.goose.model.channel Require Import idioms.
Import bag.
From New.proof Require Import chan_proof.closeable.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : workq.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) workq := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) workq := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop workq get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    workq.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init workq }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?). reflexivity. }
  iIntros "Hown". wp_auto.
  wp_apply (atomic.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (sync.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
Admitted.

Record x_names :=
  {
    docs : list go_string;
    task_gn : gname;
    done_gn : gname;
  }.

Definition own_task γ (doc : go_string) : iProp Σ :=
  ∃ (i : nat), i ↪[γ.(task_gn)] (Some doc).

(* A task being `None` means that `total` has it, but remaining hasn't been
   decremented yet. *)
Definition own_task_auth γ (remaining_docs : gmap nat (option go_string)) : iProp Σ :=
  ghost_map_auth γ.(task_gn) 1 remaining_docs.

Axiom word_count : ∀ (doc : go_string), nat.

Definition is_tasks_done γ total : iProp Σ :=
  own_Int64 total DfracDiscarded (W64 (sum_list (word_count <$> γ.(docs)))).

Definition is_coordinator γ (total remaining : loc) done : iProp Σ :=
  ∃ γdone,
  "#Hdone" ∷ own_closeable_chan done γdone (is_tasks_done γ total) closeable.Unknown ∗
  "#Hdone_is" ∷ is_chan done γdone unit ∗
  "#Hi" ∷ inv nroot (
      ∃ remaining_docs (remainingv : w64),
        "H" ∷ (if decide (remainingv = W64 0) then True
               else
                 ∃ totalv,
                   "Htotal" ∷ own_Int64 total (DfracOwn 1) totalv ∗
                   "Hdone" ∷ own_closeable_chan done γdone (is_tasks_done γ total) closeable.Open ∗
                   "%Htotal" ∷ ⌜ sint.nat totalv =
                   sum_list (imap (λ i doc, match (remaining_docs !! i) with
                                            | Some (Some _) => O
                                            | _ => word_count doc
                                            end) γ.(docs)) ⌝
          ) ∗

         "Hremaining" ∷ own_Int64 remaining (DfracOwn 1) remainingv ∗
         "H●" ∷ own_task_auth γ remaining_docs ∗
         "%Hremaining_size" ∷ ⌜ sint.nat remainingv = size remaining_docs ⌝ ∗
         "%Hsubset" ∷ ⌜ map_Forall (λ (i : nat) _, i < length γ.(docs)) remaining_docs ⌝
        ).

Definition is_Worker γ (w : loc) : iProp Σ :=
  ∃ wv γsteal γqueue,
  "#w" ∷ w ↦□ wv ∗
  "#Hqueue_is" ∷ is_chan wv.(workq.Worker.queue') γqueue go_string ∗
  "#Hqueue" ∷ is_chan_bag γqueue wv.(workq.Worker.queue') (own_task γ) ∗
  "#Hsteal_is" ∷ is_chan wv.(workq.Worker.steal') γsteal chan.t ∗
  "#Hsteal" ∷ is_chan_bag γsteal wv.(workq.Worker.steal')
    (λ (reply : chan.t),
       ∃ γreply, is_chan_bag γreply reply
                   (λ (maybe_req : loc), if decide (maybe_req = null) then True
                                         else ∃ req, maybe_req ↦ req ∗ own_task γ req
                   )
    ).

Axiom wp_strings_Fields :
  ∀ `{!strings.Assumptions} (s : go_string),
  {{{ is_pkg_init strings }}}
    @! strings.Fields #s
  {{{ sl (ss : list go_string), RET #sl; sl ↦* ss ∗ ⌜ length ss = word_count s ⌝ }}}.

Lemma wp_Worker__process γ w doc total remaining done :
  {{{
        is_pkg_init workq ∗
        "#Hw" ∷ is_Worker γ w ∗
        "#Hcoord" ∷ is_coordinator γ total remaining done ∗
        "Hdoc" ∷ own_task γ doc
  }}}
    w @! (go.PointerType workq.Worker) @! "process" #doc #total #remaining #done
  {{{
        RET #(); True
  }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto.
  wp_apply wp_strings_Fields as "* [Hsl %]".
  iDestruct (own_slice_len with "Hsl") as %Hlen.
  iNamed "Hcoord".

  wp_apply wp_Int64__Add. iInv "Hi" as "H" "Hclose".
  iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iNext. iNamedSuffix "H" "inv".
  iDestruct "Hdoc" as "(% & Hdoc)".
  iCombine "H●inv Hdoc" gives %Hlookup.
  destruct decide.
  { exfalso. subst.
    symmetry in Hremaining_sizeinv.
    apply map_size_empty_inv in Hremaining_sizeinv.
    subst. done. }
  iNamedSuffix "Hinv" "inv". iFrame. iIntros "Htotal_inv".
  iMod (ghost_map_update None with "H●inv Hdoc") as "[H●inv Hdoc]".
  iCombineNamed "*inv" as "H".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[H]") as "_".
  {
    iNamed "H". iFrame. destruct decide; first done. iFrame.
    iPureIntro.
    split_and!.
    - destruct Hlen as [Hlen ?].
      replace (sint.nat _) with
        (sint.nat totalv + length ss)%nat.
      2:{ admit. (* TODO: overflow *) }
      admit.
      (* TODO: pure fact *)
    - rewrite map_size_insert_Some //.
    - apply map_Forall_insert_2; try done.
      by eapply map_Forall_lookup_1 in Hsubsetinv.
  }
  iModIntro.
  wp_auto.

  wp_apply wp_Int64__Add. iInv "Hi" as "H" "Hclose".
  iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iNext. iNamedSuffix "H" "inv". iFrame. iIntros "Hremaining_inv".
  iCombine "H●inv Hdoc" gives %?.
  iMod (ghost_map_delete with "H●inv Hdoc") as "H●inv".

  pose proof (map_size_ne_0_lookup_2 remaining_docs0 i ltac:(done)).
  destruct decide.
  { exfalso. word. }

  destruct (decide (w64_word_instance.(word.add) remainingv0 (W64 (- (1))) = W64 0)).
  - (* about to close done. *)
    iNamedSuffix "Hinv" "done".
    iCombineNamed "*inv" as "H".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[H]") as "_".
    {
      iNamed "H". iFrame "∗#%". destruct decide; last done.
      iFrame "#".
      iPureIntro. split_and!.
      - done.
      - rewrite map_size_delete_Some //.
        word.
      - apply map_Forall_delete. done.
    }
    iModIntro. wp_auto. wp_if_destruct.
    2:{ exfalso. done. }
    iPersist "Htotaldone".
    wp_apply (wp_closeable_chan_close with "[Hdonedone]").
    { iFrame. iModIntro.
      rewrite /is_tasks_done.
      iExactEq "Htotaldone".
      f_equal.
      admit. (* TODO: pure reasoning. remaining_docs0 was a singleton with value
                (Some None), so everything was already counted *)
    }
    iIntros "#Hcl".
    wp_auto. wp_end.
  - (* not going to close done *)
    iNamedSuffix "Hinv" "inv".
    iCombineNamed "*inv" as "H".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[H]") as "_".
    { iNamed "H". iFrame "∗#%".
      rewrite decide_False //.
      iFrame. iPureIntro. split_and!.
      - admit. (* TODO: pure, deleting an entry that used to be "Some None" makes no difference  *)
      - rewrite map_size_delete_Some //.
        word.
      - apply map_Forall_delete. done.
    }
    iModIntro. wp_auto. wp_if_destruct.
    { exfalso. done. }
    wp_end.
Admitted.

Lemma wp_Worker__run γ w neighbor total remaining done (wg : loc) :
  {{{
        is_pkg_init workq ∗
        "#Hw" ∷ is_Worker γ w ∗
        "#Hneighbor" ∷ is_Worker γ neighbor ∗
        "#Hcoord" ∷ is_coordinator γ total remaining done ∗
        "Hwg" ∷ join.own_Done wg (is_tasks_done γ total)
  }}}
    w @! (go.PointerType workq.Worker) @! "run" #neighbor #total #remaining #done #wg
  {{{
        RET #(); True
  }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_apply wp_with_defer as "%defer defer". simpl subst.
  wp_auto.
  wp_for.
  iNamedSuffix "Hw" "w".
  wp_auto_lc 2.
  wp_apply chan.wp_select_nonblocking.
  iSplit.
  {
    rewrite big_andL_cons.
    iSplit.
    { (* done. *)
      iNamedSuffix "Hcoord" "coord".
      repeat iExists _. iSplitR; first done. iFrame "#".
      iApply blocking_rcv_implies_nonblocking. (* TODO: rename lemma to use `recv`. *)
      iApply (closeable_chan_receive with "[$]").
      iIntros "[#H●_done Hclosed]".
      wp_auto. wp_for_post.
      wp_apply (join.wp_WaitGroup__Done with "[$Hwg]").
      { iFrame "#". }
      wp_end.
    }
    rewrite big_andL_cons.
    iSplit.
    { (* get a request *)
      repeat iExists _. iSplitR; first done. iFrame "#".
      iApply blocking_rcv_implies_nonblocking.
      iApply (bag_recv_au with "[$]").
      { iFrame "#". }
      iNext. iIntros "%v Hv". simpl subst.
      wp_auto. wp_apply (wp_Worker__process with "[Hv]").
      { iFrame "∗#". }
      wp_for_post. iFrame.
    }
    rewrite big_andL_cons.
    iSplit.
    { (* help a worker steal from this one. *)
      repeat iExists _. iSplitR; first done. iFrame "#".
      iApply blocking_rcv_implies_nonblocking.
      iApply (bag_recv_au with "[$]").
      { iFrame "#". }
      iNext. iIntros "%reply_ch #Hreply_ch". simpl subst.
      wp_auto_lc 2.
      wp_apply chan.wp_select_nonblocking.
      iSplit.
      - (* got a piece of work. *)
        rewrite big_andL_singleton.
        repeat iExists _. iSplitR; first done. iFrame "#".
        iApply blocking_rcv_implies_nonblocking.
        iApply (bag_recv_au with "[$]").
        { iFrame "#". }
        iNext. iIntros "%v Hv".
        (* FIXME: translation bug with nested selects with receive. *)
        replace (Fst (#reply_ch, #true)%V)%E with (Fst "$recvVal") by admit.
        simpl subst.
        wp_auto_lc 2.
        iDestruct "Hreply_ch" as "(% & #Hreply_ch)".
        wp_apply (wp_bag_send with "[Hv doc]").
        { iFrame "#∗". destruct decide; first done. iFrame. }
        wp_for_post.
        iFrame.
      - (* no work, so send nil *)
        wp_auto.
        iDestruct "Hreply_ch" as "(% & #Hreply_ch)".
        wp_apply (wp_bag_send with "[]").
        { iFrame "#∗". }
        wp_for_post.
        iFrame.
    }
    rewrite big_andL_nil. done.
  }
  { (* default case; try to steal *)
    wp_auto.
    wp_apply chan.wp_make2 as "%reply %γreply (#Hreply_is & _ & Hown)"; first done.
    iNamedSuffix "Hneighbor" "neighbor".
    wp_auto_lc 2.
    iMod (start_bag with "Hreply_is Hown") as "#Hreply".
    { done. }
    wp_apply chan.wp_select_blocking.
    rewrite big_andL_cons. iSplit.
    { (* done. *)
      iNamedSuffix "Hcoord" "coord".
      repeat iExists _. iSplitR; first done. iFrame "#".
      iApply (closeable_chan_receive with "[$]").
      iIntros "[#H●_done Hclosed]".
      wp_auto. wp_for_post.
      wp_apply (join.wp_WaitGroup__Done with "[$Hwg]").
      { iFrame "#". }
      wp_end.
    }
    rewrite big_andL_cons. iSplit.
    { (* request to steal was sent *)
      iNamedSuffix "Hcoord" "coord".
      repeat iExists _. iSplitR; first done. iFrame "#".
      iApply (bag_send_au with "[$]").
      { iFrame "#". }
      { iFrame "#". }
      iNext. wp_auto.
      wp_apply (wp_bag_receive with "[$]") as "%v Hv".
      wp_if_destruct.
      { wp_for_post. iFrame. }
      rewrite decide_False //.
      iDestruct "Hv" as "(% & ? & Hv)".
      wp_auto. wp_apply (wp_Worker__process with "[Hv]").
      { iFrame "∗ ww #". }
      wp_for_post. iFrame.
    }
    rewrite big_andL_cons. iSplit.
    { (* received local work while trying to steal. *)
      repeat iExists _. iSplitR; first done. iFrame "#".
      iApply (bag_recv_au with "[$]").
      { iFrame "#". }
      iNext. wp_auto. iIntros "%v Hv". simpl subst.
      wp_auto. wp_apply (wp_Worker__process with "[Hv]").
      { iFrame "∗ ww #". }
      wp_for_post. iFrame.
    }
    rewrite big_andL_nil. done.
  }
Admitted.

End wps.
