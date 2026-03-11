From New.proof Require Import proof_prelude.
From New.proof Require Import sync.atomic strings fmt
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
Admitted.

Record workq_names :=
  {
    docs : list go_string;
    task_gn : gname;
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
  "#Hqueue" ∷ is_chan_bag γqueue wv.(workq.Worker.queue') (own_task γ) ∗
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

Lemma wp_Worker__run γ w neighbor total remaining done :
  {{{
        is_pkg_init workq ∗
        "#Hw" ∷ is_Worker γ w ∗
        "#Hneighbor" ∷ is_Worker γ neighbor ∗
        "#Hcoord" ∷ is_coordinator γ total remaining done
  }}}
    w @! (go.PointerType workq.Worker) @! "run" #neighbor #total #remaining #done
  {{{
        RET #(); True
  }}}.
Proof.
  wp_start as "@". wp_auto.
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
      wp_end.
    }
    rewrite big_andL_cons.
    iSplit.
    { (* get a request *)
      repeat iExists _. iSplitR; first done. iFrame "#".
      iDestruct (is_bag_is_chan with "[]") as "$"; first iFrame "#".
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
      iDestruct (is_bag_is_chan with "[]") as "$"; first iFrame "#".
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
        iDestruct (is_bag_is_chan with "[]") as "$"; first iFrame "#".
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
      wp_end.
    }
    rewrite big_andL_cons. iSplit.
    { (* request to steal was sent *)
      iNamedSuffix "Hcoord" "coord".
      repeat iExists _. iSplitR; first done. iFrame "#".
      iDestruct (is_bag_is_chan with "[]") as "$"; first iFrame "#".
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
      iDestruct (is_bag_is_chan with "[]") as "$"; first iFrame "#".
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

Lemma wp_wordCount docs_sl docs :
  {{{ is_pkg_init workq ∗ "Hdocs" ∷ docs_sl ↦* docs }}}
    @! workq.wordCount #docs_sl
  {{{ RET #(W64 (sum_list (word_count <$> docs))); True }}}.
Proof.
  wp_start as "@". wp_auto.
  iDestruct (own_slice_len with "Hdocs") as %[Hdocs_len ?].
  wp_if_destruct.
  { wp_end. destruct docs; simpl in *; (done || word). }

  set (numWorkers:=W64 2).
  wp_apply wp_slice_make2 as "%workers_sl [workers_sl _]".
  { subst numWorkers. word. }
  iDestruct (own_slice_len with "workers_sl") as %Hworkers_len.
  rewrite length_replicate in Hworkers_len.
  rename i_ptr into j_ptr. iRename "i" into "j".
  wp_auto.

  iMod (ghost_map_alloc (map_seq O (Some <$> docs))) as (γtask_gn) "[H● Htasks]".

  set (γ:={| docs := docs; task_gn := γtask_gn |}).
  iAssert (
      ∃ (i j : w64) workers,
        "i" ∷ i_ptr ↦ i ∗
        "j" ∷ j_ptr ↦ j ∗
        "workers_sl" ∷
          workers_sl ↦* (workers ++ replicate (sint.nat numWorkers - sint.nat i) (zero_val loc)) ∗
        "#Hworkers" ∷ □(∀ w, ⌜ w ∈ workers ⌝ → is_Worker γ w) ∗
        "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z numWorkers ⌝
    )%I with "[i j workers_sl]" as "HH".
  { iFrame. rewrite Nat.sub_0_r. iExists [].
    iFrame. iSplit; last done.
    iIntros "!# * %Hbad". exfalso. rewrite elem_of_nil // in Hbad. }
  wp_for "HH".
  wp_if_destruct.
  { (* inside loop *)
    rewrite -> decide_True.
    2: word.
    iDestruct (own_slice_len with "workers_sl") as %Hworkers_len'.
    rewrite length_app length_replicate in Hworkers_len'.
    wp_apply (wp_load_slice_index with "[workers_sl]").
    { word. }
    { iFrame. rewrite lookup_app_r; last word.
      rewrite lookup_replicate_2 //. subst numWorkers.
      word. }
    iIntros "workers_sl". wp_auto.
    wp_apply chan.wp_make2 as "%queue %γqueue queue"; first done.
    wp_apply chan.wp_make1 as "%steal %γsteal steal".
    wp_alloc wr as "wr". wp_auto.

    iPersist "wr".
    iAssert (|={⊤}=> is_Worker γ wr)%I with "[queue steal]" as ">#Hwr".
    {
      iFrame "#".
      iDestruct "queue" as "(#? & % & q)".
      iDestruct "steal" as "(#? & % & s)".
      iMod (start_bag with "[] q") as "$".
      { by destruct decide. }
      { iFrame "#". }
      iMod (start_bag with "[] s") as "$".
      { done. }
      { iFrame "#". }
      done.
    }

    rewrite -> (decide_True (P:=(_ ≤ _ < _)%Z)).
    2:{ subst numWorkers. word. }
    wp_auto.
    wp_apply (wp_store_slice_index with "[workers_sl]").
    { iFrame. len. }
    iIntros "workers_sl". wp_auto.
    wp_for_post.
    iFrame. iExists (workers ++ [wr]).
    iSplitL "workers_sl".
    { rewrite /named. iExactEq "workers_sl".
      f_equal.
      replace (sint.nat numWorkers - sint.nat i)%nat with
        (S (sint.nat numWorkers - sint.nat i - 1))%nat by word.
      simpl.
      rewrite list_insert_middle; last word.
      rewrite -app_assoc.
      f_equal. f_equal.
      f_equal. word.
    }
    iSplitL.
    {
      iModIntro. iIntros "%w %Hw".
      rewrite elem_of_app in Hw. destruct Hw as [?|Hw].
      { iApply "Hworkers". done. }
      rewrite list_elem_of_singleton in Hw. subst.
      iFrame "#".
    }
    word.
  }

  replace (sint.nat numWorkers - sint.nat i)%nat with O by word.
  clear dependent j i.
  rewrite app_nil_r.
  iDestruct (own_slice_len with "workers_sl") as "%Hworkers_len'".

  iAssert (
      ∃ (i : w64) (_unused_doc : go_string),
        "doc" ∷ doc_ptr ↦ _unused_doc ∗
        "i" ∷ i_ptr ↦ i ∗
        "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z docs_sl.(slice.len) ⌝ ∗
        "Htasks" ∷ [∗ list] doc ∈ (drop (sint.nat i) docs), own_task γ doc
    )%I with "[i Htasks doc]" as "HH".
  { iFrame. rewrite drop_0. iSplitR; first word.
    rewrite big_sepM_map_seq.
    rewrite big_sepL_fmap.
    iApply (big_sepL_impl with "Htasks").
    iIntros "!# * %Hin $". }
  wp_for "HH".
  wp_if_destruct.
  { (* loop iteration *)
    rewrite -> decide_True; last word.
    list_elem docs (sint.nat i) as doc.
    wp_apply (wp_load_slice_index with "[$Hdocs]").
    { word. }
    { done. }
    iIntros "Hdocs".
    wp_auto.
    list_elem workers O as w.
    { subst numWorkers. word. }
    rewrite -> decide_True.
    2:{ subst numWorkers. word. }
    wp_apply (wp_load_slice_index with "[$workers_sl]").
    { word. }
    { done. }
    iIntros "workers_sl".
    wp_auto.
    iDestruct ("Hworkers" $! w with "[%]") as "H".
    { apply list_elem_of_lookup_2 in Hw_lookup. done. }
    iNamed "H".
    wp_auto.
    erewrite drop_S; last done.
    iDestruct "Htasks" as "[Hdoc Htasks]".
    wp_apply (wp_bag_send with "[Hdoc]").
    { iFrame "#∗". }
    wp_for_post.
    iFrame.
    replace (sint.nat (word.add _ _)) with (S (sint.nat i)) by word.
    iFrame. word.
  }
  wp_apply wp_Int64__Store.
  iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iNext. iFrame. iIntros "remaining". iMod "Hmask" as "_". iModIntro.
  wp_auto.
  wp_apply chan.wp_make1 as "%done %γdone (#Hdone_is & % & Hdone)".

  iAssert (|={⊤}=> is_coordinator γ total_ptr remaining_ptr done)%I
            with "[Hdone H● total remaining]" as ">#Hcoord".
  {
    iMod (alloc_closeable_chan with "[$] [$]") as "Hopen".
    iDestruct (own_closeable_chan_Unknown with "Hopen") as "#$".
    iFrame "#".
    iMod (inv_alloc with "[-]") as "$"; last done.
    iFrame. iSplitL "Hopen total".
    { destruct decide; iFrame; try done.
      iPureIntro.
      admit. (* TODO: pure reasoning *) }
    iPureIntro.
    admit. (* TODO: pure reasoning about map_seq. *)
  }

  rename i_ptr into j_ptr. iRename "i" into "j".
  wp_auto.
  iClear "Htasks". clear dependent i.
  iAssert (
      ∃ (i j : w64) (_unused_w : loc),
        "w" ∷ w_ptr ↦ _unused_w ∗
        "i" ∷ i_ptr ↦ i ∗
        "j" ∷ j_ptr ↦ j ∗
        "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ length workers ⌝
    )%I with "[i w j]" as "HH".
  { iFrame. word. }
  wp_for "HH".
  wp_if_destruct.
  { (* inside loop *)
    rewrite -> decide_True.
    2:{ word. }
    wp_bind.
    list_elem workers (sint.nat i) as w.
    wp_apply (wp_load_slice_index with "[$workers_sl]") as "workers_sl".
    { word. }
    { done. }

    rewrite -> decide_True.
    2:{ subst numWorkers. admit. (* TODO: pure reasoning about modulo *) }
    list_elem workers
    (sint.Z (w64_word_instance.(word.mods) (w64_word_instance.(word.add) i (W64 1)) (W64 2))) as
    neighbor.
    { admit. (* TODO; pure reasoning about modulo *)}
    wp_apply (wp_load_slice_index with "[$workers_sl]") as "workers_sl".
    { admit. (* TODO: pure reasoning about modulo *) }
    { done. }
    iDestruct ("Hworkers" $! w with "[%]") as "#Hw".
    { by apply list_elem_of_lookup_2 in Hw_lookup. }
    iDestruct ("Hworkers" $! neighbor with "[%]") as "#Hn".
    { by apply list_elem_of_lookup_2 in Hneighbor_lookup. }
    wp_apply (wp_fork with "[]").
    { wp_apply (wp_Worker__run with "[]"); iFrame "#". }
    wp_for_post. iFrame. word.
  }
  iNamedSuffix "Hcoord" "coord".
  wp_apply (chan.wp_receive with "[$]") as "_".
  iApply (closeable_chan_receive with "[$]").
  iIntros "[#Htotal #Hclosed]".
  wp_auto. wp_apply wp_Int64__Load.
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iFrame "#". iNext. iIntros "?". iMod "Hmask" as "_".
  iModIntro. wp_auto.
  wp_end.
Admitted.

End wps.
