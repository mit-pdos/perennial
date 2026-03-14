From New.proof Require Import proof_prelude.

From New.proof Require Import sync.atomic strings fmt
  github_com.goose_lang.goose.model.channel.idiom.closeable.closeable.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples.channel
  Require Import workq.

From New.proof.github_com.goose_lang.goose.model.channel Require Import idioms.
Import bag.
From New.proof Require Import github_com.goose_lang.goose.model.channel.idiom.closeable.closeable.

Local Lemma map_seq_size {A : Type} (start : nat) (xs : list A) :
  size (map_seq start xs : gmap nat A) = length xs.
Proof.
  revert start. induction xs as [|x xs IH]; intros start.
  - done.
  - rewrite map_seq_cons.
    rewrite map_size_insert_None.
    2:{ apply map_seq_cons_disjoint. }
    rewrite IH. done.
Qed.

Local Lemma mods_2_bound (i : w64) :
  0 ≤ sint.Z i →
  sint.Z i < 2 →
  0 ≤ sint.Z (w64_word_instance.(word.mods) (w64_word_instance.(word.add) i (W64 1)) (W64 2)) ∧
  sint.Z (w64_word_instance.(word.mods) (w64_word_instance.(word.add) i (W64 1)) (W64 2)) < 2.
Proof.
  intros.
  rewrite word.signed_mods_nowrap; try word.
  pose proof (Z.rem_bound_pos (sint.Z (word.add i (W64 1))) 2 ltac:(word) ltac:(word)).
  word.
Qed.

(* When all entries in remaining_docs are Some (Some _), the imap sum is 0 *)
Local Lemma imap_sum_all_some {A : Type} (f : A → nat) (docs : list A) (remaining_docs : gmap nat (option A)) :
  (∀ (i : nat), (i < length docs)%nat → ∃ d, remaining_docs !! i = Some (Some d)) →
  sum_list (imap (λ i doc, match remaining_docs !! i with | Some (Some _) => O | _ => f doc end) docs) = 0%nat.
Proof.
  intros Hlookup.
  transitivity (sum_list (replicate (length docs) 0%nat)).
  2:{ rewrite sum_list_replicate. lia. }
  f_equal. apply list_eq. intros j.
  rewrite list_lookup_imap.
  destruct (docs !! j) eqn:Hdoc.
  - simpl.
    assert ((j < length docs)%nat) as Hlt.
    { apply lookup_lt_is_Some_1. eauto. }
    destruct (Hlookup j Hlt) as [d ->].
    symmetry. apply lookup_replicate_2. lia.
  - symmetry.
    apply lookup_ge_None_1 in Hdoc.
    apply lookup_ge_None_2.
    rewrite length_replicate. lia.
Qed.

Local Lemma imap_sum_no_some_some {A : Type} (f : A → nat) (docs : list A) (remaining_docs : gmap nat (option A)) :
  (∀ (i : nat), (i < length docs)%nat → ∀ d, remaining_docs !! i ≠ Some (Some d)) →
  sum_list (imap (λ i doc, match remaining_docs !! i with | Some (Some _) => O | _ => f doc end) docs) =
  sum_list (f <$> docs).
Proof.
  intros Hno_some.
  f_equal. apply list_eq. intros j.
  rewrite list_lookup_imap list_lookup_fmap.
  destruct (docs !! j) eqn:Hdoc; simpl; last done.
  f_equal. destruct (remaining_docs !! j) as [[d|]|] eqn:Hlook; try done.
  exfalso. eapply (Hno_some j); [eapply lookup_lt_Some; eauto | eauto].
Qed.

Local Lemma sum_list_le (l1 l2 : list nat) :
  length l1 = length l2 →
  (∀ i x y, l1 !! i = Some x → l2 !! i = Some y → x ≤ y)%nat →
  (sum_list l1 ≤ sum_list l2)%nat.
Proof.
  revert l2. induction l1 as [|a l1 IH]; intros [|b l2] Hlen Hle; simpl in *; try lia.
  assert (a ≤ b)%nat by (eapply (Hle 0%nat); done).
  assert (sum_list l1 ≤ sum_list l2)%nat.
  { apply IH; [lia | intros i x y Hx Hy; eapply (Hle (S i)%nat); done]. }
  lia.
Qed.

Local Lemma imap_sum_le {A : Type} (f : A → nat) (docs : list A) (remaining_docs : gmap nat (option A)) :
  (sum_list (imap (λ i doc, match remaining_docs !! i with | Some (Some _) => O | _ => f doc end) docs) ≤
   sum_list (f <$> docs))%nat.
Proof.
  apply sum_list_le.
  - rewrite length_imap length_fmap. done.
  - intros i x y. rewrite list_lookup_imap list_lookup_fmap.
    destruct (docs !! i); simpl; [|done].
    intros [= <-] [= <-].
    destruct (remaining_docs !! i) as [[?|]|]; simpl; lia.
Qed.

(* Inserting None at position i changes only that position's contribution *)
Local Lemma imap_sum_insert_none {A : Type} (f : A → nat) (docs : list A) (remaining_docs : gmap nat (option A)) (i : nat) doc :
  remaining_docs !! i = Some (Some doc) →
  (i < length docs)%nat →
  docs !! i = Some doc →
  sum_list (imap (λ i0 doc0, match (<[i:=None]> remaining_docs) !! i0 with | Some (Some _) => O | _ => f doc0 end) docs) =
  (sum_list (imap (λ i0 doc0, match remaining_docs !! i0 with | Some (Some _) => O | _ => f doc0 end) docs) + f doc)%nat.
Proof.
  intros Hlookup Hlt Hdoc.
  (* The two lists differ only at position i: old has 0, new has f doc *)
  (* new list = alter (λ _, f doc) i old_list *)
  set (nl := imap _ docs).
  set (ol := imap _ docs).
  assert (nl !! i = Some (f doc)) as Hnew.
  { subst nl. rewrite list_lookup_imap Hdoc /= lookup_insert.
    rewrite decide_True //. }
  assert (ol !! i = Some 0%nat) as Hold.
  { subst ol. rewrite list_lookup_imap Hdoc /= Hlookup //. }
  assert (∀ j : nat, j ≠ i → nl !! j = ol !! j) as Hother.
  { intros j Hne. subst nl ol. rewrite !list_lookup_imap.
    destruct (docs !! j); simpl; last done.
    f_equal. rewrite lookup_insert_ne; [done | lia]. }
  (* Use take_drop_middle to split *)
  rewrite -(take_drop_middle nl i (f doc) Hnew).
  rewrite -(take_drop_middle ol i 0%nat Hold).
  assert (take i nl = take i ol) as ->.
  { apply list_eq. intros j. rewrite !lookup_take.
    destruct (decide ((j < i)%nat)); [|done].
    apply Hother. lia. }
  assert (drop (S i) nl = drop (S i) ol) as ->.
  { apply list_eq. intros j. rewrite !lookup_drop. apply Hother. lia. }
  clear -f. induction (take i ol); simpl; [|rewrite IHl]; lia.
Qed.

(* Deleting a None entry doesn't change the imap sum *)
Local Lemma imap_sum_delete_none {A : Type} (f : A → nat) (docs : list A) (remaining_docs : gmap nat (option A)) (i : nat) :
  remaining_docs !! i = Some None →
  sum_list (imap (λ i0 doc0, match (delete i remaining_docs) !! i0 with | Some (Some _) => O | _ => f doc0 end) docs) =
  sum_list (imap (λ i0 doc0, match remaining_docs !! i0 with | Some (Some _) => O | _ => f doc0 end) docs).
Proof.
  intros Hlookup.
  f_equal. apply list_eq. intros j.
  rewrite !list_lookup_imap.
  destruct (docs !! j) eqn:Hdoc; simpl; last done.
  f_equal. destruct (decide (i = j)) as [->|Hne].
  - rewrite lookup_delete Hlookup /= decide_True //.
  - rewrite lookup_delete_ne; [done | lia].
Qed.

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
  wp_apply (strings.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

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

Definition is_tasks_done γ (sh : workq.shared.t) : iProp Σ :=
  own_Int64 sh.(workq.shared.total') DfracDiscarded (W64 (sum_list (word_count <$> γ.(docs)))).

Definition is_coordinator γ (sh : workq.shared.t) : iProp Σ :=
  let total := sh.(workq.shared.total') in
  let remaining := sh.(workq.shared.remaining') in
  let done := sh.(workq.shared.done') in
  ∃ γdone,
  "#Hdone" ∷ own_closeable_chan done γdone (is_tasks_done γ sh) closeable.Unknown ∗
  "#Hdone_is" ∷ is_chan done γdone unit ∗
  "#Hi" ∷ inv nroot (
      ∃ remaining_docs (remainingv : w64),
        "H" ∷ (if decide (remainingv = W64 0) then True
               else
                 ∃ totalv,
                   "Htotal" ∷ own_Int64 total (DfracOwn 1) totalv ∗
                   "Hdone" ∷ own_closeable_chan done γdone (is_tasks_done γ sh) closeable.Open ∗
                   "%Htotal" ∷ ⌜ sint.nat totalv =
                   sum_list (imap (λ i doc, match (remaining_docs !! i) with
                                            | Some (Some _) => O
                                            | _ => word_count doc
                                            end) γ.(docs)) ⌝ ∗
                   "%Htotal_nonneg" ∷ ⌜ (0 ≤ sint.Z totalv)%Z ⌝
          ) ∗

         "Hremaining" ∷ own_Int64 remaining (DfracOwn 1) remainingv ∗
         "H●" ∷ own_task_auth γ remaining_docs ∗
         "%Hremaining_size" ∷ ⌜ sint.nat remainingv = size remaining_docs ⌝ ∗
         "%Hdocs_agree" ∷ ⌜ map_Forall (λ (i : nat) (v : option go_string), match v with Some doc => γ.(docs) !! i = Some doc | None => True end) remaining_docs ⌝ ∗
         "%Hoverflow" ∷ ⌜ (Z.of_nat (sum_list (word_count <$> γ.(docs))) < 2^63)%Z ⌝
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

Lemma wp_Worker__process γ w doc sh :
  {{{
        is_pkg_init workq ∗
        "#Hw" ∷ is_Worker γ w ∗
        "#Hcoord" ∷ is_coordinator γ sh ∗
        "Hdoc" ∷ own_task γ doc
  }}}
    w @! (go.PointerType workq.Worker) @! "process" #doc #sh
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
      2:{
        assert (γ.(docs) !! i = Some doc) as Hdoc_i'.
        { eapply map_Forall_lookup_1 in Hdocs_agreeinv; [|exact Hlookup]. simpl in Hdocs_agreeinv. done. }
        pose proof (imap_sum_le word_count γ.(docs) (<[i:=None]> remaining_docs)) as Hle.
        rewrite (imap_sum_insert_none word_count _ _ _ _ Hlookup) in Hle;
          [| eapply lookup_lt_Some; eauto | done].
        rewrite -Htotalinv -H in Hle.
        rewrite Hlen.
        word. }
      assert (γ.(docs) !! i = Some doc) as Hdoc_i.
      { eapply map_Forall_lookup_1 in Hdocs_agreeinv; [|exact Hlookup]. simpl in Hdocs_agreeinv. done. }
      rewrite Htotalinv. rewrite H.
      rewrite (imap_sum_insert_none word_count _ _ _ _ Hlookup).
      { lia. }
      { eapply lookup_lt_Some. eauto. }
      { done. }
      (* TODO: pure fact *)
    - (* 0 ≤ sint.Z (word.add totalv sl.len) *)
      assert (γ.(docs) !! i = Some doc) as Hdoc_i'.
      { eapply map_Forall_lookup_1 in Hdocs_agreeinv; [|exact Hlookup]. simpl in Hdocs_agreeinv. done. }
      pose proof (imap_sum_le word_count γ.(docs) (<[i:=None]> remaining_docs)) as Hle'.
      rewrite (imap_sum_insert_none word_count _ _ _ _ Hlookup) in Hle';
        [| eapply lookup_lt_Some; eauto | done].
      rewrite -Htotalinv in Hle'. word.
    - rewrite map_size_insert_Some //.
    - apply map_Forall_insert_2; [done|].
      eapply map_Forall_impl; [apply Hdocs_agreeinv|].
      intros k v Hv. destruct v; done.
    - done.
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
      (* remaining_docs0 is a singleton {[i := None]}, so no entry is Some (Some _) *)
      rewrite (imap_sum_no_some_some word_count) in Htotaldone.
      2:{ intros j Hj d Habs.
          (* remaining_docs0 has size 1 (from e : remainingv0 + (-1) = 0) *)
          assert (size remaining_docs0 = 1)%nat as Hsize1.
          { assert (sint.nat remainingv0 = 1)%nat by word. lia. }
          (* Since size=1 and remaining_docs0 !! i = Some None, it must be {[i := None]} *)
          destruct (decide (j = i)) as [->|Hne].
          - rewrite H0 in Habs. done.
          - (* j ≠ i, but map has size 1 with key i, so j not in map *)
            assert (remaining_docs0 !! j = None) as Hnone.
            { apply not_elem_of_dom. intros Hin.
              assert ({[i]} = dom remaining_docs0) as Hdom.
              { apply set_eq. intros k. split.
                - intros Hk. rewrite elem_of_singleton in Hk. subst.
                  apply elem_of_dom. eauto.
                - intros Hk. apply elem_of_singleton.
                  assert (size (dom remaining_docs0) = 1)%nat as Hdomsize.
                  { rewrite size_dom. done. }
                  apply size_1_elem_of in Hdomsize. destruct Hdomsize as [x Hx].
                  assert (i ∈ dom remaining_docs0) by (apply elem_of_dom; eauto).
                  rewrite Hx in H2. rewrite elem_of_singleton in H2.
                  rewrite Hx in Hk. rewrite elem_of_singleton in Hk.
                  congruence. }
              rewrite -Hdom in Hin. rewrite elem_of_singleton in Hin. done. }
            rewrite Hnone in Habs. done. }
      word. }
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
      - rewrite (imap_sum_delete_none word_count _ _ _ H0). done.
      - done.
      - rewrite map_size_delete_Some //.
        word.
      - apply map_Forall_delete. done.
    }
    iModIntro. wp_auto. wp_if_destruct.
    { exfalso. done. }
    wp_end.
Qed.

Lemma wp_Worker__run γ w neighbor sh :
  {{{
        is_pkg_init workq ∗
        "#Hw" ∷ is_Worker γ w ∗
        "#Hneighbor" ∷ is_Worker γ neighbor ∗
        "#Hcoord" ∷ is_coordinator γ sh
  }}}
    w @! (go.PointerType workq.Worker) @! "run" #neighbor #sh
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
Qed.

Lemma wp_wordCount docs_sl docs :
  {{{ is_pkg_init workq ∗ "Hdocs" ∷ docs_sl ↦* docs ∗
      "%Hoverflow" ∷ ⌜ (Z.of_nat (sum_list (word_count <$> docs)) < 2^63)%Z ⌝ }}}
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
  wp_bind. wp_alloc remaining_ptr as "remaining". wp_auto.
  wp_bind. wp_alloc total_ptr as "total". wp_auto.
  wp_apply chan.wp_make1 as "%done %γdone (#Hdone_is & % & Hdone)".
  wp_apply wp_Int64__Store.
  iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iNext. iFrame. iIntros "remaining". iMod "Hmask" as "_". iModIntro.
  wp_auto.

  set (sh := workq.shared.mk remaining_ptr total_ptr done).
  iAssert (|={⊤}=> is_coordinator γ sh)%I
            with "[Hdone H● total remaining]" as ">#Hcoord".
  {
    iMod (alloc_closeable_chan with "[$] [$]") as "Hopen".
    iDestruct (own_closeable_chan_Unknown with "Hopen") as "#$".
    iFrame "#".
    iMod (inv_alloc with "[-]") as "$"; last done.
    iFrame. iSplitL "Hopen total".
    { destruct decide; iFrame; try done.
      iPureIntro. split.
      { rewrite (imap_sum_all_some word_count); first done.
        intros j Hj. rewrite lookup_map_seq_0 list_lookup_fmap.
        apply lookup_lt_is_Some_2 in Hj. destruct Hj as [d Hd].
        rewrite Hd /=. eauto. }
      { word. } }
    iPureIntro.
    split_and!.
    - rewrite map_seq_size length_fmap. done.
    - intros j x Hj. rewrite lookup_map_seq_0 in Hj.
      rewrite list_lookup_fmap in Hj.
      destruct (docs !! j) eqn:E; simpl in Hj; [|done].
      injection Hj as Hj. subst. done.
    - done.
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
    2:{ subst numWorkers. pose proof (mods_2_bound i ltac:(word) ltac:(word)). word. }
    list_elem workers
    (sint.Z (w64_word_instance.(word.mods) (w64_word_instance.(word.add) i (W64 1)) (W64 2))) as
    neighbor.
    { subst numWorkers. pose proof (mods_2_bound i ltac:(word) ltac:(word)). word. }
    wp_apply (wp_load_slice_index with "[$workers_sl]") as "workers_sl".
    { subst numWorkers. pose proof (mods_2_bound i ltac:(word) ltac:(word)). word. }
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
Qed.

End wps.
