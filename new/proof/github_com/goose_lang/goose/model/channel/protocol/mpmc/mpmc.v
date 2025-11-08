Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Import protocol.base.
From New.proof.github_com.goose_lang.goose.model.channel Require Export contrib.
From New.golang.theory Require Import chan.
From iris.algebra Require Import gmultiset big_op.
From iris.algebra Require Export csum.
From stdpp Require Export sets gmultiset countable.
From Perennial.algebra Require Import ghost_var.

(** * Multiple Producer Multiple Consumer (MPMC) Channel Verification

    Key insight: Each producer/consumer tracks their OWN history using multisets.

    - Producer i has sent: sent_i (a multiset)
    - Consumer j has received: recv_j (a multiset)
    - Invariant: ⊎ sent_i = ⊎ recv_j ⊎ inflight

    Uses contribution theory with gmultisetR V.
    Requires Countable V because gmultiset V = gmap V positive.
*)

#[local] Transparent is_channel own_channel.

Section mpmc.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!chan_protocolG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!Countable V}.
Context `{!contributionG Σ (gmultisetR V)}.
(* these is Perennial ghost_var (which supports dfrac), not Iris *)
Context `{!ghost_varG Σ bool}.

Record mpmc_names := {
  mpmc_chan_name : chan_names;
  mpmc_sent_name : gname;
  mpmc_recv_name : gname;
  mpmc_closed_name : gname
}.

Lemma delete_client γ n (X Y Z: gmultiset V) :
  n > 0 ->
  Z ⊆ Y →
  server γ n X -∗ client γ Y ==∗ server γ n (X ∖ Z) ∗ client γ (Y ∖ Z).
Proof.
  iIntros (Hgt HsubY) "Hs Hc".
  unfold server, client.
  destruct (decide (n = 0)); try lia.
  assert (Hupd : (X, Y) ~l~> ((X ∖ Z), (Y ∖ Z))).
  {
    apply gmultiset_local_update_dealloc.
    done.
  }
  Local Notation B := (exclR unitO).
  iMod (own_update_2 with "Hs Hc") as "[$ $]"; last done.
  by apply auth_update, option_local_update,
        csum_local_update_l, prod_local_update_2.
Qed.

Lemma delete_client_for_good γ n (X Y Z: gmultiset V) :
  n > 0 ->
  server γ n X -∗ client γ Y ==∗ server γ n (X ∖ Y) ∗ client γ (∅: gmultiset V) ∗ ⌜Y ⊆ X⌝.
Proof.
  iIntros (Hgt) "Hs Hc".
  iDestruct ((server_agree γ n X Y) with "Hs Hc") as %H.
  destruct H as [H1 H2].
  assert (Y ⊆ X).
  {
    apply gmultiset_included.
    exact H2.
  }
  iFrame "%".
  replace (∅) with (Y ∖ Y).
  {
    iApply ((delete_client _ _ X Y Y) with "Hs Hc"); first done.
    done.
  }
  {
    apply gmultiset_difference_diag.
  }
Qed.

Lemma bulk_cancel_and_dealloc γ n (X Y: gmultiset V) :
  n > 0 ->
  server γ n X -∗ client γ Y ==∗ server γ (pred n) (X ∖ Y) ∗ ⌜Y ⊆ X⌝.
Proof.
  iIntros (Hgt) "Hs Hc".
  iDestruct (delete_client_for_good with "Hs Hc") as ">(H1 & H2 & %H3)"; try done.
  iFrame "%".
  iApply (dealloc_client with "H1 H2").
Qed.

Lemma bulk_dealloc_all γ (X : gmultiset V) (ys : list (gmultiset V)) :
  let Z_total := fold_right (λ acc y, acc ⊎ y) ∅ ys in
  server γ (length ys) X -∗ ([∗ list] y_i ∈ ys, client γ y_i) ==∗ server γ 0 (∅: (gmultiset V)) ∗ ⌜X = Z_total⌝.
Proof.
  intros.
  iIntros "Hs Hcs".
  destruct ys.
  {
    simpl. simpl in Z_total. subst Z_total. unfold server. simpl.
    iDestruct "Hs" as "(%H1 & H2 & H3)".
    iModIntro. iFrame. iPureIntro. done.
  }
  iInduction ys as [|g' ys'] "IH" forall (X).
  - simpl. iDestruct "Hcs" as "[Hc _]".
    simpl in Z_total. subst Z_total. replace (g ⊎ ∅) with g by multiset_solver.
    iDestruct ((server_1_agree γ X g) with "[$Hs] [$Hc]") as %H.
    iSplitR "".
    {
      iDestruct ((bulk_cancel_and_dealloc γ 1 X g) with "Hs Hc") as ">Hnew"; try lia.
      replace g with X by multiset_solver. simpl. replace ∅ with (X ∖ X) by multiset_solver.
      iModIntro. iDestruct "Hnew" as "[H1 %H2]". iFrame.
    }
    iModIntro. iPureIntro. multiset_solver.
  - iDestruct (big_sepL_cons with "Hcs") as "[Hc Hcs]".
    iDestruct (big_sepL_cons with "Hcs") as "[Hc' Hcs]".
    iAssert ([∗ list] y ∈ (g :: ys'), client γ y)%I with "[Hc Hcs]" as "Hcs".
    { iFrame. }
    iDestruct ((bulk_cancel_and_dealloc γ (length (g :: g' :: ys')) X g') with "Hs Hc'") as ">Hnew".
    {
      rewrite length_cons. lia.
    }
    replace (Init.Nat.pred (length (g :: g' :: ys'))) with (length (g :: ys')) by done.
    iSpecialize ("IH" $! (X ∖ g')).
    iDestruct "Hnew" as "[Hnew %Hss]".
    iApply "IH" in "Hnew".
    iMod ("Hnew" with "Hcs") as "[Hr %HX]".
    iFrame.
    iModIntro. subst Z_total.
    iPureIntro.
    simpl.
    simpl in HX.
    replace X with ((X ∖ g') ⊎ g').
    { rewrite HX. multiset_solver. }
    simpl.
    symmetry.
    rewrite gmultiset_disj_union_comm.
    apply gmultiset_disj_union_difference.
    done.
Qed.

Lemma bulk_alloc_clients γ (ys : list (gmultiset V)) :
  let X := fold_right (λ acc y, acc ⊎ y) ∅ ys in
  server γ 0 (∅: gmultiset V) ==∗ server γ (length ys) X ∗ ([∗ list] y_i ∈ ys, client γ y_i).
Proof.
  intros X.
  iIntros "Hs".
  iInduction ys as [|y ys'] "IH".
  { simpl. iModIntro. iFrame. }
  {
    simpl. simpl in X.
    iMod ("IH" with "Hs") as "[Hs Hcs']".
    iMod (alloc_client with "Hs") as "[Hs Hc]".
    iMod ((update_client γ _ (foldr (λ acc y0 : gmultiset V, acc ⊎ y0) ∅ ys') ε X y) with "Hs Hc") as "[Hs Hc]".
    {
      subst X.
      rewrite comm.
      apply gmultiset_local_update.
      multiset_solver.
    }
    iModIntro. iFrame.
  }
Qed.

Lemma auth_map_agree γ (X : gmultiset V) (ys : list (gmultiset V)) :
  let Z_total := fold_right (λ acc y, acc ⊎ y) ∅ ys in
  server γ (length ys) X -∗ ([∗ list] y_i ∈ ys, client γ y_i) ==∗
    ⌜X = Z_total⌝ ∗ server γ (length ys) X ∗ ([∗ list] y_i ∈ ys, client γ y_i).
Proof.
  intros Z_total.
  iIntros "Hs Hcs".
  iMod (bulk_dealloc_all with "Hs Hcs") as "[Hnew %HX]".
  iFrame "%".
  iMod (bulk_alloc_clients γ ys with "Hnew") as "[Hs Hcs]".
  iFrame. subst X. iFrame.
  iModIntro. done.
Qed.

Definition is_closed (γ:mpmc_names) : iProp Σ :=
  ghost_var γ.(mpmc_closed_name) DfracDiscarded true.

Global Instance is_closed_persistent γ : Persistent (is_closed γ) := _.

Definition mpmc_producer (γ:mpmc_names) (sent:gmultiset V) : iProp Σ :=
  client γ.(mpmc_sent_name) sent.

Definition mpmc_consumer (γ:mpmc_names) (received:gmultiset V) : iProp Σ :=
  client γ.(mpmc_recv_name) received.

Definition inflight_mset (s : chan_rep.t V) : gmultiset V :=
  match s with
  | chan_rep.Buffered buff => list_to_set_disj buff
  | chan_rep.SndPending v | chan_rep.SndCommit v => {[+ v +]}
  | chan_rep.Closed draining => list_to_set_disj draining
  | _ => ∅
  end.

Definition is_mpmc (γ:mpmc_names) (ch:loc) (n_prod n_cons:nat)
                   (P: V → iProp Σ) (R: gmultiset V → iProp Σ) : iProp Σ :=
  ∃ (cap:Z),
    is_channel ch cap γ.(mpmc_chan_name) ∗
    inv nroot (
      ∃ s sent recv,
        "Hch" ∷ own_channel ch cap s γ.(mpmc_chan_name) ∗
        "HsentI" ∷ server γ.(mpmc_sent_name) n_prod sent ∗
        "HrecvI" ∷ server γ.(mpmc_recv_name) n_cons recv ∗
        "%Hrel" ∷ ⌜sent = recv ⊎ inflight_mset s⌝ ∗
        "%Hncons" ∷ ⌜n_cons > 0⌝ ∗
        "%Hnprod" ∷ ⌜n_prod > 0⌝ ∗
        "Hclosed" ∷ (match s with
                     | chan_rep.Closed [] => ghost_var γ.(mpmc_closed_name) DfracDiscarded true
                     | _ => ghost_var γ.(mpmc_closed_name) (DfracOwn 1) false
                     end) ∗
        (match s with
        | chan_rep.Buffered buff => "Hbuff" ∷ [∗ list] v ∈ buff, P v
        | chan_rep.SndPending v => "HPv" ∷ P v
        | chan_rep.SndCommit v => "HPv" ∷ P v
        | chan_rep.Closed [] =>
            "%Hsent_recv" ∷ ⌜sent = recv⌝ ∗
            "Hprods" ∷ (∃ prods : list (gmultiset V), ⌜length prods = n_prod⌝ ∗
                        [∗ list] s_i ∈ prods, mpmc_producer γ s_i) ∗
            "HR_or_clients" ∷ (R sent ∨ (∃ conss : list (gmultiset V), ⌜length conss = n_cons⌝ ∗
                                          [∗ list] r_i ∈ conss, mpmc_consumer γ r_i))
        | chan_rep.Closed draining =>
            "Hdraining" ∷ ([∗ list] v ∈ draining, P v) ∗
            "Hprods" ∷ (∃ prods : list (gmultiset V), ⌜length prods = n_prod⌝ ∗
                        [∗ list] s_i ∈ prods, mpmc_producer γ s_i) ∗
            "HR" ∷ R sent
        | _ => True
        end)
    )%I.

Lemma gmultiset_disj_union_local_update (X Y Z : gmultiset V) :
  (X, Y) ~l~> (X ⊎ Z, Y ⊎ Z).
Proof.
  apply gmultiset_local_update_alloc.
Qed.

Lemma start_mpmc ch (P : V → iProp Σ) (R : gmultiset V → iProp Σ) γ (n_prod n_cons : nat) cap s:
  match s with
  | chan_rep.Buffered [] => True
  | chan_rep.Idle => True
  | _ => False
  end ->
  n_prod > 0 ->
  n_cons > 0 ->
  is_channel ch cap γ -∗
  (own_channel ch cap s γ) ={⊤}=∗
  (∃ γmpmc, is_mpmc γmpmc ch n_prod n_cons P R ∗
            ([∗ list] _ ∈ seq 0 n_prod, mpmc_producer γmpmc ∅) ∗
            ([∗ list] _ ∈ seq 0 n_cons, mpmc_consumer γmpmc ∅)).
Proof.
  intros Hs Hprod Hcons.
  iIntros "#Hch Hoc".
  iMod (ghost_var_alloc false) as (γclosed) "Hclosed".
  iMod (contribution_init_pow n_prod (A := gmultisetR V)) as (γsent) "[HsentAuth HsentFrags]".
  iMod (contribution_init_pow n_cons (A := gmultisetR V)) as (γrecv) "[HrecvAuth HrecvFrags]".
  set (γmpmc := {| mpmc_chan_name := γ;
                   mpmc_sent_name := γsent;
                   mpmc_recv_name := γrecv;
                   mpmc_closed_name := γclosed |}).
  destruct s; try done.
  {
    destruct buff; try done.
    iMod (inv_alloc nroot _ (
      ∃ s sent recv,
        "Hch" ∷ own_channel ch cap s γ ∗
        "HsentI" ∷ server γsent n_prod sent ∗
        "HrecvI" ∷ server γrecv n_cons recv ∗
        "%Hrel" ∷ ⌜sent = recv ⊎ inflight_mset s⌝ ∗
        "%Hncons" ∷ ⌜n_cons > 0⌝ ∗
        "%Hnprod" ∷ ⌜n_prod > 0⌝ ∗
        "Hclosed" ∷ (match s with
                     | chan_rep.Closed [] => ghost_var γclosed DfracDiscarded true
                     | _ => ghost_var γclosed (DfracOwn 1) false
                     end) ∗
        (match s with
        | chan_rep.Buffered buff => "Hbuff" ∷ [∗ list] v ∈ buff, P v
        | chan_rep.SndPending v => "HPv" ∷ P v
        | chan_rep.SndCommit v => "HPv" ∷ P v
        | chan_rep.Closed [] =>
            "%Hsent_recv" ∷ ⌜sent = recv⌝ ∗
            "Hprods" ∷ (∃ prods : list (gmultiset V), ⌜length prods = n_prod⌝ ∗
                        [∗ list] s_i ∈ prods, mpmc_producer γmpmc s_i) ∗
            "HR_or_clients" ∷ (R sent ∨ (∃ conss : list (gmultiset V), ⌜length conss = n_cons⌝ ∗
                                          [∗ list] r_i ∈ conss, mpmc_consumer γmpmc r_i))
        | chan_rep.Closed draining =>
            "Hdraining" ∷ ([∗ list] v ∈ draining, P v) ∗
            "Hprods" ∷ (∃ prods : list (gmultiset V), ⌜length prods = n_prod⌝ ∗
                        [∗ list] s_i ∈ prods, mpmc_producer γmpmc s_i) ∗
            "HR" ∷ R sent
        | _ => True
        end)
    ) with "[Hoc HsentAuth HrecvAuth Hclosed]") as "#Hinv".
    {
      iNext.
      iFrame.
      iSplitL ""; first done.
      iFrame.
      simpl. done.
    }
    iModIntro. iExists γmpmc.
    unfold is_mpmc. iFrame. iSplitL "". { iExists cap. iFrame "#". }
    iSplitL "HsentFrags".
    - unfold mpmc_producer.
      assert (∅ = (ε : gmultiset V)) as Heq by reflexivity.
      rewrite -Heq.
      iApply big_sepL_replicate.
      rewrite length_seq. done.
    - unfold mpmc_consumer.
      assert (∅ = (ε : gmultiset V)) as Heq by reflexivity.
      rewrite -Heq.
      iApply big_sepL_replicate.
      rewrite length_seq. done.
  }
  {
    iMod (inv_alloc nroot _ (
      ∃ s sent recv,
        "Hch" ∷ own_channel ch cap s γ ∗
        "HsentI" ∷ server γsent n_prod sent ∗
        "HrecvI" ∷ server γrecv n_cons recv ∗
        "%Hrel" ∷ ⌜sent = recv ⊎ inflight_mset s⌝ ∗
        "%Hncons" ∷ ⌜n_cons > 0⌝ ∗
        "%Hnprod" ∷ ⌜n_prod > 0⌝ ∗
        "Hclosed" ∷ (match s with
                     | chan_rep.Closed [] => ghost_var γclosed DfracDiscarded true
                     | _ => ghost_var γclosed (DfracOwn 1) false
                     end) ∗
        (match s with
        | chan_rep.Buffered buff => "Hbuff" ∷ [∗ list] v ∈ buff, P v
        | chan_rep.SndPending v => "HPv" ∷ P v
        | chan_rep.SndCommit v => "HPv" ∷ P v
        | chan_rep.Closed [] =>
            "%Hsent_recv" ∷ ⌜sent = recv⌝ ∗
            "Hprods" ∷ (∃ prods : list (gmultiset V), ⌜length prods = n_prod⌝ ∗
                        [∗ list] s_i ∈ prods, mpmc_producer γmpmc s_i) ∗
            "HR_or_clients" ∷ (R sent ∨ (∃ conss : list (gmultiset V), ⌜length conss = n_cons⌝ ∗
                                          [∗ list] r_i ∈ conss, mpmc_consumer γmpmc r_i))
        | chan_rep.Closed draining =>
            "Hdraining" ∷ ([∗ list] v ∈ draining, P v) ∗
            "Hprods" ∷ (∃ prods : list (gmultiset V), ⌜length prods = n_prod⌝ ∗
                        [∗ list] s_i ∈ prods, mpmc_producer γmpmc s_i) ∗
            "HR" ∷ R sent
        | _ => True
        end)
    ) with "[Hoc HsentAuth HrecvAuth Hclosed]") as "#Hinv".
    {
      iNext.
      iFrame.
      iSplitL ""; first done.
      iFrame.
      iPureIntro. done.
    }
    iModIntro. iExists γmpmc.
    unfold is_mpmc. iFrame. iSplitL "". { iExists cap. iFrame "#". }
    iSplitL "HsentFrags".
    - unfold mpmc_producer.
      assert (∅ = (ε : gmultiset V)) as Heq by reflexivity.
      rewrite -Heq.
      iApply big_sepL_replicate.
      rewrite length_seq. done.
    - unfold mpmc_consumer.
      assert (∅ = (ε : gmultiset V)) as Heq by reflexivity.
      rewrite -Heq.
      iApply big_sepL_replicate.
      rewrite length_seq. done.
  }
Qed.

Lemma wp_mpmc_send γ ch (n_prod n_cons:nat) (P : V → iProp Σ) (R : gmultiset V → iProp Σ)
                   (sent : gmultiset V) (v : V) :
  {{{ is_mpmc γ ch n_prod n_cons P R ∗
      mpmc_producer γ sent ∗
      P v }}}
    chan.send #t #ch #v
  {{{ RET #(); mpmc_producer γ (sent ⊎ {[+ v +]}) }}}.
Proof.
  iIntros (Φ) "(#Hmpmc & Hprod & HP) Hcont".
  unfold is_mpmc. iNamed "Hmpmc". iDestruct "Hmpmc" as "[#Hchan Hinv]".
  iApply (chan.wp_send ch cap v γ.(mpmc_chan_name) with "[$Hchan]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  iMod (lc_fupd_elim_later with "Hlc1 Hcont") as "Hcont".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc2 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  iDestruct (server_agree with "HsentI Hprod") as %[Hn_pos Hsub].
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iFrame "Hch".
  destruct s; try done.
  {
    destruct (decide (length buff < cap)%Z); [|done].
    iIntros "Hoc".
    unfold mpmc_producer.
    iMod (update_client γ.(mpmc_sent_name) n_prod sent0 sent
                       (sent0 ⊎ {[+ v +]}) (sent ⊎ {[+ v +]})
           with "HsentI Hprod") as "[HsentI Hprod]".
    { apply gmultiset_disj_union_local_update. }
    iMod "Hmask".
    iNamed "Hinv_open".
    iMod ("Hinv_close" with "[Hoc HsentI HrecvI Hclosed HP Hbuff]") as "_".
    {
      iNext. iExists (chan_rep.Buffered (buff ++ [v])), (sent0 ⊎ {[+ v +]}), recv.
      iFrame "Hoc HsentI HrecvI Hclosed".
      iSplitR.
      {
        iPureIntro. rewrite Hrel. unfold inflight_mset.
        rewrite list_to_set_disj_app /=.
        rewrite gmultiset_disj_union_right_id gmultiset_disj_union_assoc.
        reflexivity.
      }
      simpl. iFrame "Hbuff HP".
      iFrame. simpl.
      iPureIntro.
      done.
    }
    iModIntro. by iApply "Hcont".
  }
  {
    iIntros "Hoc".
    unfold mpmc_producer.
    iMod (update_client γ.(mpmc_sent_name) n_prod sent0 sent
                       (sent0 ⊎ {[+ v +]}) (sent ⊎ {[+ v +]})
           with "HsentI Hprod") as "[HsentI Hprod]".
    { apply gmultiset_disj_union_local_update. }
    iMod "Hmask".
    iNamed "Hoc".
    iAssert (own_channel ch cap (chan_rep.SndPending v) γ.(mpmc_chan_name))%I
      with "[Hchanrepfrag]" as "Hoc".
    { iFrame. iPureIntro. unfold chan_cap_valid. done. }
    iMod ("Hinv_close" with "[Hoc HsentI HrecvI Hclosed HP]") as "_".
    {
      iNext. iExists (chan_rep.SndPending v), (sent0 ⊎ {[+ v +]}), recv.
      iFrame "Hoc HsentI HrecvI Hclosed".
      iSplitR.
      { iPureIntro. rewrite Hrel. unfold inflight_mset. set_solver. }
      simpl. iFrame "HP".
      iPureIntro. done.
    }
    iModIntro. unfold send_au_inner.
    iInv "Hinv" as "Hinv_open2" "Hinv_close2".
    iMod (lc_fupd_elim_later with "Hlc3 Hinv_open2") as "Hinv_open2".
    iNamed "Hinv_open2".
    destruct s; try (iFrame;done).
    {
      iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask1"].
      iNext.
      iNamed "Hinv_open2".
      iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask1"].
      iNext.
      iNamed "Hinv_open2".
      iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask1"].
      iNext.
      iNamed "Hinv_open2".
      iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask1"].
      iNext.
      iNamed "Hinv_open2".
      iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask1"].
      iNext.
      iNamed "Hinv_open2".
      iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask1"].
      iNext.
      iNamed "Hinv_open2".
      iFrame.
      iIntros "Hoc".
      iMod "Hmask1".
      iMod ("Hinv_close2" with "[HsentI HrecvI Hoc Hclosed]") as "_".
      {
        iNext. iExists chan_rep.Idle, sent1, recv0.
        iFrame "Hoc HsentI HrecvI Hclosed".
        iPureIntro. rewrite Hrel0. simpl. done.
      }
      iModIntro. by iApply "Hcont".
    }
    {
      destruct draining.
      - iNamed "Hinv_open2".
        unfold mpmc_producer.
        iNamed "Hprods".
        iDestruct "Hprods" as "[%H1 Hprods]".
        subst n_prod.
        iExists (chan_rep.Closed []).
        iFrame "Hch".
        iMod (bulk_dealloc_all with "HsentI Hprods") as "[Hserver0 _]".
        iFrame.
        destruct prods as [|p ps]; first (simpl in *;lia).
        iDestruct (server_agree with "Hserver0 Hprod") as %[Hcontra _].
        done.
      - iNamed "Hinv_open2".
        unfold mpmc_producer.
        iNamed "Hprods".
        iDestruct "Hprods" as "[%H1 Hprods]".
        subst n_prod.
        iMod (bulk_dealloc_all with "HsentI Hprods") as "[Hserver0 _]".
        iFrame.
        destruct prods as [|p ps]; first (simpl in *;lia).
        iDestruct (server_agree with "Hserver0 Hprod") as %[Hcontra _].
        done.
    }
  }
  {
    iMod "Hmask".
    iNamed "Hinv_open". iIntros "Hoc".
    iMod (update_client γ.(mpmc_sent_name) n_prod sent0 sent
                       (sent0 ⊎ {[+ v +]}) (sent ⊎ {[+ v +]})
           with "HsentI Hprod") as "[HsentI Hprod]".
    { apply gmultiset_disj_union_local_update. }
    iMod ("Hinv_close" with "[Hoc HsentI HrecvI Hclosed HP]") as "_".
    {
      iNext. iFrame. iFrame "HP". iFrame. iPureIntro. subst sent0.
      unfold inflight_mset. simpl. set_solver.
    }
    {
      iModIntro. iApply "Hcont". iFrame.
    }
  }
  {
    destruct draining.
    - iNamed "Hinv_open".
      unfold mpmc_producer.
      iNamed "Hprods".
      iDestruct "Hprods" as "[%H1 Hprods]".
      subst n_prod.
      iMod (bulk_dealloc_all with "HsentI Hprods") as "[Hserver0 _]".
      iFrame.
      destruct prods as [|p ps]; first (simpl in *;lia).
      iDestruct (server_agree with "Hserver0 Hprod") as %[Hcontra _].
      done.
    - iNamed "Hinv_open".
      unfold mpmc_producer.
      iNamed "Hprods".
      iDestruct "Hprods" as "[%H1 Hprods]".
      subst n_prod.
      iMod (bulk_dealloc_all with "HsentI Hprods") as "[Hserver0 _]".
      iFrame.
      destruct prods as [|p ps]; first (simpl in *;lia).
      iDestruct (server_agree with "Hserver0 Hprod") as %[Hcontra _].
      done.
  }
Qed.

Lemma wp_mpmc_receive γ ch (n_prod n_cons:nat) (P : V → iProp Σ) (R : gmultiset V → iProp Σ)
                      (received : gmultiset V) :
  {{{  is_mpmc γ ch n_prod n_cons P R ∗
      mpmc_consumer γ received }}}
    chan.receive #t #ch
  {{{ (v:V) (ok:bool), RET (#v, #ok);
      if ok
      then P v ∗ mpmc_consumer γ (received ⊎ {[+ v +]})
      else is_closed γ ∗ mpmc_consumer γ received }}}.
Proof.
  iIntros (Φ) "( #Hmpmc & Hcons) Hcont".
  unfold is_mpmc. iNamed "Hmpmc".
  iDestruct "Hmpmc" as "[Hchan Hinv]".
  iApply (chan.wp_receive ch cap γ.(mpmc_chan_name) with "[$Hchan]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  iDestruct (server_agree with "HrecvI Hcons") as %[Hn_pos Hsub].
  unfold rcv_au_slow.
  iExists s. iFrame "Hch".
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iFrame.
  destruct s; try done.
  {
    destruct buff as [|v rest].
    { done. }
    {
      iIntros "Hoc".
      unfold mpmc_consumer.
      iMod (update_client γ.(mpmc_recv_name) n_cons recv received (recv ⊎ {[+ v +]})
                                (received ⊎ {[+ v +]})
             with "HrecvI Hcons") as "[HrecvI_new Hcons_new]".
      { apply gmultiset_disj_union_local_update. }
      iDestruct (big_sepL_cons with "Hinv_open") as "[HPv Hrest]".
      iMod "Hmask".
      iMod ("Hinv_close" with "[Hoc HsentI HrecvI_new Hrest Hclosed]") as "_".
      {
        iNext.
        iFrame.
        iFrame "%".
        iFrame.
        iPureIntro.
        rewrite Hrel. simpl. unfold inflight_mset.
        rewrite -gmultiset_disj_union_assoc.
        reflexivity.
      }
      iModIntro. iApply "Hcont". iFrame.
    }
  }
  {
    iIntros "Hoc".
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc HsentI HrecvI Hclosed]") as "_".
    {
      iNext.
      iFrame. iFrame "%". iFrame.
    }
    iModIntro. unfold rcv_au_inner.
    iInv "Hinv" as "Hinv_open2" "Hinv_close2".
    iMod (lc_fupd_elim_later with "Hlc2 Hinv_open2") as "Hinv_open2".
    iNamed "Hinv_open2".
    iDestruct (server_agree with "HrecvI Hcons") as %[_ Hsub2].
    unfold rcv_au_slow.
    iExists s. iFrame "Hch".
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask1"].
    iNext.
    destruct s; try done.
    {
      iMod (update_client γ.(mpmc_recv_name) n_cons recv0 received (recv0 ⊎ {[+ v +]})
                                (received ⊎ {[+ v +]})
             with "HrecvI Hcons") as "[HrecvI_new Hcons_new]".
      { apply gmultiset_disj_union_local_update. }
      iIntros "Hoc".
      iMod "Hmask1".
      iMod ("Hinv_close2" with "[HsentI HrecvI_new Hoc Hclosed]") as "_".
      {
        iNext.
        iFrame. iFrame "Hclosed". iPureIntro.
        rewrite Hrel0. simpl. rewrite gmultiset_disj_union_right_id. done.
      }
      iModIntro. iApply "Hcont". iFrame.
    }
    {
      destruct draining as [|v rest]; last done.
      iIntros "Hoc".
      iMod "Hmask1".
      simpl.
      iDestruct "Hinv_open2" as "[%Hprod2 HR]".
      iNamed "HR".
      iDestruct "HR_or_clients" as "[HR_final | Hconss]".
      - iDestruct "Hclosed" as "#Hclosed".
        iMod ("Hinv_close2" with "[Hoc HsentI HrecvI Hprods HR_final]") as "_".
        {
          iNext. iExists (chan_rep.Closed []), sent0, recv0.
          iFrame "#". iFrame. iFrame "%".
        }
        iModIntro.
        iApply "Hcont".
        iFrame "Hcons".
        unfold is_closed.
        iFrame.
        iFrame "Hclosed".
      - unfold mpmc_consumer.
        iNamed "Hconss".
        iDestruct "Hconss" as "[%H1 Hcons1]".
        subst n_cons.
        iMod (bulk_dealloc_all with "HrecvI Hcons1") as "[Hserver0 _]".
        iFrame.
        destruct conss as [|p ps]; first (simpl in *;lia).
        iDestruct (server_agree with "Hserver0 Hcons") as %[Hcontra _].
        done.
    }
  }
  {
    iIntros "Hcont1".
    iMod "Hmask".
    iMod (update_client γ.(mpmc_recv_name) n_cons recv received (recv ⊎ {[+ v +]})
                                (received ⊎ {[+ v +]})
             with "HrecvI Hcons") as "[HrecvI_new Hcons_new]".
    { apply gmultiset_disj_union_local_update. }
    iMod ("Hinv_close" with "[HsentI HrecvI_new Hcont1 Hclosed]") as "_".
    {
      iNext.
      iFrame. iFrame "Hclosed". iPureIntro.
      unfold inflight_mset in *. rewrite gmultiset_disj_union_right_id. done.
    }
    iModIntro. iApply "Hcont". iFrame.
  }
  {
    destruct draining as [|v rest].
    {
      iIntros "Hoc".
      iMod "Hmask".
      simpl.
      iDestruct "Hinv_open" as "[%Hprod2 HR]".
      iNamed "HR".
      iDestruct "HR_or_clients" as "[HR_final | Hconss]".
      - iDestruct "Hclosed" as "#Hclosed".
        iMod ("Hinv_close" with "[Hoc HsentI HrecvI Hprods HR_final]") as "_".
        {
          iNext.
          iFrame.
          iFrame "#". iFrame. iFrame "%".
        }
        iModIntro.
        iApply "Hcont".
        iFrame "Hcons".
        unfold is_closed.
        iFrame.
        iFrame "Hclosed".
      - unfold mpmc_consumer.
        iNamed "Hconss".
        iDestruct "Hconss" as "[%H1 Hcons1]".
        subst n_cons.
        iMod (bulk_dealloc_all with "HrecvI Hcons1") as "[Hserver0 _]".
        iFrame.
        destruct conss as [|p ps]; first (simpl in *;lia).
        iDestruct (server_agree with "Hserver0 Hcons") as %[Hcontra _].
        done.
    }
    {
      iIntros "Hoc".
      iMod (update_client _ _ recv received (recv ⊎ {[+ v +]}) (received ⊎ {[+ v +]})
             with "HrecvI Hcons") as "[HrecvI_new Hcons_new]".
      { apply gmultiset_disj_union_local_update. }
      iMod "Hmask".
      iDestruct "Hinv_open" as "(Hrest & Hmp & HR)".
      {
        iDestruct (big_sepL_cons with "Hrest") as "[HPv Hrest2]".
        destruct rest.
        {
          iMod (ghost_var_update true with "Hclosed") as "Hclosed".
          iMod (ghost_var_persist with "Hclosed") as "#Hclosed'".
          iMod ("Hinv_close" with "[HsentI HrecvI_new Hoc HR Hmp]") as "_".
          {
            iNext.
            iFrame. iFrame "#". iFrame "HR".
            iFrame "Hmp". iPureIntro.
            split.
            {
              rewrite Hrel. unfold inflight_mset.
              rewrite list_to_set_disj_cons list_to_set_disj_nil.
              rewrite gmultiset_disj_union_right_id -gmultiset_disj_union_assoc.
              set_solver.
            }
            set_solver.
          }
          iModIntro. iApply "Hcont". iFrame.
        }
        {
          iMod ("Hinv_close" with "[HsentI HrecvI_new Hoc Hrest2 HR Hmp Hclosed]") as "_".
          {
            iNext.
            iFrame. iFrame "HR".
            iFrame.
            iFrame "%".
            iFrame "#".
            iPureIntro.
            rewrite Hrel. unfold inflight_mset.
            rewrite !list_to_set_disj_cons -!gmultiset_disj_union_assoc.
            reflexivity.
          }
          iModIntro. iApply "Hcont". iFrame.
        }
      }
    }
  }
Qed.

Lemma wp_mpmc_close γ ch (n_prod n_cons:nat) P R (producers : list (gmultiset V)):
  length producers = n_prod →
  {{{ £ 1 ∗ £ 1 ∗ £ 1 ∗ is_mpmc γ ch n_prod n_cons P R ∗
      ([∗ list] s_i ∈ producers, mpmc_producer γ s_i) ∗
      R (foldr (⊎) ∅ producers) }}}
    chan.close #t #ch
  {{{ RET #(); True }}}.
Proof.
  intros.
  iIntros "(Hlc1 & Hlc2 & Hlc3 & #Hmpmc & Hprods & HR) Hcont".
  unfold is_mpmc. iNamed "Hmpmc".
  iDestruct "Hmpmc" as "[Hchan Hinv]".
  iApply (chan.wp_close ch cap γ.(mpmc_chan_name) with "[$Hchan]").
  iIntros "Hlc4".
  iMod (lc_fupd_elim_later with "Hlc1 Hcont") as "Hcont".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc2 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  destruct s; try done.
  - iExists (chan_rep.Buffered buff). iFrame "Hch".
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
    iIntros "Hoc".
    iMod "Hmask".
    iFrame.
    destruct buff as [|v rest].
    + iMod (ghost_var_update true with "Hclosed") as "Hclosed".
      iMod (ghost_var_persist with "Hclosed") as "#Hclosed'".
      assert (inflight_mset (chan_rep.Buffered []) = ∅) as Hempty.
      { simpl. reflexivity. }
      rewrite Hempty in Hrel.
      rewrite right_id in Hrel.
      unfold mpmc_producer.
      subst n_prod.
      iMod (auth_map_agree γ.(mpmc_sent_name) sent producers with "[$HsentI] [$Hprods]") as "(%Hsent_eq & HsentI & Hprods)".
      replace (foldr (λ acc y : gmultiset V, acc ⊎ y) ∅ producers) with sent by done.
      iMod ("Hinv_close" with "[Hoc HsentI HrecvI Hinv_open Hprods HR]") as "_".
      {
        iNext.
        iFrame. iFrame "#".
        simpl.
        iFrame "%".
        rewrite right_id.
        iSplitL ""; first done.
        unfold inflight_mset in Hrel.
        simpl in Hrel.
        iFrame.
        done.
      }
      iModIntro.
      iApply "Hcont". done.
    + iFrame.
      unfold mpmc_producer.
      subst n_prod.
      iMod (auth_map_agree γ.(mpmc_sent_name) sent producers with "[$HsentI] [$Hprods]") as "(%Hsent_eq & HsentI & Hprods)".
      replace (foldr (λ acc y : gmultiset V, acc ⊎ y) ∅ producers) with sent by done.
      iMod ("Hinv_close" with "[Hoc HsentI HrecvI Hinv_open Hprods Hclosed HR]") as "_".
      {
        iModIntro. iFrame.
        iFrame "%#". iFrame.
        done.
      }
      iModIntro.
      iApply "Hcont". done.
  - iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
    iFrame. iIntros "Hoc".
    iMod (ghost_var_update true with "Hclosed") as "Hclosed".
    iMod (ghost_var_persist with "Hclosed") as "#Hclosed'".
    iMod "Hmask".
    unfold mpmc_producer.
    subst n_prod.
    iMod (auth_map_agree γ.(mpmc_sent_name) sent producers with "[$HsentI] [$Hprods]") as "(%Hsent_eq & HsentI & Hprods)".
    replace (foldr (λ acc y : gmultiset V, acc ⊎ y) ∅ producers) with sent by done.
    iMod ("Hinv_close" with "[Hoc HsentI HrecvI Hclosed' Hprods HR]") as "_".
    {
      iNext.
      iExists (chan_rep.Closed []), sent, recv.
      iFrame "Hoc HsentI HrecvI".
      iSplitR; first by iPureIntro; rewrite Hrel; simpl.
      iFrame "Hclosed'".
      simpl. iFrame.
      iPureIntro.
      unfold inflight_mset in Hrel.
      simpl in Hrel.
      subst sent.
      multiset_solver.
    }
    iModIntro. iApply "Hcont". done.
  - unfold mpmc_producer.
    subst n_prod.
    iMod (auth_map_agree γ.(mpmc_sent_name) sent producers with "[$HsentI] [$Hprods]") as "(%Hsent_eq & HsentI & Hprods)".
    replace (foldr (λ acc y : gmultiset V, acc ⊎ y) ∅ producers) with sent by done.
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
    iFrame.
  - unfold mpmc_producer.
    subst n_prod.
    iMod (auth_map_agree γ.(mpmc_sent_name) sent producers with "[$HsentI] [$Hprods]") as "(%Hsent_eq & HsentI & Hprods)".
    replace (foldr (λ acc y : gmultiset V, acc ⊎ y) ∅ producers) with sent by done.
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
    iFrame.
  - unfold mpmc_producer.
    subst n_prod.
    iMod (auth_map_agree γ.(mpmc_sent_name) sent producers with "[$HsentI] [$Hprods]") as "(%Hsent_eq & HsentI & Hprods)".
    replace (foldr (λ acc y : gmultiset V, acc ⊎ y) ∅ producers) with sent by done.
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
    iFrame.
  - unfold mpmc_producer.
    subst n_prod.
    iMod (auth_map_agree γ.(mpmc_sent_name) sent producers with "[$HsentI] [$Hprods]") as "(%Hsent_eq & HsentI & Hprods)".
    replace (foldr (λ acc y : gmultiset V, acc ⊎ y) ∅ producers) with sent by done.
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
    iFrame.
  - unfold mpmc_producer.
    subst n_prod.
    iMod (auth_map_agree γ.(mpmc_sent_name) sent producers with "[$HsentI] [$Hprods]") as "(%Hsent_eq & HsentI & Hprods)".
    replace (foldr (λ acc y : gmultiset V, acc ⊎ y) ∅ producers) with sent by done.
    destruct draining.
    {
      iDestruct "Hprods" as "Hprods1".
      iNamed "Hinv_open". iNamed "Hprods".
      iDestruct "Hprods" as "[%Hgood H2]".
      replace (length producers) with (length prods) by done.
      iMod (auth_map_agree γ.(mpmc_sent_name) sent prods with "[$HsentI] [$H2]") as
        "(%Hsent_eq1 & HsentI2 & Hprods2)".
      replace (foldr (λ acc y : gmultiset V, acc ⊎ y) ∅ producers) with sent by done.
      iMod (bulk_dealloc_all with "HsentI2 Hprods2") as "[Hserver0 _]".
      destruct producers as [|p ps]; first (simpl in *;lia).
      iDestruct (big_sepL_cons with "Hprods1") as "[Hp _]".
      iExFalso.
      iDestruct (server_agree with "Hserver0 Hp") as %[Hcontra _].
      lia.
    }
    {
      iDestruct "Hprods" as "Hprods1". iDestruct "HR" as "HR1".
      iNamed "Hinv_open". iNamed "Hprods".
      iDestruct "Hprods" as "[%Hgood H2]".
      replace (length producers) with (length prods) by done.
      iMod (auth_map_agree γ.(mpmc_sent_name) sent prods with "[$HsentI] [$H2]") as
        "(%Hsent_eq1 & HsentI2 & Hprods2)".
      replace (foldr (λ acc y : gmultiset V, acc ⊎ y) ∅ producers) with sent by done.
      iMod (bulk_dealloc_all with "HsentI2 Hprods2") as "[Hserver0 _]".
      destruct producers as [|p ps]; first (simpl in *;lia).
      iDestruct (big_sepL_cons with "Hprods1") as "[Hp _]".
      iExFalso.
      iDestruct (server_agree with "Hserver0 Hp") as %[Hcontra _].
      lia.
    }
Qed.

Lemma mpmc_get_final_resource
  γ ch (n_prod n_cons : nat) P R (consumers : list (gmultiset V)) :
  length consumers = n_cons →
  £ 1 -∗
  is_mpmc γ ch n_prod n_cons P R -∗
  is_closed γ -∗
  ([∗ list] r_i ∈ consumers, mpmc_consumer γ r_i)
  ={⊤}=∗ R (foldr disj_union ∅ consumers).
Proof.
  iIntros (Hlen) "Hlc #Hmpmc #Hclosed Hcons".
  unfold is_mpmc. iDestruct "Hmpmc" as (cap) "[#Hchan #Hinv]".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iNamed "Hinv_open".
  iMod (lc_fupd_elim_later with "Hlc Hinv_open") as "Hinv_open".
  iDestruct "Hclosed" as "#Hclosed1".
  iNamed "Hinv_open".
  unfold is_closed.
  destruct s; try (iExFalso;(iDestruct (ghost_var_agree with "Hclosed1 Hclosed") as %Hbad);done).
  destruct draining.
  - iNamed "Hinv_open".
    iDestruct "HR_or_clients" as "[HR | Hconss]".
    + unfold mpmc_consumer.
      subst n_cons.
      iMod (auth_map_agree γ.(mpmc_recv_name) recv consumers with "HrecvI Hcons") as
        "(%Hrecv_eq & HrecvI & Hcons)". rewrite Hsent_recv. rewrite Hrecv_eq.
      iFrame.
      iMod ("Hinv_close" with "[Hch HsentI HrecvI Hclosed Hprods Hcons]") as "_".
      {
        iNext. iFrame "#%". iFrame.
        rewrite Hsent_recv. rewrite Hrecv_eq.
        iFrame.
        iRight.
        iFrame.
        done.
      }
      iModIntro. done.
    + unfold mpmc_consumer.
      subst n_cons.
      iMod (auth_map_agree γ.(mpmc_recv_name) recv consumers with "HrecvI Hcons") as
        "(%Hrecv_eq & HrecvI & Hcons)". rewrite Hsent_recv. rewrite Hrecv_eq.
      iFrame.
      iExFalso.
      iDestruct "Hconss" as (conss Hlen_conss) "Hconss_list".
      iMod (bulk_dealloc_all with "HrecvI Hcons") as "[Hserver0 _]".
      destruct conss as [|c cs]; first (simpl in *;lia).
      iDestruct (big_sepL_cons with "Hconss_list") as "[Hc _]".
      iDestruct (server_agree with "Hserver0 Hc") as %[Hcontra _].
      lia.
  - iNamed "Hinv_open".
    unfold is_mpmc.
    iDestruct (ghost_var_agree with "Hclosed1 Hclosed") as %Hclosed_eq.
    done.
Qed.

End mpmc.
