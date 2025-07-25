From iris.algebra Require Import mono_nat mono_list gmap_view gset.
From iris.algebra.lib Require Import dfrac_agree.
From Perennial.base_logic Require Import ghost_map mono_nat saved_prop.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import quorum.

Definition ledger := list byte_string.

Definition proposals := gmap nat ledger.

Inductive nodedec :=
| Accept (v : ledger)
| Reject.

Section def.
  Context `{Countable A}.
  (* XXX: fix the naming scheme *)
  Implicit Type t n : nat.
  Implicit Type l : proposals.
  Implicit Type v : ledger.
  Implicit Type bs bsq : gmap A proposals.
  Implicit Type ps psb : proposals.

  Definition accepted_in l t v :=
    ∃ v', l !! t = Some v' ∧ prefix v v'.

  Definition chosen_in bs t v :=
    ∃ bsq, bsq ⊆ bs ∧
           cquorum_size (dom bs) (dom bsq) ∧
           map_Forall (λ _ l, accepted_in l t v) bsq.

  Definition chosen bs v :=
    ∃ t, chosen_in bs t v.

  Definition consistency bs :=
    ∀ v1 v2, chosen bs v1 -> chosen bs v2 -> prefix v1 v2 ∨ prefix v2 v1.

  Definition proposed_after_chosen bs ps :=
    ∀ t1 t2 v1 v2,
    (t1 < t2)%nat ->
    chosen_in bs t1 v1 ->
    ps !! t2 = Some v2 ->
    prefix v1 v2.

  (* Compute the latest term in which a proposal is accepted before [n]. *)
  Fixpoint latest_term_before_with `{Lookup nat B M}
    (f : option B -> option ledger) (t : nat) (m : M) :=
    match t with
    | O => O
    | S p => match f (m !! p) with
            | Some _ => p
            | _ => latest_term_before_with f p m
            end
    end.

  (* XXX: duplicate lemma *)
  Lemma latest_term_before_with_lt `{Lookup nat B M} f t (m : M) :
    t ≠ O ->
    (latest_term_before_with f t m < t)%nat.
  Proof.
    intros Hnz.
    induction t as [| t IH]; first done.
    simpl.
    destruct (f (m !! t)); first lia.
    destruct (decide (t = O)) as [Heq | Hne].
    { subst t. simpl. lia. }
    specialize (IH Hne).
    lia.
  Qed.

  Lemma latest_term_before_with_None `{Lookup nat B M} f t p (m : M) :
    (latest_term_before_with f t m < p < t)%nat ->
    f (m !! p) = None.
  Proof.
    intros Hp.
    induction t as [| t IH]; first lia.
    destruct (f (m !! t)) as [v |] eqn:Hv.
    { rewrite /latest_term_before_with Hv in Hp. lia. }
    destruct (decide (p = t)) as [-> | Hne]; first apply Hv.
    apply IH.
    rewrite /latest_term_before_with Hv in Hp.
    rewrite /latest_term_before_with.
    lia.
  Qed.

  Definition latest_term_before t ps :=
    latest_term_before_with id t ps.

  Definition latest_term_before_quorum_step (x : A) (cur prev : nat) : nat :=
    cur `max` prev.

  Definition latest_term_before_quorum_with `{Lookup nat B M}
    (f : option B -> option ledger) (ms : gmap A M) (t : nat) :=
    let ts := fmap (latest_term_before_with f t) ms in
    map_fold latest_term_before_quorum_step O ts.

  Lemma latest_term_before_quorum_with_singleton `{Lookup nat B M} f (x : A) (m : M) t p :
    latest_term_before_with f t m = p ->
    latest_term_before_quorum_with f {[x := m]} t = p.
  Proof.
    intros Hp.
    rewrite /latest_term_before_quorum_with map_fmap_singleton map_fold_singleton.
    by rewrite /latest_term_before_quorum_step Nat.max_0_r.
  Qed.

  Lemma latest_term_before_quorum_with_insert_le `{Lookup nat B M}
    f (ms : gmap A M) (x : A) (m : M) t p :
    ms !! x = None ->
    latest_term_before_with f t m = p ->
    (p ≤ latest_term_before_quorum_with f ms t)%nat ->
    latest_term_before_quorum_with f (<[x := m]> ms) t = latest_term_before_quorum_with f ms t.
  Proof.
    intros Hnone Hp Hle.
    rewrite /latest_term_before_quorum_with fmap_insert map_fold_insert_L; last first.
    { by rewrite lookup_fmap Hnone /=. }
    { intros x1 x2 n1 n2 n _ _ _. rewrite /latest_term_before_quorum_step. lia. }
    rewrite Hp {1}/latest_term_before_quorum_step.
    rewrite /latest_term_before_quorum_with in Hle.
    lia.
  Qed.

  Lemma latest_term_before_quorum_with_insert_ge `{Lookup nat B M}
    f (ms : gmap A M) (x : A) (m : M) t s :
    ms !! x = None ->
    latest_term_before_with f t m = s ->
    (latest_term_before_quorum_with f ms t ≤ s)%nat ->
    latest_term_before_quorum_with f (<[x := m]> ms) t = s.
  Proof.
    intros Hnone Hs Hge.
    rewrite /latest_term_before_quorum_with fmap_insert map_fold_insert_L; last first.
    { by rewrite lookup_fmap Hnone /=. }
    { intros x1 x2 n1 n2 n _ _ _. rewrite /latest_term_before_quorum_step. lia. }
    rewrite Hs {1}/latest_term_before_quorum_step.
    rewrite /latest_term_before_quorum_with in Hge.
    lia.
  Qed.

  Lemma latest_before_quorum_step_O_or_exists (ts : gmap A nat) :
    map_fold latest_term_before_quorum_step O ts = O ∨
    ∃ x, ts !! x = Some (map_fold latest_term_before_quorum_step O ts).
  Proof.
    apply (map_fold_weak_ind (λ p r, p = O ∨ ∃ x, r !! x = Some p)); first by left.
    intros x n m b Hmx IHm.
    unfold latest_term_before_quorum_step.
    destruct IHm as [-> | [y Hy]]; right.
    { exists x. rewrite lookup_insert_eq. by rewrite Nat.max_0_r. }
    destruct (decide (b ≤ n)%nat).
    { exists x. rewrite lookup_insert_eq. by replace (_ `max` _)%nat with n by lia. }
    exists y.
    assert (Hne : x ≠ y) by set_solver.
    rewrite lookup_insert_ne; last done. rewrite Hy.
    by replace (_ `max` _)%nat with b by lia.
  Qed.

  Lemma latest_term_before_quorum_step_ge (ts : gmap A nat) :
    map_Forall (λ _ t, (t ≤ map_fold latest_term_before_quorum_step O ts)%nat) ts.
  Proof.
    intros x t.
    apply (map_fold_weak_ind (λ p r, (r !! x = Some t -> t ≤ p)%nat)); first done.
    intros y n m b _ Hnr Hn.
    unfold latest_term_before_quorum_step.
    destruct (decide (y = x)) as [-> | Hne].
    { rewrite lookup_insert_eq in Hn. inversion_clear Hn. lia. }
    rewrite lookup_insert_ne in Hn; last done.
    specialize (Hnr Hn).
    lia.
  Qed.

  Lemma latest_term_before_quorum_ge `{Lookup nat B M} f ms t :
    map_Forall
      (λ _ (m : M), (latest_term_before_with f t m ≤ latest_term_before_quorum_with f ms t)%nat)
      ms.
  Proof.
    intros x l Hlookup.
    unfold latest_term_before_quorum_with.
    pose proof (latest_term_before_quorum_step_ge (latest_term_before_with f t <$> ms)) as Hstep.
    rewrite map_Forall_lookup in Hstep.
    apply (Hstep x (latest_term_before_with f t l)).
    rewrite lookup_fmap.
    by rewrite Hlookup.
  Qed.

  Lemma latest_before_quorum_step_in (ts : gmap A nat) :
    ts ≠ ∅ ->
    map_Exists (λ _ t, t = map_fold latest_term_before_quorum_step O ts) ts.
  Proof.
    intros Hnonempty.
    destruct (latest_before_quorum_step_O_or_exists ts) as [Hz | [x Hx]]; last first.
    { exists x. by eauto. }
    rewrite Hz.
    destruct (decide (O ∈ (map_img ts : gset nat))) as [Hin | Hnotin].
    { rewrite elem_of_map_img in Hin.
      destruct Hin as [x Hx].
      by exists x, O.
    }
    assert (Hallgz : ∀ t, t ∈ (map_img ts : gset nat) -> (0 < t)%nat).
    { intros t Ht. assert (Hnz : t ≠ O) by set_solver. lia. }
    apply map_choose in Hnonempty.
    destruct Hnonempty as (x & n & Hxn).
    apply latest_term_before_quorum_step_ge in Hxn as Hle.
    rewrite Hz in Hle.
    apply (elem_of_map_img_2 (SA:=gset nat)) in Hxn.
    apply Hallgz in Hxn.
    lia.
  Qed.

  Lemma latest_term_before_quorum_in `{Lookup nat B M} f ms t :
    ms ≠ ∅ ->
    map_Exists
      (λ _ (m : M), (latest_term_before_with f t m = latest_term_before_quorum_with f ms t)%nat)
      ms.
  Proof.
    intros Hnonempty.
    unfold latest_term_before_quorum_with.
    pose proof (latest_before_quorum_step_in (latest_term_before_with f t <$> ms)) as Hstep.
    rewrite fmap_empty_iff in Hstep.
    specialize (Hstep Hnonempty).
    destruct Hstep as (x & m & Hlookup & <-).
    rewrite lookup_fmap fmap_Some in Hlookup.
    destruct Hlookup as (l & Hlookup & Heq).
    by exists x, l.
  Qed.

  Lemma latest_term_before_quorum_with_None `{Lookup nat B M}
    f (ms : gmap A M) t p :
    (latest_term_before_quorum_with f ms t < p < t)%nat ->
    map_Forall (λ _ m, f (m !! p) = None) ms.
  Proof.
    intros Hp x m Hm.
    apply (latest_term_before_with_None _ t).
    pose proof (latest_term_before_quorum_ge f ms t _ _ Hm) as Hle. simpl in Hle.
    lia.
  Qed.

  Lemma latest_term_before_quorum_with_lt `{Lookup nat B M} f (ms : gmap A M) t:
    t ≠ O ->
    (latest_term_before_quorum_with f ms t < t)%nat.
  Proof.
    intros Hnz.
    rewrite /latest_term_before_quorum_with.
    set ts := (latest_term_before_with _ _ <$> ms).
    assert (map_Forall (λ _ t', (t' < t)%nat) ts) as Hlts.
    { subst ts.
      rewrite map_Forall_fmap.
      intros x m Hm.
      by apply latest_term_before_with_lt.
    }
    induction ts as [| x t' ts Hnone Hfold IH] using map_first_key_ind.
    { rewrite map_fold_empty. lia. }
    rewrite map_fold_insert_first_key; [| apply Hnone | apply Hfold].
    rewrite map_Forall_insert in Hlts; last apply Hnone.
    destruct Hlts as [Hlt Hlts].
    specialize (IH Hlts).
    rewrite {1}/latest_term_before_quorum_step.
    lia.
  Qed.

  Definition latest_term_before_quorum bs t :=
    latest_term_before_quorum_with id bs t.

  Definition longest_proposal_step (x : A) (cur prev : option ledger) :=
    match prev with
    | None => cur
    | Some lprev => match cur with
                   | Some lcur => if decide (length lprev < length lcur)%nat
                                 then cur
                                 else prev
                   | _ => prev
                   end
    end.

  Definition longest_proposal ovs :=
    map_fold longest_proposal_step None ovs.

  Definition ledger_in_term_with `{Lookup nat B M}
    (f : option B -> option ledger) (t : nat) (m : M) := f (m !! t).

  Definition ledger_in_term t ps :=
    ledger_in_term_with id t ps.

  Definition longest_proposal_in_term_with `{Lookup nat B M}
    (f : option B -> option ledger) (ms : gmap A M) t :=
    let ovs := fmap (ledger_in_term_with f t) ms in
    longest_proposal ovs.

  Definition longest_proposal_in_term bs t :=
    longest_proposal_in_term_with id bs t.

  Definition equal_latest_longest_proposal_with `{Lookup nat B M}
    (f : option B -> option ledger) (ms : gmap A M) t v :=
    if decide (t = O)
    then v = []
    else let t' := latest_term_before_quorum_with f ms t in
         longest_proposal_in_term_with f ms t' = Some v.

  Definition equal_latest_longest_proposal bsq t v :=
    equal_latest_longest_proposal_with id bsq t v.

  Definition valid_base_proposal bs t v :=
    ∃ bsq : gmap A proposals,
      bsq ⊆ bs ∧
      cquorum_size (dom bs) (dom bsq) ∧
      equal_latest_longest_proposal bsq t v.

  Definition valid_base_proposals bs psb :=
    map_Forall (λ n v, valid_base_proposal bs n v) psb.

  Definition valid_lb_ballot psb l :=
    ∀ t v, l !! t = Some v -> ∃ v', psb !! t = Some v' ∧ prefix v' v.

  Definition valid_lb_ballots bs psb :=
    map_Forall (λ _ l, valid_lb_ballot psb l) bs.

  Definition valid_ub_ballot ps l :=
    ∀ t v, l !! t = Some v -> ∃ v', ps !! t = Some v' ∧ prefix v v'.

  Definition valid_ub_ballots bs ps :=
    map_Forall (λ _ l, valid_ub_ballot ps l) bs.

  Definition valid_proposals ps psb :=
    map_Forall2 (λ _ (lb l : ledger), prefix lb l) psb ps.

  Definition free_term_with_partf (P : A -> nat -> Prop) (ts : gset nat) (x : A) (t : nat) :=
    ∀ t', P x t' -> (t < t')%nat -> t' ∉ ts.

  Definition free_terms_with_partf (P : A -> nat -> Prop) (ts : gset nat) (tm : gmap A nat) :=
    (∀ x1 x2 t, x1 ≠ x2 -> P x1 t -> not (P x2 t)) ∧
    map_Forall (λ x n, free_term_with_partf P ts x n) tm.

  Definition gt_prev_term (tm : gmap A nat) (x : A) (t : nat) :=
    (∃ t', tm !! x = Some t' ∧ (t' < t)%nat).

End def.

Definition max_nodes : Z := 16.

Definition is_term_of_node (x : u64) (t : nat) :=
  t `mod` max_nodes = (uint.Z x).

#[global]
Instance is_term_of_node_decision x t :
  Decision (is_term_of_node x t).
Proof. unfold is_term_of_node. apply _. Defined.

Lemma is_term_of_node_partitioned x1 x2 t :
  x1 ≠ x2 -> is_term_of_node x1 t -> not (is_term_of_node x2 t).
Proof.
  unfold is_term_of_node.
  intros Hne Hx1.
  rewrite Hx1.
  by apply word.unsigned_inj'.
Qed.

Definition free_terms ts tm :=
  free_terms_with_partf is_term_of_node ts tm.

Definition terms_all : gset nat := list_to_set (Z.to_nat <$> (seqZ 0 (2 ^ 64))).

Lemma elem_of_terms_all (n : nat) :
  n < 2 ^ 64 ->
  n ∈ terms_all.
Proof.
  intros Hn.
  rewrite /terms_all.
  rewrite elem_of_list_to_set list_elem_of_fmap.
  exists (Z.of_nat n).
  split; first lia.
  rewrite elem_of_seqZ.
  lia.
Qed.

Inductive pxst :=
| PaxosState (termc terml lsnc : nat) (ledger : ledger)
| PaxosStuck.

Inductive pxcmd :=
| CmdPaxosExtend (ents : ledger)
| CmdPaxosAppend (ent : byte_string)
| CmdPaxosPrepare (term : nat)
| CmdPaxosAdvance (term lsn : nat) (ents : ledger)
| CmdPaxosAccept (lsn : nat) (ents : ledger)
| CmdPaxosExpand (lsn : nat).

Definition byte_stringO := listO w8.
Definition byte_stringmlR := mono_listR byte_stringO.
Definition lsnmR := gmapR nat (dfrac_agreeR natO).
Canonical Structure nodedecO := leibnizO nodedec.
Definition declistR := mono_listR nodedecO.
Definition node_declistR := gmapR u64 declistR.
Definition ledgerO := leibnizO ledger.
Definition proposalmR := gmap_viewR nat (agreeR gnameO).
Definition node_proposalmR := gmapR u64 proposalmR.
Definition node_natmR := gmapR u64 (dfrac_agreeR natO).
Definition node_ledgerR := gmapR u64 (dfrac_agreeR ledgerO).
Definition pxcmdlO := leibnizO (list pxcmd).
Definition node_pxcmdlR := gmapR u64 (dfrac_agreeR pxcmdlO).
Definition node_stringR := gmapR u64 (agreeR byte_stringO).

Class paxos_ghostG (Σ : gFunctors) :=
  { #[global] byte_stringmlG :: inG Σ byte_stringmlR;
    #[global] cpoolG :: ghost_mapG Σ byte_string unit;
    #[global] proposalG :: ghost_mapG Σ nat gname;
    #[global] base_proposalG :: ghost_mapG Σ nat ledger;
    #[global] prepare_lsnG :: inG Σ lsnmR;
    #[global] node_declistG :: inG Σ node_declistR;
    #[global] node_proposalG :: inG Σ node_proposalmR;
    #[global] current_termG :: inG Σ node_natmR;
    #[global] ledger_termG :: inG Σ node_natmR;
    #[global] committed_lsnG :: inG Σ node_natmR;
    #[global] node_ledgerG :: inG Σ node_ledgerR;
    #[global] node_walG :: inG Σ node_pxcmdlR;
    #[global] node_wal_fnameG :: inG Σ node_stringR;
    #[global] trmlmG :: ghost_mapG Σ chan unit;
    #[global] paxos_stagedG :: stagedG Σ;
  }.

Definition paxos_ghostΣ :=
  #[ GFunctor lsnmR;
     ghost_mapΣ byte_string unit;
     ghost_mapΣ nat gname;
     GFunctor byte_stringmlR;
     ghost_mapΣ nat ledger;
     GFunctor node_declistR;
     GFunctor node_proposalmR;
     GFunctor node_natmR;
     GFunctor node_natmR;
     GFunctor node_natmR;
     GFunctor node_ledgerR;
     GFunctor node_pxcmdlR;
     GFunctor node_stringR;
     ghost_mapΣ chan unit;
     stagedΣ
    ].

#[global]
Instance subG_paxos_ghostG {Σ} :
  subG paxos_ghostΣ Σ → paxos_ghostG Σ.
Proof. solve_inG. Qed.

Record paxos_names := {
    consensus_log : gname;
    consensus_cpool : gname;
    proposal : gname;
    base_proposal : gname;
    prepare_lsn : gname;
    node_declist : gname;
    node_proposal : gname;
    current_term : gname;
    ledger_term : gname;
    committed_lsn : gname;
    node_ledger : gname;
    node_wal : gname;
    node_wal_fname : gname;
    trmlm : gname;
  }.
