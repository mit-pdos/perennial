From stdpp Require Export coPset.
From iris.algebra Require Import gmap auth agree gset coPset list vector excl.
From Perennial.algebra Require Import mlist.
From iris.proofmode Require Import tactics.
From Perennial.base_logic Require Export lib.own.
From iris.prelude Require Import options.

(* An inductive grammar of "basic" BI expressions. *)
Inductive bi_schema :=
| bi_sch_emp : bi_schema
| bi_sch_pure : Prop → bi_schema
| bi_sch_and : bi_schema → bi_schema → bi_schema
| bi_sch_or : bi_schema → bi_schema → bi_schema
| bi_sch_forall : ∀ A, (A → bi_schema) → bi_schema
| bi_sch_exist : ∀ A, (A → bi_schema) → bi_schema
| bi_sch_sep : bi_schema → bi_schema → bi_schema
| bi_sch_wand : bi_schema → bi_schema → bi_schema
| bi_sch_persistently : bi_schema → bi_schema
| bi_sch_later : bi_schema → bi_schema
| bi_sch_bupd : bi_schema → bi_schema
(* Schemas can include either fixed or mutable references to an iProp *)
| bi_sch_var_fixed : nat → bi_schema
| bi_sch_var_mut : nat → bi_schema
| bi_sch_wsat : bi_schema
| bi_sch_ownE : (nat → coPset) → bi_schema.

Canonical Structure bi_schemaO := leibnizO bi_schema.

(** All definitions in this file are internal to [fancy_updates] with the
exception of what's in the [invGS] module. The module [invGS] is thus exported in
[fancy_updates], which [wsat] is only imported. *)

Record invariant_level_names := { invariant_name : gname; }.

Global Instance invariant_level_names_eq_dec : EqDecision (invariant_level_names).
Proof.
  intros [] [].
  rewrite /Decision.
  repeat (decide equality).
Qed.

Module invGS.
  Class invGpreS (Σ : gFunctors) : Set := WsatPreG {
    inv_inPreG :> inG Σ (authR (gmapUR positive
                                    (prodR (agreeR (prodO (listO (laterO (iPropO Σ))) bi_schemaO))
                                           (optionR (prodR fracR (agreeR (listO (laterO (iPropO Σ)))))))));
    enabled_inPreG :> inG Σ coPset_disjR;
    disabled_inPreG :> inG Σ (gset_disjR positive);
    mlist_inPreG :> fmlistG (invariant_level_names) Σ;
  }.

  Class invGS (Σ : gFunctors) : Set := WsatG {
    inv_inG :> invGpreS Σ;
    inv_list_name : gname;
    enabled_name : gname;
    disabled_name : gname;
  }.

  Record inv_names :=
    { inv_names_list_name : gname;
      inv_names_enabled_name : gname;
      inv_names_disabled_name : gname;
    }.

  Definition inv_update_pre `(ipG : invGpreS Σ) (names : inv_names) :=
    {| inv_inG := ipG;
       inv_list_name := inv_names_list_name names;
       enabled_name := inv_names_enabled_name names;
       disabled_name := inv_names_disabled_name names |}.

  Definition inv_get_names `(iG : invGS Σ) : inv_names :=
    {| inv_names_list_name := inv_list_name;
      inv_names_enabled_name := enabled_name;
      inv_names_disabled_name := disabled_name |}.

  Definition invΣ : gFunctors :=
    #[GFunctor (authRF (gmapURF positive
                                (prodRF (agreeRF (prodOF (listOF (laterOF idOF)) (constOF bi_schemaO)))
                                        (optionRF (prodRF fracR (agreeRF (listOF (laterOF idOF))))))));
      GFunctor coPset_disjR;
      GFunctor (gset_disjR positive);
      fmlistΣ invariant_level_names
     ].

  (* XXX: magic commands to make the next proof not take 2min. *)
  Local Strategy 100 [authR].
  Local Strategy 100 [gmapURF].
  Local Strategy 100 [agreeR].
  Local Strategy 100 [prodR].
  Local Strategy 100 [optionR].
  Local Strategy 100 [prodO].
  Local Strategy 100 [laterO].
  Local Strategy 100 [listO].

  Global Instance subG_invΣ {Σ} : subG invΣ Σ → invGpreS Σ.
  Proof. solve_inG. Qed.
End invGS.
Import invGS.

Definition invariant_unfold {Σ} {n} sch (Ps : vec (iProp Σ) n) : agree (list (later (iPropO Σ)) * bi_schema) :=
  to_agree ((λ P, Next P) <$> (vec_to_list Ps), sch).
Definition inv_mut_unfold {Σ} {n} q (Ps : vec (iProp Σ) n) : option (frac * (agree (list (later (iPropO Σ))))) :=
  Some (q%Qp, to_agree ((λ P, Next P) <$> (vec_to_list Ps))).
Definition ownI `{!invGS Σ} {n} (lvl: nat) (i : positive) (sch: bi_schema) (Ps : vec (iProp Σ) n) : iProp Σ :=
  (∃ γs, fmlist_idx inv_list_name lvl γs ∗
         own (invariant_name γs) (◯ {[ i := (invariant_unfold sch Ps, ε) ]})).
Global Arguments ownI {_ _ _} _ _ _%I _%I.
Typeclasses Opaque ownI.
Global Instance: Params (@invariant_unfold) 1 := {}.
Global Instance: Params (@ownI) 3 := {}.

Definition ownI_mut `{!invGS Σ} {n} (lvl: nat) (i : positive) q (Qs : vec (iProp Σ) n) : iProp Σ :=
  (∃ (l: agree (list (later (iPropO Σ)) * bi_schema)) γs, fmlist_idx inv_list_name lvl γs ∗
         own (invariant_name γs) (◯ {[ i := (l, inv_mut_unfold q Qs) ]})).
Global Arguments ownI_mut {_ _ _} _ _ _%I.
Typeclasses Opaque ownI_mut.
Instance: Params (@inv_mut_unfold) 1 := {}.
Instance: Params (@ownI_mut) 3 := {}.

Definition ownE `{!invGS Σ} (E : coPset) : iProp Σ :=
  own enabled_name (CoPset E).
Typeclasses Opaque ownE.
Global Instance: Params (@ownE) 3 := {}.

Definition ownD `{!invGS Σ} (E : gset positive) : iProp Σ :=
  own disabled_name (GSet E).
Typeclasses Opaque ownD.
Global Instance: Params (@ownD) 3 := {}.

Definition inv_cmra_fmap `{!invGS Σ} (v: (list (iProp Σ) * bi_schema) * list (iProp Σ)) :=
  let '((Ps, sch), Qs) := v in
  (invariant_unfold sch (list_to_vec Ps), inv_mut_unfold 1%Qp (list_to_vec Qs)).

Fixpoint bi_schema_pre `{!invGS Σ} n (Ps Ps_mut: list (iProp Σ)) wsat (sch: bi_schema) :=
  match sch with
  | bi_sch_emp => emp
  | bi_sch_pure φ => ⌜φ⌝
  | bi_sch_and sch1 sch2 => bi_schema_pre n Ps Ps_mut wsat sch1 ∧ bi_schema_pre n Ps Ps_mut wsat sch2
  | bi_sch_or sch1 sch2 => bi_schema_pre n Ps Ps_mut wsat sch1 ∨ bi_schema_pre n Ps Ps_mut wsat sch2
  | bi_sch_forall A sch => ∀ (a: A),  bi_schema_pre n Ps Ps_mut wsat (sch a)
  | bi_sch_exist A sch => ∃ (a: A),  bi_schema_pre n Ps Ps_mut wsat (sch a)
  | bi_sch_sep sch1 sch2 => bi_schema_pre n Ps Ps_mut wsat sch1 ∗ bi_schema_pre n Ps Ps_mut wsat sch2
  | bi_sch_wand sch1 sch2 => bi_schema_pre n Ps Ps_mut wsat sch1 -∗ bi_schema_pre n Ps Ps_mut wsat sch2
  | bi_sch_persistently sch => <pers> bi_schema_pre n Ps Ps_mut wsat sch
  | bi_sch_later sch => ▷ bi_schema_pre n Ps Ps_mut wsat sch
  | bi_sch_bupd sch => |==> bi_schema_pre n Ps Ps_mut wsat sch
  | bi_sch_var_fixed i =>
    match (Ps !! i) with
    | None => emp
    | Some P => P
    end
  | bi_sch_var_mut i =>
    match (Ps_mut !! i) with
    | None => emp
    | Some P => P
    end
  | bi_sch_wsat => wsat
  | bi_sch_ownE E => ownE (E n)
  end%I.

Definition wsat_pre `{!invGS Σ} n bi_schema_interp :=
  (∃ I : gmap positive ((list (iProp Σ) * bi_schema) * list (iProp Σ)),
        (∃ γs, fmlist_idx inv_list_name n γs ∗
             own (invariant_name γs) (● (inv_cmra_fmap <$> I : gmap _ _))) ∗
        [∗ map] i ↦ Qs ∈ I, (bi_schema_interp (bi_later <$> Qs.1.1) (bi_later <$> Qs.2) Qs.1.2 ∗
                             ownI_mut n i (1/2)%Qp (list_to_vec Qs.2) ∗
                             ownD {[i]}) ∨
                            ownE {[i]})%I.

Fixpoint bi_schema_interp `{!invGS Σ} n (Ps Ps_mut: list (iProp Σ)) sch {struct n} :=
  match n with
  | O => bi_schema_pre O Ps Ps_mut True%I sch
  | S n' => bi_schema_pre (S n') Ps Ps_mut (wsat_pre n' (bi_schema_interp n') ∗ wsat n')%I sch
  end
  with
  wsat `{!invGS Σ} n :=
  match n with
    | S n =>
  (∃ I : gmap positive ((list (iProp Σ) * bi_schema) * list (iProp Σ)),
        (∃ γs, fmlist_idx inv_list_name n γs ∗
             own (invariant_name γs) (● (inv_cmra_fmap <$> I : gmap _ _))) ∗
        [∗ map] i ↦ Qs ∈ I, (bi_schema_interp n (bi_later <$> Qs.1.1) (bi_later <$> Qs.2) Qs.1.2 ∗
                             ownI_mut n i (1/2)%Qp (list_to_vec Qs.2) ∗
                             ownD {[i]}) ∨
                            ownE {[i]})
    ∗ wsat n
    | O => True
  end%I.
Global Arguments bi_schema_interp {_ _} _ _ _ _.
Global Arguments wsat {_ _} _.

Lemma wsat_unfold `{!invGS Σ} n:
  wsat n =
  match n with
    | S n =>
  (∃ I : gmap positive ((list (iProp Σ) * bi_schema) * list (iProp Σ)),
        (∃ γs, fmlist_idx inv_list_name n γs ∗
             own (invariant_name γs) (● (inv_cmra_fmap <$> I : gmap _ _))) ∗
        [∗ map] i ↦ Qs ∈ I, (bi_schema_interp n (bi_later <$> Qs.1.1) (bi_later <$> Qs.2) Qs.1.2 ∗
                             ownI_mut n i (1/2)%Qp (list_to_vec Qs.2) ∗
                             ownD {[i]}) ∨
                            ownE {[i]})
    ∗ wsat n
    | O => True
  end%I.
Proof. rewrite /=. destruct n => //=. Qed.

Lemma bi_schema_interp_unfold `{!invGS Σ} n Ps Ps_mut sch :
  bi_schema_interp n Ps Ps_mut sch =
  match sch with
  | bi_sch_emp => emp
  | bi_sch_pure φ => ⌜φ⌝
  | bi_sch_and sch1 sch2 => bi_schema_interp n Ps Ps_mut sch1 ∧ bi_schema_interp n Ps Ps_mut sch2
  | bi_sch_or sch1 sch2 => bi_schema_interp n Ps Ps_mut sch1 ∨ bi_schema_interp n Ps Ps_mut sch2
  | bi_sch_forall A sch => ∀ (a: A),  bi_schema_interp n Ps Ps_mut (sch a)
  | bi_sch_exist A sch => ∃ (a: A),  bi_schema_interp n Ps Ps_mut (sch a)
  | bi_sch_sep sch1 sch2 => bi_schema_interp n Ps Ps_mut sch1 ∗ bi_schema_interp n Ps Ps_mut sch2
  | bi_sch_wand sch1 sch2 => bi_schema_interp n Ps Ps_mut sch1 -∗ bi_schema_interp n Ps Ps_mut sch2
  | bi_sch_persistently sch => <pers> bi_schema_interp n Ps Ps_mut sch
  | bi_sch_later sch => ▷ bi_schema_interp n Ps Ps_mut sch
  | bi_sch_bupd sch => |==> bi_schema_interp n Ps Ps_mut sch
  | bi_sch_var_fixed i =>
    match (Ps !! i) with
    | None => emp
    | Some P => P
    end
  | bi_sch_var_mut i =>
    match (Ps_mut !! i) with
    | None => emp
    | Some P => P
    end
  | bi_sch_wsat => wsat n
  | bi_sch_ownE E => ownE (E n)
  end%I.
Proof. destruct n, sch => //=. Qed.

Opaque wsat bi_schema_interp_unfold.

Section wsat.
Context `{!invGS Σ}.
Implicit Types P : iProp Σ.

Lemma wsat_le_acc n1 n2:
  n1 ≤ n2 →
  wsat n2 ⊢ wsat n1 ∗ (wsat n1 -∗ wsat n2).
Proof.
  induction 1.
  - iIntros "$". eauto.
  - rewrite wsat_unfold.
    iIntros "($&Hm)".
    iDestruct (IHle with "Hm") as "($&Hclo)".
    auto.
Qed.

(* Invariants *)
Lemma dist_later_vec_to_list {A: ofe} {m} n (l1 l2 : vec A m):
  dist_later n l1 l2 ↔ dist_later n (vec_to_list l1) (vec_to_list l2).
Proof. destruct n => //=. Qed.
Local Instance invariant_unfold_contractive' m sch : Contractive (@invariant_unfold Σ m sch).
Proof.
  intros n l1 l2 Hd.
  rewrite /invariant_unfold.
  specialize (vec_to_list_same_length l1 l2) => Hlen.
  revert Hd; rewrite dist_later_vec_to_list.
  remember (vec_to_list l1) as l1' eqn:Heq1.
  remember (vec_to_list l2) as l2' eqn:Heq2.
  rewrite -Heq1 -Heq2.
  clear l1 l2 Heq1 Heq2.
  revert l2' Hlen.
  induction l1' => l2' Hlen Hd.
  - destruct l2' => //=.
  - destruct l2'; first by (simpl in Hlen; congruence).
    apply to_agree_ne => //=.
    apply pair_ne; last done. econstructor.
    { destruct n; eauto. apply Next_contractive. inversion Hd; subst; eauto => //=. }
    efeed pose proof (IHl1' l2') as Hagree; eauto.
    { destruct n; eauto. inversion Hd; subst; eauto. }
    apply to_agree_injN in Hagree. eapply Hagree.
Qed.
Global Instance ownI_contractive n lvl i sch : Contractive (@ownI Σ _ n lvl i sch).
Proof. rewrite /ownI. solve_contractive. Qed.
Global Instance ownI_persistent n lvl i sch (Ps: vec _ n) : Persistent (ownI lvl i sch Ps).
Proof. rewrite /ownI. apply _. Qed.

Lemma ownE_empty : ⊢ |==> ownE ∅.
Proof.
  rewrite /bi_emp_valid.
  by rewrite (own_unit (coPset_disjUR) enabled_name).
Qed.
Lemma ownE_op E1 E2 : E1 ## E2 → ownE (E1 ∪ E2) ⊣⊢ ownE E1 ∗ ownE E2.
Proof. intros. by rewrite /ownE -own_op coPset_disj_union. Qed.
Lemma ownE_disjoint E1 E2 : ownE E1 ∗ ownE E2 ⊢ ⌜E1 ## E2⌝.
Proof. rewrite /ownE -own_op own_valid. by iIntros (?%coPset_disj_valid_op). Qed.
Lemma ownE_op' E1 E2 : ⌜E1 ## E2⌝ ∧ ownE (E1 ∪ E2) ⊣⊢ ownE E1 ∗ ownE E2.
Proof.
  iSplit; [iIntros "[% ?]"; by iApply ownE_op|].
  iIntros "HE". iDestruct (ownE_disjoint with "HE") as %?.
  iSplit; first done. iApply ownE_op; by try iFrame.
Qed.
Lemma ownE_singleton_twice i : ownE {[i]} ∗ ownE {[i]} ⊢ False.
Proof. rewrite ownE_disjoint. iIntros (?); set_solver. Qed.

Lemma ownD_empty : ⊢ |==> ownD ∅.
Proof.
  rewrite /bi_emp_valid.
  by rewrite (own_unit (gset_disjUR positive) disabled_name).
Qed.
Lemma ownD_op E1 E2 : E1 ## E2 → ownD (E1 ∪ E2) ⊣⊢ ownD E1 ∗ ownD E2.
Proof. intros. by rewrite /ownD -own_op gset_disj_union. Qed.
Lemma ownD_disjoint E1 E2 : ownD E1 ∗ ownD E2 ⊢ ⌜E1 ## E2⌝.
Proof. rewrite /ownD -own_op own_valid. by iIntros (?%gset_disj_valid_op). Qed.
Lemma ownD_op' E1 E2 : ⌜E1 ## E2⌝ ∧ ownD (E1 ∪ E2) ⊣⊢ ownD E1 ∗ ownD E2.
Proof.
  iSplit; [iIntros "[% ?]"; by iApply ownD_op|].
  iIntros "HE". iDestruct (ownD_disjoint with "HE") as %?.
  iSplit; first done. iApply ownD_op; by try iFrame.
Qed.
Lemma ownD_singleton_twice i : ownD {[i]} ∗ ownD {[i]} ⊢ False.
Proof. rewrite ownD_disjoint. iIntros (?); set_solver. Qed.

Lemma list_equivI_O {A: ofe} {M} (m1 m2: list A) : m1 ≡ m2 ⊣⊢@{uPredI M} ∀ i, m1 !! i ≡ m2 !! i.
Proof.
  uPred.unseal => //=.
  split => n x Hval. split.
  - intros ? Hequiv. apply list_dist_lookup; eauto.
  - intros Hequiv. apply list_dist_lookup; eauto.
Qed.
Lemma list_equivI_1 {A: ofe} {M} (m1 m2: list A) : m1 ≡ m2 ⊢@{uPredI M} ∀ i, m1 !! i ≡ m2 !! i.
Proof.
  uPred.unseal => //=.
  split => n x Hval Hequiv i. apply list_dist_lookup; eauto.
Qed.
Lemma list_equivI_length {A: ofe} {M} (m1 m2: list A) : m1 ≡ m2 ⊢@{uPredI M} ⌜ length m1 = length m2 ⌝.
Proof.
  uPred.unseal => //=.
  split => n x Hval Hequiv.
  eapply (Forall2_length _ m1 m2 Hequiv).
Qed.
Lemma vec_equivI_1 {A: ofe} {M} {n} (m1 m2: vec A n) :
  m1 ≡ m2 ⊢@{uPredI M} ∀ i, vec_to_list m1 !! i ≡ vec_to_list m2 !! i.
Proof.
  uPred.unseal => //=.
  split => ? x Hval Hequiv i. apply list_dist_lookup; eauto.
Qed.

Lemma invariant_lookup_weak I {n} γ i sch (Ps: vec _ n) :
  own γ (● (inv_cmra_fmap <$> I : gmap _ _)) ∗
  own γ (◯ {[i := (invariant_unfold sch Ps, ε)]})  ⊢
  ∃ Qs Qs_mut, ⌜I !! i = Some ((Qs, sch), Qs_mut)⌝ ∗
               ⌜ length Qs = length Ps ⌝ ∗
               ∀ i, ▷ (Qs !! i ≡ vec_to_list Ps !! i).
Proof.
  rewrite -own_op own_valid auth_both_validI /=. iIntros "[#HI #HvI]".
  iDestruct "HI" as (I') "HI". rewrite gmap_equivI gmap_validI.
  iSpecialize ("HI" $! i). iSpecialize ("HvI" $! i).
  rewrite lookup_fmap lookup_op lookup_singleton option_equivI.
  case: (I !! i)=> [[[Q sch'] Qmut]|] /=; [|case: (I' !! i)=> [Q'|] /=; by iExFalso].
  iExists Q, Qmut. (* iSplit; first done. *)
  iAssert (invariant_unfold sch' (list_to_vec Q) ≡ invariant_unfold sch Ps)%I as "Hequiv".
  { case: (I' !! i)=> [[Q' Qmut']|] //=.
    - iRewrite "HI" in "HvI". rewrite option_validI prod_validI agree_validI.
      iDestruct "HvI" as "(HvI&_)". simpl.
      iRewrite -"HvI" in "HI". rewrite -pair_op agree_idemp prod_equivI.
      iDestruct "HI" as "($&_)".
    - rewrite prod_equivI. iDestruct "HI" as "($&_)".
  }
  rewrite /invariant_unfold.
  rewrite agree_equivI prod_equivI //=. iDestruct "Hequiv" as "(Hequiv&Hsch_equiv)".
  iSplit.
  { iDestruct "Hsch_equiv" as %Heq. iPureIntro. move:Heq => //=. congruence. }
  iDestruct (list_equivI_length with "Hequiv") as %Hlen.
  iSplit.
  { iPureIntro. move: Hlen. rewrite ?fmap_length vec_to_list_to_vec //=. }
  rewrite list_equivI_1. iIntros (j).
  iSpecialize ("Hequiv" $! j).
  rewrite ?list_lookup_fmap vec_to_list_to_vec.
  rewrite option_equivI.
  destruct (Q !! j) as [Q0|] eqn:HeqQ;
  destruct (vec_to_list Ps !! j) as [P0|] eqn:HeqP;
  rewrite ?HeqQ ?HeqP //=.
  { rewrite //= ?later_equivI //=. iNext. by iRewrite "Hequiv". }
Qed.

Lemma agree_equiv_inclI {M} {A: ofe} (a b: A) c : to_agree a ≡ to_agree b ⋅ c ⊢@{uPredI M} (b ≡ a).
Proof.
  uPred.unseal. split.
  intros n ? Hx Heq. apply (to_agree_includedN n b a). exists c; eauto.
Qed.

Lemma agree_op_invI {M} {A : ofe} (x y : agree A): ✓ (x ⋅ y) ⊢@{uPredI M} x ≡ y.
Proof. uPred.unseal. split. intros n ? Hx Heq. by apply agree_op_invN. Qed.

Lemma invariant_lookup_strong I {n m} γ i q sch (Ps: vec _ n) (Ps_mut: vec _ m) :
  own γ (● (inv_cmra_fmap <$> I : gmap _ _)) ∗
  own γ (◯ {[i := (invariant_unfold sch Ps, inv_mut_unfold q Ps_mut)]})  ⊢
  ∃ Qs Qs_mut, ⌜I !! i = Some ((Qs, sch), Qs_mut)⌝ ∗
               ⌜ length Qs = length Ps ⌝ ∗
               ⌜ length Qs_mut = length Ps_mut ⌝ ∗
               (∀ i, ▷ (Qs !! i ≡ vec_to_list Ps !! i)) ∗
               (∀ i, ▷ (Qs_mut !! i ≡ vec_to_list Ps_mut !! i)).
Proof.
  rewrite -own_op own_valid auth_both_validI /=. iIntros "[#HI #HvI]".
  iDestruct "HI" as (I') "HI". rewrite gmap_equivI gmap_validI.
  iSpecialize ("HI" $! i). iSpecialize ("HvI" $! i).
  rewrite lookup_fmap lookup_op lookup_singleton option_equivI.
  case: (I !! i)=> [[[Q sch'] Qmut]|] /=; [|case: (I' !! i)=> [Q'|] /=; by iExFalso].
  iExists Q, Qmut. (* iSplit; first done. *)
  iAssert (invariant_unfold sch' (list_to_vec Q) ≡ invariant_unfold sch Ps)%I as "Hequiv".
  { case: (I' !! i)=> [[Q' Qmut']|] //=.
    - iRewrite "HI" in "HvI". rewrite option_validI prod_validI agree_validI.
      iDestruct "HvI" as "(HvI&_)". simpl.
      iRewrite -"HvI" in "HI". rewrite -pair_op agree_idemp prod_equivI.
      iDestruct "HI" as "($&_)".
    - rewrite prod_equivI. iDestruct "HI" as "($&_)".
  }
  (* XXX: this asserts a bundled equivalence that we then break apart right afterward. *)
  iAssert (inv_mut_unfold q (list_to_vec Qmut) ≡ inv_mut_unfold q Ps_mut)%I as "Hequiv_mut".
  {
    case: (I' !! i)=> [[Q' Qmut']|] //=.
    - iRewrite "HI" in "HvI". rewrite option_validI prod_validI agree_validI.
      iDestruct "HvI" as "(HvI&_)". simpl.
      iRewrite -"HvI" in "HI". rewrite -pair_op agree_idemp prod_equivI //=.
      iDestruct "HI" as "(_&Hi)".
      rewrite /inv_mut_unfold option_equivI ?prod_equivI; iSplit => //=.
      destruct Qmut' as [(?&?)|]; last first.
      { iEval (rewrite right_id) in "Hi".
        rewrite option_equivI prod_equivI; iDestruct "Hi" as "(_&$)". }
      rewrite -Some_op -pair_op.
      rewrite option_equivI prod_equivI. iDestruct "Hi" as "(_&Hi)" => //=.
      iDestruct (agree_equiv_inclI with "Hi") as "Heq". by iRewrite "Heq".
    - rewrite prod_equivI => //=.
      rewrite /inv_mut_unfold ?option_equivI ?prod_equivI; iSplit => //=.
      iDestruct "HI" as "(_&_&$)".
  }
  rewrite /invariant_unfold.
  rewrite agree_equivI prod_equivI //=. iDestruct "Hequiv" as "(Hequiv&Hsch_equiv)".
  rewrite /inv_mut_unfold.
  rewrite option_equivI prod_equivI agree_equivI. iDestruct "Hequiv_mut" as "(_&Hequiv_mut)".
  iSplit.
  { iDestruct "Hsch_equiv" as %Heq. iPureIntro. move:Heq => //=. congruence. }
  iDestruct (list_equivI_length with "Hequiv") as %Hlen.
  iDestruct (list_equivI_length with "Hequiv_mut") as %Hlen_mut.
  iSplit.
  { iPureIntro. move: Hlen. rewrite ?fmap_length vec_to_list_to_vec //=. }
  iSplit.
  { iPureIntro. move: Hlen_mut. rewrite ?fmap_length vec_to_list_to_vec //=. }
  rewrite ?list_equivI_1.
  iSplitL "Hequiv HI".
  - iIntros (j).
    iSpecialize ("Hequiv" $! j).
    rewrite ?list_lookup_fmap ?vec_to_list_to_vec.
    rewrite option_equivI.
    destruct (Q !! j) as [Q0|] eqn:HeqQ;
    destruct (vec_to_list Ps !! j) as [P0|] eqn:HeqP;
    rewrite ?HeqQ ?HeqP //=.
    { rewrite //= ?later_equivI //=. iNext. by iRewrite "Hequiv". }
  - iIntros (j).
    iSpecialize ("Hequiv_mut" $! j).
    rewrite ?list_lookup_fmap ?vec_to_list_to_vec.
    rewrite option_equivI.
    destruct (Qmut !! j) as [Q0|] eqn:HeqQ;
    destruct (vec_to_list Ps_mut !! j) as [P0|] eqn:HeqP;
    rewrite ?HeqQ ?HeqP //=.
    { rewrite //= ?later_equivI //=. iNext. by iRewrite "Hequiv_mut". }
Qed.


Lemma equivI_elim_own {A: cmra} `{Hin: inG Σ A} γ (a b: A):
  (a ≡ b) -∗ own γ a -∗ own γ b.
Proof. iIntros "Hequiv". iRewrite "Hequiv". eauto. Qed.

Lemma ownI_mut_later {n m} lvl i q (Qs_mut: vec _ n) (Ps_mut: vec _ m):
  n = m →
  (∀ i, ▷ (vec_to_list Qs_mut !! i ≡ vec_to_list Ps_mut !! i)) -∗
  ownI_mut lvl i q (Qs_mut) -∗
  ownI_mut lvl i q (Ps_mut).
Proof.
  iIntros (Hlen) "#HPQ". rewrite /ownI_mut.
  iDestruct 1 as (l γs) "(Hidx&Hown)".
  iExists l, γs; iFrame.
  iAssert (inv_mut_unfold q Ps_mut ≡ inv_mut_unfold q Qs_mut)%I as "Heq".
  { rewrite /inv_mut_unfold option_equivI prod_equivI => //=; iSplit; first done.
    rewrite agree_equivI ?vec_to_list_to_vec list_equivI_O.
    iIntros (j).
    rewrite ?list_lookup_fmap.
    iSpecialize ("HPQ" $! j).
    rewrite ?option_equivI.
    destruct (vec_to_list Qs_mut !! j) as [Q0|] eqn:HeqQ;
    destruct (vec_to_list Ps_mut !! j) as [P0|] eqn:HeqP;
    rewrite ?HeqQ ?HeqP //=.
    * rewrite later_equivI. iNext. by iRewrite "HPQ".
    * exfalso. apply lookup_ge_None_1 in HeqP. apply lookup_lt_Some in HeqQ.
      rewrite ?vec_to_list_length in HeqQ HeqP. lia.
    * exfalso. apply lookup_ge_None_1 in HeqQ. apply lookup_lt_Some in HeqP.
      rewrite ?vec_to_list_length in HeqQ HeqP. lia. }
  iRewrite "Heq".
  iExact "Hown".
Qed.

Lemma bi_schema_interp_ctx_later lvl sch (Qs Qs_mut Ps Ps_mut: list (iProp Σ)):
  (∀ i, ▷ (Qs !! i ≡ Ps !! i)) -∗
  (∀ i, ▷ (Qs_mut !! i ≡ Ps_mut !! i)) -∗
  bi_schema_interp lvl (bi_later <$> Qs) (bi_later <$> Qs_mut) sch ∗-∗
  bi_schema_interp lvl (bi_later <$> Ps) (bi_later <$> Ps_mut) sch.
Proof.
  iIntros "#HPQ1 #HPQ2".
  iInduction sch as [] "IH"; rewrite ?bi_schema_interp_unfold; try auto; rewrite //=.
  - iSplit; iIntros "H"; iSplit;
    try iApply "IH"; try iApply "IH1"; try iDestruct "H" as "($&_)"; try iDestruct "H" as "(_&$)".
  - iSplit; iIntros "HQ"; iDestruct "HQ" as "[HQ|HQ]";
      try (iLeft; by iApply "IH");
      try (iRight; by iApply "IH1").
  - iSplit; simpl; iIntros "H"; iIntros (a); iApply "IH"; eauto.
  - iSplit; simpl; iDestruct 1 as (a) "H"; iExists a; by iApply "IH"; eauto.
  - iSplit; simpl; iDestruct 1 as "(H1&H2)"; iSplitL "H1"; try (by iApply "IH"); try (by iApply "IH1").
  - iSplit; simpl; iIntros "Hw H1"; iApply "IH1"; iApply "Hw"; iApply "IH"; auto.
  - iSplit; simpl; iIntros "#H !>"; iApply "IH"; eauto.
  - iSplit; simpl; iIntros "H !>"; iApply "IH"; eauto.
  - iSplit; simpl; iIntros ">H"; iApply "IH"; eauto.
  - iSpecialize ("HPQ1" $! n). iSplit; rewrite ?list_lookup_fmap;
    destruct (Qs !! n) as [|] eqn:Heq1; rewrite Heq1 => //=;
    destruct (Ps !! n) as [|] eqn:Heq2; rewrite Heq2 => //=;
    iIntros; rewrite option_equivI; auto; iNext.
    * by iRewrite -"HPQ1".
    * by iRewrite "HPQ1".
  - iSpecialize ("HPQ2" $! n). iSplit; rewrite ?list_lookup_fmap;
    destruct (Qs_mut !! n) as [|] eqn:Heq1; rewrite Heq1 => //=;
    destruct (Ps_mut !! n) as [|] eqn:Heq2; rewrite Heq2 => //=;
    iIntros; rewrite option_equivI; auto; iNext.
    * by iRewrite -"HPQ2".
    * by iRewrite "HPQ2".
Qed.

Lemma ownI_open {n} lvl i sch (Ps: vec _ n) :
  wsat (S lvl) ∗ ownI lvl i sch Ps ∗ ownE {[i]} ⊢
  wsat (S lvl) ∗ (∃ m (Ps_mut: vec _ m),
                        bi_schema_interp lvl (bi_later <$> (vec_to_list Ps))
                                             (bi_later <$> (vec_to_list Ps_mut)) sch ∗
                        ownI_mut lvl i (1/2)%Qp Ps_mut) ∗ ownD {[i]}.
Proof.
  rewrite /ownI wsat_unfold.
  iIntros "((Hw&$) & Hi & HiE)". iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct "Hw" as (γs1) "(#Hidx1&Hw)".
  iDestruct "Hi" as (γs2) "(#Hidx2&Hi)".
  iDestruct (fmlist_idx_agree_1 with "Hidx1 Hidx2") as %->.
  iDestruct (invariant_lookup_weak I _ i sch Ps with "[$]") as (Qs Qs_mut HIlookup Hlen) "#HPQ".
  iDestruct (big_sepM_delete _ _ i with "HI") as "[[[HQ [HQ_mut $]]|HiE'] HI]"; eauto.
  - iSplitR "HQ HQ_mut"; last first.
    { iExists (length Qs_mut), (list_to_vec Qs_mut). iFrame.
      rewrite //=. rewrite vec_to_list_to_vec. iApply (bi_schema_interp_ctx_later with "[HPQ] [] [$]").
      - iIntros (i0). iNext => //=. by iRewrite -("HPQ" $! i0).
      - iIntros (i0). iNext => //=.
    }
    iExists I. iSplitL "Hw".
    { by eauto with iFrame. }
    iApply (big_sepM_delete _ _ i); eauto.
    iFrame "HI"; eauto.
  - iDestruct (ownE_singleton_twice with "[$HiE $HiE']") as %[].
Qed.

Lemma gmap_validI_singleton `{Countable K} {A: cmra} {M: ucmra} (i: K) (a: A) :
  ✓ {[ i := a ]} ⊣⊢@{uPredI M} ✓ a.
Proof.
  rewrite gmap_validI. iSplit.
  - iIntros "H". iSpecialize ("H" $! i). rewrite lookup_singleton option_validI //=.
  - iIntros "Ha". iIntros (j). destruct (decide (i = j)).
    * subst. rewrite lookup_singleton option_validI //=.
    * rewrite lookup_singleton_ne //=.
Qed.

Lemma ownI_close {n m} lvl i sch (Ps : vec _ n) (Ps_mut: vec _ m) :
  wsat (S lvl) ∗
  ownI lvl i sch Ps ∗
  ownI_mut lvl i (1/2)%Qp Ps_mut ∗
  bi_schema_interp lvl (bi_later <$> (vec_to_list Ps)) (bi_later <$> (vec_to_list Ps_mut)) sch ∗
  ownD {[i]} ⊢
  wsat (S lvl) ∗ ownE {[i]}.
Proof.
  rewrite /ownI wsat_unfold.
  iIntros "((Hw&$) & Hi & Hi_mut & HP & HiD)". iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct "Hw" as (γs1) "(#Hidx1&Hw)".
  iDestruct "Hi" as (γs2) "(#Hidx2&Hi)".
  iEval (rewrite /ownI_mut) in "Hi_mut".
  iDestruct "Hi_mut" as (? γs2_mut) "(#Hidx3&Hi_mut)".
  iDestruct (fmlist_idx_agree_1 with "Hidx1 Hidx2") as %->.
  iDestruct (fmlist_idx_agree_1 with "Hidx3 Hidx2") as %->.
  iDestruct (invariant_lookup_strong with "[$Hw Hi Hi_mut]")
    as (Qs Qs_mut HIlookup Hlen Hlen_mut) "(#HPQ&#HPQ_mut)".
  { iCombine "Hi Hi_mut" as "Hcombine".
    iDestruct (own_valid with "Hcombine") as "#Hval".
    rewrite auth_frag_validI gmap_validI_singleton prod_validI /=.
    rewrite agree_validI. iDestruct "Hval" as "(Hval_agree&_)".
    iRewrite -"Hval_agree" in "Hcombine".
    rewrite agree_idemp left_id. eauto.
  }
  iDestruct (big_sepM_delete _ _ i with "HI") as "[[[HQ [HQmut ?]]|$] HI]"; eauto.
  - iDestruct (ownD_singleton_twice with "[$]") as %[].
  - iExists I. iSplitL "Hw".
    { by eauto with iFrame. }
    iApply (big_sepM_delete _ _ i); eauto.
    iFrame "HI". iLeft. iFrame "HiD". iClear "Hi".
    iSplitL "HP".
    { by iApply (bi_schema_interp_ctx_later with "HPQ HPQ_mut"). }
    iApply (ownI_mut_later _ _ _ Ps_mut (list_to_vec Qs_mut)).
    { rewrite -(vec_to_list_length Ps_mut). auto. }
    { iIntros (j). rewrite vec_to_list_to_vec. iNext. by iRewrite ("HPQ_mut" $! j). }
    iExists _, _. iFrame "Hidx2"; eauto.
Qed.

Lemma ownI_mut_update {m m'} γ (i: positive) I x
      (Qs_mut: vec (iProp Σ) m) (Qs_mut': vec (iProp Σ) m') :
  own γ (● (inv_cmra_fmap <$> I : gmap _ _)) -∗
  own γ (◯ {[i := (x, inv_mut_unfold 1%Qp Qs_mut)]}) ==∗
  ∃ PsI schI QsI (Hlook: I !! i = Some ((PsI, schI), QsI)),
  own γ (● (inv_cmra_fmap <$> (<[i := ((PsI, schI), vec_to_list Qs_mut')]> I) : gmap _ _)) ∗
  own γ (◯ {[i := (x, inv_mut_unfold 1%Qp Qs_mut')]}).
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_valid_2 with "Hauth Hfrag")
      as "#Hval".
  (* This is more complicated than something like gen_heap_update, because we cannot eliminate
     the validity to a pure fact. *)
  destruct (I !! i) as [((QsI&schI)&Qs_mutI)|] eqn:Hlookup; last first.
  {
    rewrite auth_both_validI.
    iDestruct "Hval" as "(Hval&_)".
    iDestruct "Hval" as (I') "Heq".
    rewrite gmap_equivI. iSpecialize ("Heq" $! i). rewrite lookup_fmap Hlookup //=.
    rewrite lookup_op lookup_singleton option_equivI.
    case (I' !! i) => //=.
  }
  iExists QsI, schI, Qs_mutI.
  iMod (own_update_2 with "Hauth Hfrag") as "[$ $]"; last done.
  { eapply auth_update. rewrite fmap_insert. eapply singleton_local_update.
    { rewrite lookup_fmap Hlookup //=. }
    apply prod_local_update.
    { rewrite //=. }
    { rewrite /= /inv_mut_unfold //=. rewrite ?vec_to_list_to_vec.
      apply option_local_update.
      apply exclusive_local_update => //=.
    }
  }
Qed.

Lemma ownI_full_split_frac γ x i q {n} (Ps_mut: vec _ n):
  own γ (◯ {[i := (x, inv_mut_unfold q Ps_mut)]}) -∗
  own γ (◯ {[i := (x, inv_mut_unfold (q/2) Ps_mut)]}) ∗
  own γ (◯ {[i := (x, inv_mut_unfold (q/2) Ps_mut)]}).
Proof.
  rewrite -own_op. iIntros "H". iApply (own_proper with "H").
  apply auth_frag_proper => //=.
  intros j. rewrite lookup_op. destruct (decide (i = j)); last first.
  { rewrite ?lookup_singleton_ne //=. }
  subst. rewrite ?lookup_singleton /=.
  rewrite -Some_op -pair_op agree_idemp /inv_mut_unfold.
  rewrite -Some_op -pair_op agree_idemp.
  repeat f_equiv. by rewrite frac_op Qp_div_2.
Qed.

Lemma ownI_full_split_comp γ x y i:
  own γ (◯ {[i := (x, y)]}) -∗
  own γ (◯ {[i := (x, ε)]}) ∗
  own γ (◯ {[i := (x, y)]}).
Proof.
  rewrite -own_op. iIntros "H". iApply (own_proper with "H").
  apply auth_frag_proper => //=.
  intros j. rewrite lookup_op. destruct (decide (i = j)); last first.
  { rewrite ?lookup_singleton_ne //=. }
  subst. rewrite ?lookup_singleton /=.
  rewrite -Some_op -pair_op agree_idemp /inv_mut_unfold left_id //=.
Qed.

Lemma ownI_mut_agree {n m} lvl i q1 q2 (Qs_mut1: vec _ n) (Qs_mut2: vec _ m):
  ownI_mut lvl i q1 Qs_mut1 -∗
  ownI_mut lvl i q2 Qs_mut2 -∗
  ⌜ n = m ⌝ ∗ (∀ j, ▷ (vec_to_list Qs_mut1 !! j ≡  vec_to_list Qs_mut2 !! j)).
Proof.
  rewrite /ownI_mut.
  iDestruct 1 as (l1 γs1) "(#Hidx1&Hown1)".
  iDestruct 1 as (l2 γs2) "(#Hidx2&Hown2)".
  iDestruct (fmlist_idx_agree_1 with "Hidx1 Hidx2") as %->.
  iCombine "Hown1 Hown2" as "Hown".
  iDestruct (own_valid with "Hown") as "Hval".
  rewrite auth_frag_validI gmap_validI.
  iSpecialize ("Hval" $! i).
  rewrite lookup_singleton /= option_validI /= prod_validI /=.
  iDestruct "Hval" as "(_&Hval)".
  rewrite option_validI /= prod_validI /=.
  iDestruct "Hval" as "(_&Hagree)".
  rewrite agree_validI agree_equivI.
  (* XXX: this pattern is repeated a few times in other proofs. prove a lemma *)
  iDestruct (list_equivI_length with "Hagree") as %Hlen.
  iSplitL "".
  { iPureIntro. rewrite ?fmap_length ?vec_to_list_length //= in Hlen. }
  rewrite ?list_equivI_1. iIntros (j). iSpecialize ("Hagree" $! j).
  rewrite ?list_lookup_fmap ?vec_to_list_to_vec.
  rewrite option_equivI.
  destruct (vec_to_list Qs_mut1 !! j) as [Q0|] eqn:HeqQ;
  destruct (vec_to_list Qs_mut2 !! j) as [P0|] eqn:HeqP;
  rewrite ?HeqQ ?HeqP //=.
  rewrite //= ?later_equivI //=. iNext. by iRewrite "Hagree".
Qed.

Lemma ownI_mut_combine {n m} lvl i q1 q2 (Qs_mut1: vec _ n) (Qs_mut2: vec _ m):
  ownI_mut lvl i q1 Qs_mut1 -∗
  ownI_mut lvl i q2 Qs_mut2 -∗
  ownI_mut lvl i (q1 + q2)%Qp Qs_mut1.
Proof.
  rewrite /ownI_mut.
  iDestruct 1 as (l1 γs1) "(#Hidx1&Hown1)".
  iDestruct 1 as (l2 γs2) "(#Hidx2&Hown2)".
  iDestruct (fmlist_idx_agree_1 with "Hidx1 Hidx2") as %->.
  iExists l1, _.  iFrame "Hidx1".
  iCombine "Hown1 Hown2" as "Hown".
  iDestruct (own_valid with "Hown") as "#Hval".
  rewrite auth_frag_validI gmap_validI.
  iSpecialize ("Hval" $! i).
  rewrite lookup_singleton /= option_validI /= prod_validI /=.
  iDestruct "Hval" as "(Hval1&Hval2)".
  rewrite agree_op_invI. iRewrite -"Hval1" in "Hown".
  rewrite agree_idemp.
  rewrite /= option_validI /= prod_validI /=.
  iDestruct "Hval2" as "(Hval2a&Hval2b)".
  rewrite agree_op_invI. iRewrite -"Hval2b" in "Hown".
  rewrite agree_idemp.
  eauto.
Qed.

Lemma ownI_close_modify {n m m'} lvl i sch (Ps : vec _ n) (Ps_mut: vec _ m) (Qs_mut: vec _ m') :
  wsat (S lvl) ∗
  ownI lvl i sch Ps ∗
  ownI_mut lvl i 1%Qp Qs_mut ∗
  bi_schema_interp lvl (bi_later <$> (vec_to_list Ps)) (bi_later <$> (vec_to_list Ps_mut)) sch ∗
  ownD {[i]} ⊢
  |==> wsat (S lvl) ∗ ownE {[i]} ∗ ownI_mut lvl i (1/2)%Qp Ps_mut.
Proof.
  rewrite /ownI wsat_unfold.
  iIntros "((Hw&$) & Hi & Hi_mut & HP & HiD)". iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct "Hw" as (γs1) "(#Hidx1&Hw)".
  iDestruct "Hi" as (γs2) "(#Hidx2&Hi)".
  iEval (rewrite /ownI_mut) in "Hi_mut".
  iDestruct "Hi_mut" as (? γs2_mut) "(#Hidx3&Hi_mut)".
  iDestruct (fmlist_idx_agree_1 with "Hidx1 Hidx2") as %->.
  iDestruct (fmlist_idx_agree_1 with "Hidx3 Hidx2") as %->.
  iDestruct (invariant_lookup_strong with "[$Hw Hi Hi_mut]")
    as (Qs' Qs_mut' HIlookup Hlen Hlen_mut) "(#HPQ&#HPQ_mut)".
  { iCombine "Hi Hi_mut" as "Hcombine".
    iDestruct (own_valid with "Hcombine") as "#Hval".
    rewrite auth_frag_validI gmap_validI_singleton prod_validI /=.
    rewrite agree_validI. iDestruct "Hval" as "(Hval_agree&_)".
    iRewrite -"Hval_agree" in "Hcombine".
    rewrite agree_idemp left_id. eauto.
  }
  iDestruct (big_sepM_insert_acc _ _ i with "HI") as "[[[HQ [HQmut ?]]|$] HI]"; eauto.
  { iDestruct (ownD_singleton_twice with "[$]") as %[]. }
  iMod (ownI_mut_update _ _ _ _ _ Ps_mut with "[$] [$]") as (Ps' sch' ? HIlookup') "(Hw&Hi_mut)".
  iModIntro. iDestruct (ownI_full_split_frac with "Hi_mut") as "(Hi_mut1&Hi_mut2)".
  iSplitR "Hi_mut2"; last first.
  { iExists _, _. by iFrame. }
  iExists _.
  iSplitL "Hw".
  { by eauto with iFrame. }
  iApply "HI". iLeft.
  iFrame "HiD". iClear "Hi".
  iSplitL "HP".
  { simpl. rewrite HIlookup in HIlookup'. inversion HIlookup'; subst.
    iApply (bi_schema_interp_ctx_later with "HPQ []"); last eauto.
    { iIntros; iNext. trivial. }
  }
  iExists _, _. iFrame "Hidx2" => /=. rewrite /inv_mut_unfold vec_to_list_to_vec //=.
Qed.

Lemma ownI_alloc {n m} φ sch lvl (Ps: vec _ n) (Ps_mut: vec _ m):
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat (S lvl) ∗
  bi_schema_interp lvl (bi_later <$> (vec_to_list Ps)) (bi_later <$> (vec_to_list Ps_mut)) sch ==∗
  ∃ i, ⌜φ i⌝ ∗ wsat (S lvl) ∗ ownI lvl i sch Ps ∗ ownI_mut lvl i (1/2)%Qp Ps_mut.
Proof.
  rewrite wsat_unfold.
  iIntros (Hfresh) "[(Hw&$) HP]".
  iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct "Hw" as (γs) "(#Hidx1&Hw)".
  iMod (own_unit (gset_disjUR positive) disabled_name) as "HE".
  iMod (own_updateP with "[$]") as "HE".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom _ I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HE" as (X) "[Hi HE]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply auth_update_alloc,
     (alloc_singleton_local_update _ i (invariant_unfold sch Ps, inv_mut_unfold 1%Qp Ps_mut)); last done.
    by rewrite /= lookup_fmap HIi. }
  iDestruct (ownI_full_split_comp with "HiP") as "(Hi_pers&Hi_mut)".
  iDestruct (ownI_full_split_frac with "Hi_mut") as "(Hi_mut1&Hi_mut2)".
  iModIntro; iExists i;  iSplit; [done|]. iSplitR "Hi_pers Hi_mut1"; last first.
  { rewrite /ownI/ownI_mut. iSplitL "Hi_pers".
    { iExists _; iFrame "Hidx1"; eauto. }
    { iExists _, _; iFrame "Hidx1"; eauto. }
  }
  iExists (<[i:=((vec_to_list Ps, sch), vec_to_list Ps_mut)]>I); iSplitL "Hw".
  { iExists γs. iFrame "Hidx1".
    rewrite ?fmap_insert ?insert_singleton_op ?lookup_fmap ?HIi //=
            /invariant_unfold/inv_mut_unfold ?vec_to_list_to_vec //=. }
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI". iLeft. rewrite /ownD. iFrame.
  iExists _, _. iFrame "Hidx1". rewrite /inv_mut_unfold ?vec_to_list_to_vec //=.
Qed.

Lemma ownI_alloc_nomut {n} φ sch lvl (Ps: vec _ n):
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat (S lvl) ∗
  bi_schema_interp lvl (bi_later <$> (vec_to_list Ps)) [] sch ==∗
  ∃ i, ⌜φ i⌝ ∗ wsat (S lvl) ∗ ownI lvl i sch Ps.
Proof.
  iIntros. iMod (ownI_alloc _ _ _ _ (list_to_vec []) with "[$]") as (?) "(?&?&?&?)"; auto.
Qed.

Lemma ownI_alloc_open {n m} lvl φ sch (Ps: vec _ n) (Ps_mut : vec _ m) :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat (S lvl) ==∗
  ∃ i, ⌜φ i⌝ ∗
       (ownE {[i]} -∗ wsat (S lvl)) ∗
       ownI lvl i sch Ps ∗
       ownI_mut lvl i (1/2)%Qp Ps_mut ∗
       ownD {[i]}.
Proof.
  iIntros (Hfresh) "Hw". rewrite wsat_unfold.
  iDestruct "Hw" as "(Hw&$)".
  iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct "Hw" as (γs) "(#Hidx1&Hw)".
  iMod (own_unit (gset_disjUR positive) disabled_name) as "HD".
  iMod (own_updateP with "[$]") as "HD".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom _ I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HD" as (X) "[Hi HD]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply auth_update_alloc,
     (alloc_singleton_local_update _ i (invariant_unfold sch Ps, inv_mut_unfold 1%Qp Ps_mut)); last done.
    by rewrite /= lookup_fmap HIi. }
  iDestruct (ownI_full_split_comp with "HiP") as "(Hi_pers&Hi_mut)".
  iDestruct (ownI_full_split_frac with "Hi_mut") as "(Hi_mut1&Hi_mut2)".
  iModIntro; iExists i;  iSplit; [done|]. iSplitR "Hi_pers Hi_mut1 HD"; last first.
  { rewrite /ownI/ownI_mut. iSplitL "Hi_pers".
    { iExists _; iFrame "Hidx1"; eauto. }
    iSplitL "Hi_mut1".
    { iExists _, _; iFrame "Hidx1"; eauto. }
    rewrite /ownD; eauto.
  }
  iIntros "HE".
  iExists (<[i:=((vec_to_list Ps, sch), vec_to_list Ps_mut)]>I); iSplitL "Hw".
  { iExists γs. iFrame "Hidx1".
    rewrite ?fmap_insert ?insert_singleton_op ?lookup_fmap ?HIi //=
            /invariant_unfold/inv_mut_unfold ?vec_to_list_to_vec //=. }
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI". by iRight.
Qed.

Lemma wsat_alloc_new_level l:
  wsat (length l) -∗ fmlist (inv_list_name) 1 l ==∗
  ∃ (γ: invariant_level_names), fmlist inv_list_name 1 (l ++ [γ]) ∗ wsat (S (length l)).
Proof.
  iIntros "Hw Hlist".
  rewrite ?wsat_unfold. iFrame.
  iMod (own_alloc (● (∅ : gmap positive _))) as (γ) "HI";
    first by rewrite auth_auth_valid.
  iExists {| invariant_name := γ |}.
  iMod (fmlist_update (l ++ [{| invariant_name := γ|}]) with "[$]") as "($&Hidx)".
  { eexists; eauto. }
  iModIntro.
  iExists ∅. rewrite fmap_empty big_sepM_empty right_id.
  iExists {| invariant_name := γ |}; iFrame.
  iApply fmlist_lb_to_idx; auto.
  rewrite lookup_app_r //=. replace (length l - length l) with O by lia; auto.
Qed.

Lemma wsat_alloc_new_levels l n:
  wsat (length l) -∗ fmlist (inv_list_name) 1 l ==∗
  ∃ l', ⌜ length l' = n ⌝ ∗ fmlist inv_list_name 1 (l ++ l') ∗ wsat (length (l ++ l')).
Proof.
  iIntros "Hw Hlist".
  iInduction n as [| n] "IH".
  - iModIntro; iExists []. rewrite ?right_id. by iFrame.
  - iMod ("IH" with "[$] [$]") as (l' Hlen) "(Hw&Hlist)".
    iMod (wsat_alloc_new_level with "[$] [$]") as (γ) "(Hlist&Hw)".
    iExists (l' ++ [γ]). rewrite ?app_length //=.
    rewrite app_assoc. iFrame.
    replace (length l + (length l' + 1)) with (S (length l + length l')) by lia; iFrame.
    iPureIntro. lia.
Qed.

Definition wsat_all := (∃ l, wsat (length l) ∗ fmlist (inv_list_name) 1 l)%I.

Lemma wsat_all_acc n:
  wsat_all ==∗ wsat n ∗ (wsat n -∗ wsat_all).
Proof.
  iDestruct 1 as (l) "(Hw&Hlist)".
  iMod (wsat_alloc_new_levels l (n - length l) with "[$] [$]") as (l' Hlen) "(Hlist&Hw)".
  iDestruct (wsat_le_acc n with "[$]") as "($&Hclo)"; first auto.
  { rewrite app_length. lia. }
  iIntros "!> Hw". iExists _. iFrame. by iApply "Hclo".
Qed.

End wsat.

(* Allocation of an initial world *)
Lemma wsat_alloc'_strong `{HIPRE: !invGpreS Σ} :
  ⊢ |==> ∃ (_ : invGS Σ) (HEQ: inv_inG = HIPRE), wsat_all ∗ ownE ⊤.
Proof.
  iIntros.
  iMod (fmlist_alloc []) as (γI) "HI".
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (GSet ∅)) as (γD) "HD"; first done.
  set (iG := (WsatG _ _ γI γE γD)).
  unshelve (iExists iG, _); eauto.
  rewrite /ownE. iFrame. iClear "HD".
  replace γI with (inv_list_name) by eauto.
  iExists [] => //=. iFrame. rewrite wsat_unfold //.
Qed.

Lemma wsat_alloc' `{!invGpreS Σ} :
  ⊢ |==> ∃ (_ : invGS Σ), wsat_all ∗ ownE ⊤.
Proof.
  iIntros.
  iMod (fmlist_alloc []) as (γI) "HI".
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (GSet ∅)) as (γD) "HD"; first done.
  set (iG := (WsatG _ _ γI γE γD)).
  iExists iG.
  rewrite /ownE. iFrame. iClear "HD".
  replace γI with (inv_list_name) by eauto.
  iExists [] => //=. iFrame. rewrite wsat_unfold //.
Qed.

Lemma wsat_alloc `{!invGpreS Σ} n : ⊢ |==> ∃ _ : invGS Σ, wsat n ∗ ownE ⊤.
Proof.
  iIntros.
  iMod (wsat_alloc') as (?) "(Hall&Hown)".
  iExists _. iMod (wsat_all_acc n with "[$]") as "(?&?)".
  by iFrame.
Qed.

Section schema_test_bupd.
Context `{!invGS Σ}.
Implicit Types P : iProp Σ.

Definition ownI_bupd lvl i P := ownI lvl i (bi_sch_bupd (bi_sch_var_fixed O)) (list_to_vec [P]).

Lemma ownI_bupd_alloc lvl φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat (S lvl) ∗ (|==> ▷ P) ==∗ ∃ i, ⌜φ i⌝ ∗ wsat (S lvl) ∗ ownI_bupd lvl i P.
Proof.
  iIntros (?) "HwP".
  iApply (ownI_alloc_nomut); auto.
  rewrite ?bi_schema_interp_unfold //=.
Qed.

Lemma ownI_bupd_open lvl i P :
  wsat (S lvl) ∗ ownI_bupd lvl i P ∗ ownE {[i]} ⊢ wsat (S lvl) ∗ |==> ▷ P ∗ ownD {[i]}.
Proof.
 iIntros "Hw".
 iDestruct (ownI_open with "Hw") as "($&HP&$)".
 iDestruct "HP" as (??) "(HP&_)".
 rewrite ?bi_schema_interp_unfold //=.
Qed.

End schema_test_bupd.

Section schema_test_mut.
Context `{!invGS Σ}.
Implicit Types P Q : iProp Σ.

Definition bi_sch_bupd_factory (Q P: bi_schema) : bi_schema :=
  bi_sch_sep Q (bi_sch_persistently (bi_sch_wand Q (bi_sch_bupd (bi_sch_sep Q P)))).

Definition ownI_bupd_factory lvl i P :=
  ownI lvl i (bi_sch_bupd_factory (bi_sch_var_mut O) (bi_sch_var_fixed O)) (list_to_vec [P]).

Definition ownI_full_bupd_factory lvl i q Q P :=
  (∃ n (Qs: vec _ n), ownI lvl i (bi_sch_bupd_factory (bi_sch_var_mut O) (bi_sch_var_fixed O)) (list_to_vec [P]) ∗
   ownI_mut lvl i q Qs ∗ ⌜ default True%I (vec_to_list Qs !! 0) = Q ⌝)%I.

Lemma ownI_bupd_factory_alloc lvl φ Q P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat (S lvl) ∗ (▷ Q ∗ □ (▷ Q ==∗ ▷ Q ∗ ▷ P))
       ==∗ ∃ i, ⌜φ i⌝ ∗ wsat (S lvl) ∗ ownI_full_bupd_factory lvl i (1/2)%Qp Q P.
Proof.
  iIntros (?) "(Hw&(HQ&#Hfactory))". iMod (ownI_alloc with "[$Hw HQ]") as (i) "(?&?&?&?)"; eauto; last first.
  { iModIntro. iExists i. iFrame. iExists 1, (list_to_vec [Q]). iFrame. rewrite //=. }
  repeat (rewrite ?bi_schema_interp_unfold //=).
  iFrame. eauto.
Qed.

Lemma ownI_full_bupd_factory_open lvl i Q P:
  wsat (S lvl) ∗ ownI_full_bupd_factory lvl i (1/2)%Qp Q P ∗ ownE {[i]} ⊢
  wsat (S lvl) ∗ (▷ Q ∗ □ (▷ Q ==∗ ▷ Q ∗ ▷ P)) ∗ ownI_full_bupd_factory lvl i 1%Qp Q P ∗ ownD {[i]}.
Proof.
  iIntros "(Hw&Hfull&HE)".
  iDestruct "Hfull" as (? Qs) "(#HI&HI_mut&Hp)".
  iDestruct "Hp" as %Hp.
  iPoseProof (ownI_open with "[$Hw $HI $HE]") as "($&H&$)".
  iDestruct "H" as (??) "(Hinterp&HI_mut2)".
  iDestruct (ownI_mut_agree with "HI_mut HI_mut2") as (Hlen) "#Hequiv".
  iDestruct (bi_schema_interp_ctx_later with "[] Hequiv Hinterp") as "Hinterp".
  { iIntros. iNext. eauto. }
  repeat (rewrite ?bi_schema_interp_unfold //=).
  iSplitL "Hinterp".
  { rewrite ?list_lookup_fmap.
    destruct (vec_to_list Qs !! 0) as [?|] eqn:Heq.
    * rewrite ?Heq => //=. move: Hp => //= ->.
      { iDestruct "Hinterp" as "($&#$)". }
    * move: Hp. rewrite Heq => //= <-.
      { iDestruct "Hinterp" as "(?&#Hwand)". iSplitL ""; first eauto.
        iModIntro. iIntros. iMod ("Hwand" with "[//]") as "(?&$)"; eauto. }
   }
  iExists _, _. iFrame "#".
  iDestruct (ownI_mut_combine with "HI_mut [$]") as "H". rewrite Qp_div_2 //=. iFrame. eauto.
Qed.

Lemma ownI_bupd_factory_open lvl i P:
  wsat (S lvl) ∗ ownI_bupd_factory lvl i P ∗ ownE {[i]} ⊢
  wsat (S lvl) ∗ ∃ Q, (▷ Q ∗ □ (▷ Q ==∗ ▷ Q ∗ ▷ P)) ∗ ownI_full_bupd_factory lvl i (1/2)%Qp Q P ∗ ownD {[i]}.
Proof.
  iIntros "(Hw&#HI0&HE)".
  iPoseProof (ownI_open with "[$Hw $HI0 $HE]") as "($&H&$)".
  iDestruct "H" as (? Qs_mut) "(Hinterp&HI_mut2)".
  iExists (default True%I (vec_to_list Qs_mut !! 0)).
  repeat (rewrite ?bi_schema_interp_unfold //=).
  rewrite ?list_lookup_fmap.
  destruct (vec_to_list Qs_mut !! 0) as [?|] eqn:Heq; rewrite Heq //=.
  - iSplitL "Hinterp".
    { iDestruct "Hinterp" as "($&#$)". }
    iFrame "#". iExists _, Qs_mut. rewrite Heq //=. by iFrame.
  - iSplitL "Hinterp".
    { iDestruct "Hinterp" as "(?&#Hwand)". iSplitL ""; first eauto.
      iModIntro. iIntros. iMod ("Hwand" with "[//]") as "(?&$)"; eauto. }
    iFrame "#". iExists _, Qs_mut. rewrite Heq //=. by iFrame.
Qed.

Lemma ownI_bupd_factory_close lvl i Q P:
  wsat (S lvl) ∗ (▷ Q ∗ □ (▷ Q ==∗ ▷ Q ∗ ▷ P)) ∗ ownI_full_bupd_factory lvl i (1/2)%Qp Q P ∗ ownD {[i]} ⊢
  wsat (S lvl) ∗ ownE {[i]}.
Proof.
  iIntros "(Hw&Hinterp&HI0&HD)".
  iDestruct ("HI0") as (? Qs_mut) "(?&?&Hp)".
  iDestruct "Hp" as %Hp.
  iApply (ownI_close).
  iFrame.
  repeat (rewrite ?bi_schema_interp_unfold //=).
  rewrite ?list_lookup_fmap.
  destruct (vec_to_list Qs_mut !! 0) as [?|] eqn:Heq; rewrite Heq //=.
  - move: Hp => //= ->.
    { iDestruct "Hinterp" as "($&#$)". }
  - move: Hp => //= <-.
    { iDestruct "Hinterp" as "(?&#Hwand)". iSplitL ""; first eauto.
      iModIntro. iIntros. iMod ("Hwand" with "[//]") as "(?&$)"; eauto. }
Qed.

Lemma ownI_bupd_factory_close_modify lvl i Q Q0 P:
  wsat (S lvl) ∗ (▷ Q ∗ □ (▷ Q ==∗ ▷ Q ∗ ▷ P)) ∗ ownI_full_bupd_factory lvl i 1%Qp Q0 P ∗ ownD {[i]} ⊢
  |==> wsat (S lvl) ∗ ownE {[i]} ∗ ownI_full_bupd_factory lvl i (1/2)%Qp Q P.
Proof.
  iIntros "(Hw&Hinterp&HI0&HD)".
  iDestruct ("HI0") as (? Qs_mut) "(#Hi&?&Hp)".
  iDestruct "Hp" as %Hp.
  iMod (ownI_close_modify _ _ _ _ (list_to_vec [Q]) Qs_mut  with "[-]") as "($&$&?)".
  {
    iFrame. iFrame "#".
    repeat (rewrite ?bi_schema_interp_unfold //=).
    iDestruct "Hinterp" as "($&#$)".
  }
  iExists _, _. iFrame "# ∗" => //=.
Qed.

End schema_test_mut.
