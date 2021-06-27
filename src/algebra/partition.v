From stdpp Require Export namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap frac agree gset.
From Perennial.base_logic.lib Require Export own.
From Perennial.algebra Require Import gen_heap_names.
Set Default Proof Using "Type".
Import uPred.

Class partitionG (L V: Type) (Σ: gFunctors) `{Countable L, Infinite L, Countable V, Infinite V} := {
  partition_heap_inG :> gen_heapGS L (gset V) Σ;
}.

Class partition_preG (L V: Type) Σ `{Countable L, Infinite L, Countable V, Infinite V} := {
  partition_heap_preG :> gen_heapGpreS L (gset V) Σ;
}.


Definition partitionΣ (L V: Type) `{Countable L, Infinite L, Countable V, Infinite V} : gFunctors :=
    #[gen_heapΣ L (gset V)].

Instance subG_partitionG L V {Σ} `{Countable L, Infinite L, Countable V, Infinite V}:
  subG (partitionΣ L V) Σ → partition_preG L V Σ.
Proof. solve_inG. Qed.

Local Notation "l ↦{ q } v" := (mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Local Notation "l ↦ v" := (mapsto l 1 v) (at level 20) : bi_scope.

Local Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Local Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

Section definitions.
Context `{Countable L, Infinite L, Countable V, Infinite V, hG : !partitionG L V Σ}.

Implicit Types l : L.
Implicit Types s : gset V.

Definition disjoint_images (σ: gmap L (gset V)) : Prop :=
  ∀ i1 i2 s1 s2, i1 ≠ i2 → σ !! i1 = Some s1 → σ !! i2 = Some s2 →
                 s1 ## s2.

Definition partition_ctx (σ: gmap L (gset V)) : iProp Σ :=
  (⌜ disjoint_images σ ⌝ ∗ gen_heap_ctx σ).

Definition union_partition (σ: gmap L (gset V)) : gset V :=
  map_fold (λ _ s1 s2, s1 ∪ s2) ∅ σ.

Lemma union_partition_elem_of_1 σ (v: V):
  v ∈ union_partition σ → ∃ i s, σ !! i = Some s ∧ v ∈ s.
Proof.
  revert v.
  eapply (map_fold_ind (λ b σ, ∀ v, v ∈ b → ∃ i s, σ !! i = Some s ∧ v ∈ s) _ ∅).
  - set_solver.
  - intros i s1 m s2 Hlookup HP v Hin.
    apply elem_of_union in Hin as [Hs1|Hs2].
    * exists i, s1. rewrite lookup_insert; auto.
    * edestruct (HP) as (i'&s'&?&?); eauto.
      exists i', s'. rewrite lookup_insert_ne //=. congruence.
Qed.

Lemma union_partition_elem_of_2 σ (v: V) i s:
  σ !! i = Some s → v ∈ s → v ∈ union_partition σ.
Proof.
  revert v i s.
  eapply (map_fold_ind (λ b σ, ∀ v i s, σ !! i = Some s → v ∈ s → v ∈ b) _ ∅).
  - set_solver.
  - intros i s1 m s2 Hlookup HP v i' s Hlookup2 Hin.
    destruct (decide (i = i')).
    * subst. rewrite lookup_insert in Hlookup2. apply elem_of_union_l.
      inversion Hlookup2; subst; eauto.
    * rewrite lookup_insert_ne in Hlookup2 * => //=.
      apply elem_of_union_r. eapply HP; eauto.
Qed.

Lemma union_partition_subset σ i s:
  σ !! i = Some s → s ⊆ union_partition σ.
Proof. set_unfold. intros. by eapply union_partition_elem_of_2. Qed.

Definition fresh_partition_value (σ: gmap L (gset V)) : V :=
  fresh (union_partition σ).

Lemma not_elem_of_union_partition σ x :
  x ∉ union_partition σ → ∀ i s, σ !! i = Some s → x ∉ s.
Proof.
  intros Hin1 i s Hlookup.
  intros Hin. eapply union_partition_elem_of_2 in Hlookup; eauto.
Qed.

Lemma fresh_partition_value_spec σ :
  ∀ i s, σ !! i = Some s → fresh_partition_value σ ∉ s.
Proof.
  rewrite /fresh_partition_value.
  apply not_elem_of_union_partition, is_fresh.
Qed.

Lemma partition_alloc σ:
  partition_ctx σ ==∗ ∃ l v (Hfresh1: σ !! l = None) (Hfresh2: v ∉ union_partition σ),
        partition_ctx (<[l := {[v]}]>σ) ∗ l ↦ {[v]} ∗ meta_token l ⊤.
Proof.
  iIntros "(Hdisj&Hctx)". iDestruct "Hdisj" as %Hdisj.
  iMod (gen_heap_alloc σ (fresh (dom (gset L) σ)) ({[fresh_partition_value σ]}) with "Hctx")
       as "(Hctx&Hl&Hmeta)".
  { rewrite -(not_elem_of_dom (D := gset L)). apply is_fresh. }
  iModIntro. unshelve (iExists _, _, _, _; iFrame).
  { eapply (not_elem_of_dom (D := gset L)). apply is_fresh. }
  { rewrite /fresh_partition_value. eapply is_fresh. }
  iPureIntro.
  intros i j s1 s2 Hneq.
  destruct (decide (i = fresh (dom (gset L) σ))) as [He1|Hne1].
  { subst. rewrite lookup_insert lookup_insert_ne //.
    inversion 1; subst. intros Hlookup.
    specialize (fresh_partition_value_spec σ j s2). set_solver. }
  destruct (decide (j = fresh (dom (gset L) σ))) as [He2|Hne2].
  { subst. rewrite lookup_insert lookup_insert_ne //.
    inversion 1; subst. intros Hlookup.
    specialize (fresh_partition_value_spec σ i s1). set_solver. }
  rewrite ?lookup_insert_ne //. by eapply Hdisj.
Qed.

Lemma partition_valid_disj σ (l1 l2: L) (s1 s2: gset V):
  partition_ctx σ -∗ l1 ↦ s1 -∗ l2 ↦ s2 -∗ ⌜ l1 ≠ l2 ∧ s1 ## s2 ⌝.
Proof.
  iDestruct 1 as (Hdisj) "Hctx". iIntros "Hl1 Hl2".
  iDestruct (gen_heap_valid with "Hctx Hl1") as %Hin1.
  iDestruct (gen_heap_valid with "Hctx Hl2") as %Hin2.
  iAssert (⌜l1 ≠ l2⌝)%I with "[-]" as %Hneq.
  { iIntros (?). subst. iDestruct (mapsto_valid_2 with "[$] [$]") as %Hval.
    rewrite frac_valid in Hval * => Hlt. by apply Qp_not_plus_q_ge_1 in Hlt.
  }
  iPureIntro. split; auto. eapply Hdisj; eauto.
Qed.

Lemma union_partition_move σ (l1 l2: L) (s1 s1' s2: gset V):
  l1 ≠ l2 →
  s1 ## s1' →
  σ !! l1 = Some (s1 ∪ s1') →
  σ !! l2 = Some s2 →
  union_partition σ = union_partition (<[l1:=s1]> (<[l2:=s2 ∪ s1']> σ)).
Proof.
  intros Hneq Hdisj Hl1 Hl2.
  assert (<[l1:=s1]> (<[l2:=s2 ∪ s1']> σ) =
          <[l1:=s1]> (delete l1 (<[l2:=s2 ∪ s1']> (delete l2 σ)))) as Heq.
  { by rewrite ?insert_delete_insert. }
  rewrite Heq.

  assert (σ = <[l1:=s1 ∪ s1']> (delete l1 (<[l2:=s2]> (delete l2 σ)))) as Heq'.
  { rewrite ?insert_delete_insert ?insert_id //. }
  rewrite {1}Heq'.

  rewrite /union_partition ?map_fold_insert ?lookup_delete //; try set_solver+.
  rewrite ?delete_insert_ne //.
  assert (delete l1 (delete l2 σ) !! l2 = None).
  { rewrite lookup_delete_ne // lookup_delete //. }
  rewrite ?map_fold_insert //; set_solver+.
Qed.

Lemma partition_move σ (l1 l2: L) (s1 s1' s2: gset V):
  s1 ## s1' →
  partition_ctx σ -∗ l1 ↦ (s1 ∪ s1') -∗ l2 ↦ s2 ==∗
  partition_ctx (<[l1 := s1]>(<[l2 := s2 ∪ s1']>σ)) ∗ l1 ↦ s1 ∗ l2 ↦ (s2 ∪ s1').
Proof.
  iIntros (Hdisjs1) "Hpart Hl1 Hl2".
  iDestruct (partition_valid_disj with "Hpart Hl1 Hl2") as %Hdisj_s1s2.
  iDestruct "Hpart" as (Hdisj) "Hctx".
  iDestruct (gen_heap_valid with "Hctx Hl1") as %Hin1.
  iDestruct (gen_heap_valid with "Hctx Hl2") as %Hin2.
  iMod (gen_heap_update σ l2 _ (s2 ∪ s1') with "[$] [$]") as "(Hctx&Hl2)".
  iMod (gen_heap_update _ l1 _ (s1) with "[$] [$]") as "(Hctx&Hl1)".
  iModIntro. iFrame. iPureIntro.
  intros i j si sj Hneq.
  destruct (decide (i = l1)) as [He1|Hne1].
  { subst.
    rewrite lookup_insert. inversion 1; subst.
    rewrite lookup_insert_ne //.
    destruct (decide (j = l2)) as [He2|Hne2].
    {
      subst. rewrite lookup_insert. inversion 1; subst.
      set_solver.
    }
    rewrite lookup_insert_ne //; intros; eauto.
    cut (si ∪ s1' ## sj); first by set_solver.
    eapply Hdisj; [ | apply Hin1 | eauto ]; eauto.
  }
  rewrite lookup_insert_ne //.
  destruct (decide (i = l2)) as [He2|Hne2].
  {
    subst.
    rewrite lookup_insert.
    destruct (decide (j = l1)) as [He2|Hne2].
    {
      subst. rewrite lookup_insert. inversion 1; subst.
      set_solver.
    }
    inversion 1; subst.
    rewrite ?lookup_insert_ne //; intros; eauto.
    cut (s1 ∪ s1' ## sj ∧ s2 ## sj); first by set_solver.
    split.
    * eapply Hdisj; [ | apply Hin1 | eauto ]; eauto.
    * eapply Hdisj; [ | apply Hin2 | eauto ]; eauto.
  }
  rewrite lookup_insert_ne // => ?.
  destruct (decide (j = l1)) as [He3|Hne3].
  {
    subst. rewrite lookup_insert. inversion 1; subst.
    cut (sj ∪ s1' ## si); first by set_solver.
    eapply Hdisj; [ | apply Hin1 | eauto ]; eauto.
  }
  rewrite lookup_insert_ne //.
  destruct (decide (j = l2)) as [He4|Hne4].
  {
    subst. rewrite lookup_insert. inversion 1; subst.
    cut (s1 ∪ s1' ## si ∧ s2 ## si); first by set_solver.
    split.
    * eapply Hdisj; [ | apply Hin1 | eauto ]; eauto.
    * eapply Hdisj; [ | apply Hin2 | eauto ]; eauto.
  }
  rewrite lookup_insert_ne // => Hin4.
  eapply Hdisj; [ | | apply Hin4 ]; eauto.
Qed.

Lemma partition_move_1 σ (l1 l2: L) (v: V) (s: gset V):
  partition_ctx σ -∗ l1 ↦ {[v]} -∗ l2 ↦ s ==∗
  partition_ctx (<[l1 := ∅]>(<[l2 := s ∪ {[v]}]>σ)) ∗ l1 ↦ ∅ ∗ l2 ↦ (s ∪ {[v]}).
Proof.
  replace {[v]} with (∅ ∪ {[v]} : gset V) at 1 by set_solver.
  iApply partition_move; set_solver.
Qed.

Lemma partition_join σ (l1 l2: L) (s1 s2: gset V):
  partition_ctx σ -∗ l1 ↦ s1 -∗ l2 ↦ s2 ==∗
  partition_ctx (<[l1 := ∅]>(<[l2 := s2 ∪ s1]>σ)) ∗ l1 ↦ ∅ ∗ l2 ↦ (s2 ∪ s1).
Proof.
  replace s1 with (∅ ∪ s1) at 1 by set_solver.
  iApply partition_move; set_solver.
Qed.

End definitions.

Lemma partition_init `{hP: partition_preG L V Σ}:
  ⊢ |==> ∃ names : gen_heap_names,
        let _ := {| partition_heap_inG :=
                      gen_heapG_update_pre (@partition_heap_preG _ _ _ _ _ _ _ _ _ hP) names |} in
        partition_ctx (∅: gmap L (gset V)).
Proof.
  iMod (gen_heap_name_init ∅) as (names) "H".
  iModIntro. iExists names. iFrame. rewrite //=.
Qed.
