From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap frac agree.
From iris.base_logic.lib Require Import own gen_heap.
Set Default Proof Using "Type".
Import uPred.

(** This is from iris/theories/base_logic/lib/gen_heap.v with tokens removed
    so that we can support deletion. *)

(** The CMRA we need. *)
Class gen_heapG (L V : Type) (Σ : gFunctors) `{Countable L} := GenHeapG {
  gen_heap_inG :> inG Σ (authR (gen_heapUR L V));
  gen_heap_name : gname
}.
Arguments gen_heap_name {_ _ _ _ _} _ : assert.

Class gen_heapPreG (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_heap_preG_inG :> inG Σ (authR (gen_heapUR L V))
}.

Definition gen_heapΣ (L V : Type) `{Countable L} : gFunctors := #[
  GFunctor (authR (gen_heapUR L V))
].

Instance xsubG_gen_heapPreG {Σ L V} `{Countable L} :
  subG (gen_heapΣ L V) Σ → gen_heapPreG L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{Countable L, hG : !gen_heapG L V Σ}.

  Definition gen_heap_ctx (σ : gmap L V) : iProp Σ := (
    own (gen_heap_name hG) (● (to_gen_heap σ)))%I.

  Definition mapsto_def (l : L) (q : Qp) (v: V) : iProp Σ :=
    own (gen_heap_name hG) (◯ {[ l := (q, to_agree (v : leibnizO V)) ]}).
  Definition mapsto_aux : seal (@mapsto_def). by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
End definitions.

Local Notation "l ↦{ q } v" := (mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Local Notation "l ↦ v" := (mapsto l 1 v) (at level 20) : bi_scope.

Local Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Local Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

Section to_gen_heap.
  Context (L V : Type) `{Countable L}.
  Implicit Types σ : gmap L V.

  Lemma to_gen_heap_delete l σ :
    to_gen_heap (delete l σ) = delete l (to_gen_heap σ).
  Proof. by rewrite /to_gen_heap fmap_delete. Qed.
End to_gen_heap.

Lemma gen_heap_init `{Countable L, !gen_heapPreG L V Σ} σ :
  ⊢ |==> ∃ _ : gen_heapG L V Σ, gen_heap_ctx σ.
Proof.
  iMod (own_alloc (● to_gen_heap σ)) as (γh) "Hh".
  { rewrite auth_auth_valid. exact: to_gen_heap_valid. }
  iModIntro. iExists (GenHeapG L V Σ _ _ _ γh). done.
Qed.

Section gen_heap.
  Context {L V} `{Countable L, !gen_heapG L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L V.
  Implicit Types h g : gen_heapUR L V.
  Implicit Types l : L.
  Implicit Types v : V.

  (** General properties of mapsto *)
  Global Instance mapsto_timeless l q v : Timeless (l ↦{q} v).
  Proof. rewrite mapsto_eq /mapsto_def. apply _. Qed.
  Global Instance mapsto_fractional l v : Fractional (λ q, l ↦{q} v)%I.
  Proof.
    intros p q. by rewrite mapsto_eq /mapsto_def -own_op -auth_frag_op
      op_singleton -pair_op agree_idemp.
  Qed.
  Global Instance mapsto_as_fractional l q v :
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split. done. apply _. Qed.

  Lemma mapsto_agree l q1 q2 v1 v2 : l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply wand_intro_r.
    rewrite mapsto_eq /mapsto_def -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv. rewrite auth_frag_valid op_singleton singleton_valid -pair_op.
    by intros [_ ?%agree_op_invL'].
  Qed.

  Lemma mapsto_combine l q1 q2 v1 v2 :
    l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ l ↦{q1 + q2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (mapsto_agree with "Hl1 Hl2") as %->.
    iCombine "Hl1 Hl2" as "Hl". eauto with iFrame.
  Qed.

  Global Instance ex_mapsto_fractional l : Fractional (λ q, l ↦{q} -)%I.
  Proof.
    intros p q. iSplit.
    - iDestruct 1 as (v) "[H1 H2]". iSplitL "H1"; eauto.
    - iIntros "[H1 H2]". iDestruct "H1" as (v1) "H1". iDestruct "H2" as (v2) "H2".
      iDestruct (mapsto_agree with "H1 H2") as %->. iExists v2. by iFrame.
  Qed.
  Global Instance ex_mapsto_as_fractional l q :
    AsFractional (l ↦{q} -) (λ q, l ↦{q} -)%I q.
  Proof. split. done. apply _. Qed.

  Lemma mapsto_valid l q v : l ↦{q} v -∗ ✓ q.
  Proof.
    rewrite mapsto_eq /mapsto_def own_valid !discrete_valid -auth_frag_valid.
    by apply pure_mono=> /singleton_valid [??].
  Qed.
  Lemma mapsto_valid_2 l q1 q2 v1 v2 : l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %->.
    iApply (mapsto_valid l _ v2). by iFrame.
  Qed.

  (** Update lemmas *)
  Lemma gen_heap_alloc σ l v :
    σ !! l = None →
    gen_heap_ctx σ ==∗ gen_heap_ctx (<[l:=v]>σ) ∗ l ↦ v.
  Proof.
    iIntros (Hσl). rewrite /gen_heap_ctx mapsto_eq /mapsto_def /=.
    iIntros "Hσ".
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ (1%Qp, to_agree (v:leibnizO _)))=> //.
      by apply lookup_to_gen_heap_None. }
    iModIntro. iFrame "Hl".
    rewrite to_gen_heap_insert //.
  Qed.

  Lemma gen_heap_alloc_gen σ σ' :
    σ' ##ₘ σ →
    gen_heap_ctx σ ==∗
    gen_heap_ctx (σ' ∪ σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↦ v).
  Proof.
    revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    by iMod (gen_heap_alloc with "Hσ'σ") as "($ & $)";
      first by apply lookup_union_None.
  Qed.

  Lemma gen_heap_valid σ l q v : gen_heap_ctx σ -∗ l ↦{q} v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_both_valid; auto.
  Qed.

  Lemma gen_heap_update σ l v1 v2 :
    gen_heap_ctx σ -∗ l ↦ v1 ==∗ gen_heap_ctx (<[l:=v2]>σ) ∗ l ↦ v2.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_both_valid.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (1%Qp, to_agree (v2:leibnizO _)))=> //.
      by rewrite /to_gen_heap lookup_fmap Hl. }
    iModIntro. iFrame "Hl". rewrite to_gen_heap_insert //.
  Qed.

  Lemma gen_heap_delete σ l v :
    l ↦ v ∗ gen_heap_ctx σ ==∗ gen_heap_ctx (delete l σ).
  Proof.
    iIntros "[Hl Hσ]".
    iDestruct (gen_heap_valid with "Hσ Hl") as %?.
    rewrite /gen_heap_ctx mapsto_eq /mapsto_def /=.
    iMod (own_update with "[Hl Hσ]") as "Hσ".
    2: iApply own_op; iFrame.
    { eapply auth_update_dealloc.
      eapply delete_singleton_local_update.
      apply pair_exclusive_l.
      apply frac_full_exclusive.
    }

    iModIntro. rewrite to_gen_heap_delete //.
  Qed.

End gen_heap.
