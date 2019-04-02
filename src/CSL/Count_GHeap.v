(* This is a modification of the Iris 'gen_heap'.v file to using counting
   permissions instead of fractional permissions, since that seems to be
   a very common pattern for Argosy examples. *)
(* TODO: this could be derived from Count_Heap.v, which is more generic *)
From iris.algebra Require Import auth gmap agree.
From RecoveryRefinement.CSL Require Import Counting.
From iris.base_logic.lib Require Export own.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Definition gen_heapUR (L V : Type) `{Countable L} : ucmraT :=
  gmapUR L (prodR countingR (agreeR (leibnizC V))).
Definition to_gen_heap {L V} `{Countable L} : gmap L V → gen_heapUR L V :=
  fmap (λ v, (Count 0, to_agree (v : leibnizC V))).

(** The CMRA we need. *)
Class gen_heapG (L V : Type) (Σ : gFunctors) `{Countable L} := GenHeapG {
  gen_heap_inG :> inG Σ (authR (gen_heapUR L V));
  gen_heap_name : gname
}.
Arguments gen_heap_name {_ _ _ _ _} _ : assert.

Class gen_heapPreG (L V : Type) (Σ : gFunctors) `{Countable L} :=
  { gen_heap_preG_inG :> inG Σ (authR (gen_heapUR L V)) }.

Definition gen_heapΣ (L V : Type) `{Countable L} : gFunctors :=
  #[GFunctor (authR (gen_heapUR L V))].

Instance subG_gen_heapPreG {Σ L V} `{Countable L} :
  subG (gen_heapΣ L V) Σ → gen_heapPreG L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{hG : gen_heapG L V Σ}.

  Definition gen_heap_ctx (σ : gmap L V) : iProp Σ :=
    own (gen_heap_name hG) (● (to_gen_heap σ)).

  Definition mapsto_def (l : L) (n: Z) (v: V) : iProp Σ :=
    own (gen_heap_name hG) (◯ {[ l := (Count n, to_agree (v : leibnizC V)) ]}).
  Definition mapsto_aux : seal (@mapsto_def). by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).

  Definition read_mapsto_def (l : L) (v: V) : iProp Σ :=
    own (gen_heap_name hG) (◯ {[ l := (Count (-1), to_agree (v : leibnizC V)) ]}).
  Definition read_mapsto_aux : seal (@read_mapsto_def). by eexists. Qed.
  Definition read_mapsto := read_mapsto_aux.(unseal).
  Definition read_mapsto_eq : @read_mapsto = @read_mapsto_def := read_mapsto_aux.(seal_eq).
End definitions.

Local Notation "l ↦{ q } v" := (mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Local Notation "l ↦ v" := (mapsto l 0 v) (at level 20) : bi_scope.

Local Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Local Notation "l ↦ -" := (l ↦{0} -)%I (at level 20) : bi_scope.

Local Notation "l r↦ v" := (read_mapsto l v) (at level 20, format "l  r↦  v") : bi_scope.

Local Notation "l r↦ -" := (∃ v, l r↦ v)%I
  (at level 20, format "l  r↦ -") : bi_scope.

Section to_gen_heap.
  Context (L V : Type) `{Countable L}.
  Implicit Types σ : gmap L V.

  (** Conversion to heaps and back *)
  Lemma to_gen_heap_valid σ : ✓ to_gen_heap σ.
  Proof. intros l. rewrite lookup_fmap. by case (σ !! l). Qed.
  Lemma lookup_to_gen_heap_None σ l : σ !! l = None → to_gen_heap σ !! l = None.
  Proof. by rewrite /to_gen_heap lookup_fmap=> ->. Qed.
  Lemma gen_heap_singleton_included σ l q v :
    {[l := (q, to_agree v)]} ≼ to_gen_heap σ → σ !! l = Some v.
  Proof.
    rewrite singleton_included=> -[[q' av] []].
    rewrite /to_gen_heap lookup_fmap fmap_Some_equiv => -[v' [Hl [/= -> ->]]].
    move=> /Some_pair_included_total_2 [_] /to_agree_included /leibniz_equiv_iff -> //.
  Qed.
  Lemma to_gen_heap_insert l v σ :
    to_gen_heap (<[l:=v]> σ) = <[l:=(Count 0, to_agree (v:leibnizC V))]> (to_gen_heap σ).
  Proof. by rewrite /to_gen_heap fmap_insert. Qed.
  Lemma to_gen_heap_delete l σ :
    to_gen_heap (delete l σ) = delete l (to_gen_heap σ).
  Proof. by rewrite /to_gen_heap fmap_delete. Qed.
End to_gen_heap.

Lemma gen_heap_init `{gen_heapPreG L V Σ} σ :
  (|==> ∃ _ : gen_heapG L V Σ, gen_heap_ctx σ)%I.
Proof.
  iMod (own_alloc (● to_gen_heap σ)) as (γ) "Hh".
  { apply: auth_auth_valid. exact: to_gen_heap_valid. }
  iModIntro. by iExists (GenHeapG L V Σ _ _ _ γ).
Qed.

Lemma gen_heap_strong_init `{H: gen_heapPreG L V Σ} σs :
  (|==> ∃ (H0 : gen_heapG L V Σ) (Hpf: gen_heap_inG = gen_heap_preG_inG), gen_heap_ctx σs ∗
    own (gen_heap_name _) (◯ (to_gen_heap σs)))%I.
Proof.
  iMod (own_alloc (● to_gen_heap σs ⋅ ◯ to_gen_heap σs)) as (γ) "(?&?)".
  { apply auth_valid_discrete_2; split; auto. exact: to_gen_heap_valid. }
  iModIntro. unshelve (iExists (GenHeapG L V Σ _ _ _ γ), _); auto. iFrame.
Qed.

Section gen_heap.
  Context `{hG: gen_heapG L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L V.
  Implicit Types h g : gen_heapUR L V.
  Implicit Types l : L.
  Implicit Types v : V.

  (** General properties of mapsto *)
  Global Instance mapsto_timeless l q v : Timeless (l ↦{q} v).
  Proof. rewrite mapsto_eq /mapsto_def. apply _. Qed.
  Global Instance read_mapsto_timeless l v : Timeless (l r↦ v).
  Proof. rewrite read_mapsto_eq /read_mapsto_def. apply _. Qed.

  Lemma gen_heap_init_to_bigOp σ:
    own (gen_heap_name hG) (◯ to_gen_heap σ)
        -∗ [∗ map] i↦v ∈ σ, i ↦ v .
  Proof.
    induction σ using map_ind.
    - iIntros. rewrite //=.
    - iIntros "Hown".
      rewrite big_opM_insert //.
      iAssert (own (gen_heap_name hG) (◯ to_gen_heap m) ∗ (i ↦ x))%I
        with "[Hown]" as "[Hrest $]".
      {
        rewrite mapsto_eq /mapsto_def //.
        rewrite to_gen_heap_insert insert_singleton_op; last by apply lookup_to_gen_heap_None.
        rewrite auth_frag_op. iDestruct "Hown" as "(?&?)". iFrame.
      }
      by iApply IHσ.
  Qed.

  Lemma mapsto_agree l q1 v1 v2 : l ↦{q1} v1 -∗ l r↦ v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply wand_intro_r.
    rewrite mapsto_eq read_mapsto_eq /mapsto_def /read_mapsto_def.
    rewrite -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_own_valid /=. rewrite op_singleton singleton_valid pair_op.
    by intros [_ ?%agree_op_invL'].
  Qed.

  Lemma mapsto_valid l q1 q2 v1 v2 :
    q1 >= 0 → q2 >= 0 → l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ False.
  Proof.
    intros.
    apply wand_intro_r.
    rewrite mapsto_eq /mapsto_def.
    rewrite -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_own_valid /=. rewrite op_singleton singleton_valid pair_op.
    intros [Hcount ?].
    rewrite counting_op' //= in Hcount.
    repeat destruct decide => //=. lia.
  Qed.

  Lemma read_split_join l (q: nat) v : l ↦{q} v ⊣⊢ (l ↦{S q} v ∗ l r↦ v).
  Proof.
    rewrite mapsto_eq read_mapsto_eq /mapsto_def /read_mapsto_def.
    rewrite -own_op -auth_frag_op.
    rewrite op_singleton pair_op.
    rewrite counting_op' //=.
    repeat destruct decide => //=. lia.
    replace (S q + (-1))%Z with (q : Z) by lia.
    by rewrite agree_idemp.
  Qed.

  Lemma gen_heap_alloc σ l v :
    σ !! l = None → gen_heap_ctx σ ==∗ gen_heap_ctx (<[l:=v]>σ) ∗ l ↦ v.
  Proof.
    iIntros (?) "Hσ". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ (Count 0, to_agree (v:leibnizC _)))=> //.
      by apply lookup_to_gen_heap_None. }
    iModIntro. rewrite to_gen_heap_insert. iFrame.
  Qed.

  Lemma gen_heap_dealloc σ l v :
    gen_heap_ctx σ -∗ l ↦ v ==∗ gen_heap_ctx (delete l σ).
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    rewrite to_gen_heap_delete. iApply (own_update_2 with "Hσ Hl").
    eapply auth_update_dealloc, (delete_singleton_local_update _ _ _).
  Qed.

  Lemma gen_heap_valid σ l q v : gen_heap_ctx σ -∗ l ↦{q} v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_valid_discrete_2; auto.
  Qed.

  Lemma gen_heap_valid_2 σ l v : gen_heap_ctx σ -∗ l r↦ v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx read_mapsto_eq /read_mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_valid_discrete_2; auto.
  Qed.

  Lemma gen_heap_update σ l v1 v2 :
    gen_heap_ctx σ -∗ l ↦ v1 ==∗ gen_heap_ctx (<[l:=v2]>σ) ∗ l ↦ v2.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (Count 0, to_agree (v2:leibnizC _)))=> //.
      by rewrite /to_gen_heap lookup_fmap Hl. }
    iModIntro. rewrite to_gen_heap_insert. iFrame.
  Qed.
End gen_heap.
