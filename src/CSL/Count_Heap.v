(* This is a modification of the Iris 'gen_heap'.v file to using counting
   permissions and arbitrary function maps instead of fractional permissions and gmaps
   a very common pattern for Armada examples. *)

From iris.algebra Require Import auth agree functions.
From RecoveryRefinement.CSL Require Import Counting.
From iris.base_logic.lib Require Export own.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.
From Classes Require Import EqualDec.
Import EqualDecNotation.

Global Instance partial_fn_insert (A T : Type) `{EqualDec A} : Insert A T (A → option T) :=
  λ (a : A) (t : T) (f : A → option T) (b : A),
    if b == a then Some t else f b.
Global Instance partial_fn_delete (A T : Type) `{EqualDec A} : Delete A (A → option T) :=
  λ (a : A) (f : A → option T) (b : A),
    if b == a then None else f b.

Definition gen_heapUR L V `{EqualDec L}: ucmraT :=
  ofe_funUR (fun (a: L) => optionUR (prodR countingR (agreeR (leibnizC V)))).
Definition to_gen_heap {L V} `{EqualDec L} (f: L → option V): gen_heapUR L V :=
  λ k, match (f k) with
       | None => None
       | Some v => Some (Count 0, to_agree (v: leibnizC V))
       end.

(** The CMRA we need. *)
Class gen_heapG (L V : Type) (Σ : gFunctors) `{EqualDec L} := GenHeapG {
  gen_heap_inG :> inG Σ (authR (gen_heapUR L V));
  gen_heap_name : gname
}.
Arguments gen_heap_name {_ _ _ _} _ : assert.

Class gen_heapPreG (L V : Type) (Σ : gFunctors) `{EqualDec L} :=
  { gen_heap_preG_inG :> inG Σ (authR (gen_heapUR L V)) }.

Definition gen_heapΣ (L V : Type) `{EqualDec L} : gFunctors :=
  #[GFunctor (authR (gen_heapUR L V))].

Instance subG_gen_heapPreG {Σ L V} `{EqualDec L} :
  subG (gen_heapΣ L V) Σ → gen_heapPreG L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{hG : gen_heapG L V Σ}.

  Definition gen_heap_ctx (σ : L → option V) : iProp Σ :=
    own (gen_heap_name hG) (● (to_gen_heap σ)).

  Definition mapsto_def (l : L) (n: Z) (v: V) : iProp Σ :=
    own (gen_heap_name hG)
        (◯ (fun l' =>
              if l' == l then
                Some (Count (n: Z), to_agree (v : leibnizC V))
              else
                ε)).
  Definition mapsto_aux : seal (@mapsto_def). by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).

  Definition read_mapsto_def (l : L) (v: V) : iProp Σ :=
    own (gen_heap_name hG)
        (◯ (fun l' =>
              if l' == l then
                Some (Count (-1), to_agree (v : leibnizC V))
              else
                ε)).
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
  Context (L V : Type) `{EqualDec L}.
  Implicit Types σ : L → option V.

  (** Conversion to heaps and back *)
  Lemma to_gen_heap_valid σ : ✓ to_gen_heap σ.
  Proof. rewrite /to_gen_heap => l. by case (σ l). Qed.
  Lemma lookup_to_gen_heap_None σ l : σ l = None → to_gen_heap σ l = None.
  Proof. rewrite /to_gen_heap. by case (σ l). Qed.
  Lemma gen_heap_singleton_included σ l q v :
    ((fun l' => if l' == l then
                  Some (Count q, to_agree (v : leibnizC V))
                else
                  ε) : gen_heapUR L V) ≼ to_gen_heap σ → σ l = Some v.
  Proof.
    intros Hincl. apply (ofe_fun_included_spec_1 _ _ l) in Hincl.
    move: Hincl. rewrite /to_gen_heap.
    destruct (l == l); last congruence.
    destruct (σ l).
    - move=> /Some_pair_included_total_2 [_] /to_agree_included /leibniz_equiv_iff -> //.
    - rewrite option_included. intros [?|Hcase].
      * congruence.
      * repeat destruct Hcase as [? Hcase]. congruence.
  Qed.
  Lemma to_gen_heap_insert l v σ :
    to_gen_heap (<[l:=v]> σ) ≡ <[l:=(Count 0, to_agree (v:leibnizC V))]> (to_gen_heap σ).
  Proof.
    rewrite /to_gen_heap=> k//=.
    rewrite /insert/partial_fn_insert.
    destruct ((k == l)) => //=.
  Qed.
  Lemma to_gen_heap_delete l σ :
    to_gen_heap (delete l σ) ≡ delete l (to_gen_heap σ).
  Proof.
    rewrite /to_gen_heap=> k//=.
    rewrite /delete/partial_fn_delete.
    destruct ((k == l)) => //=.
  Qed.
End to_gen_heap.

Lemma gen_heap_init `{gen_heapPreG L V Σ} σ :
  (|==> ∃ _ : gen_heapG L V Σ, gen_heap_ctx σ)%I.
Proof.
  iMod (own_alloc (● to_gen_heap σ)) as (γ) "Hh".
  { apply: auth_auth_valid. exact: to_gen_heap_valid. }
  iModIntro. by iExists (GenHeapG L V Σ _ _ γ).
Qed.

Section gen_heap.
  Context `{gen_heapG L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : L → option V.
  Implicit Types h g : gen_heapUR L V.
  Implicit Types l : L.
  Implicit Types v : V.

  (** General properties of mapsto *)
  Global Instance mapsto_timeless l q v : Timeless (l ↦{q} v).
  Proof. rewrite mapsto_eq /mapsto_def. apply _. Qed.
  Global Instance read_mapsto_timeless l v : Timeless (l r↦ v).
  Proof. rewrite read_mapsto_eq /read_mapsto_def. apply _. Qed.

  Lemma mapsto_agree l q1 v1 v2 : l ↦{q1} v1 -∗ l r↦ v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply wand_intro_r.
    rewrite mapsto_eq read_mapsto_eq /mapsto_def /read_mapsto_def.
    rewrite -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_own_valid /=.
    intros Hval. move: (Hval l). rewrite ofe_fun_lookup_op.
    destruct ((l == l)); last by congruence.
    rewrite -Some_op pair_op.
    by intros [_ ?%agree_op_invL'].
  Qed.

  Lemma mapsto_valid l q1 q2 v1 v2 : q1 >= 0 → q2 >= 0 → l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ False.
  Proof.
    intros ??.
    apply wand_intro_r.
    rewrite mapsto_eq /mapsto_def.
    rewrite -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_own_valid /=.
    intros Hval. move: (Hval l). rewrite ofe_fun_lookup_op.
    destruct ((l == l)); last by congruence.
    rewrite -Some_op pair_op.
    intros [Hcount ?].
    rewrite counting_op' //= in Hcount.
    repeat destruct decide => //=. lia.
  Qed.

  Lemma read_split_join l (q: nat) v : l ↦{q} v ⊣⊢ (l ↦{S q} v ∗ l r↦ v).
  Proof.
    rewrite mapsto_eq read_mapsto_eq /mapsto_def /read_mapsto_def.
    rewrite -own_op -auth_frag_op.
    f_equiv. split => //= l'. rewrite ofe_fun_lookup_op.
    destruct ((l' == l)) => //=.
    rewrite -Some_op pair_op.
    rewrite counting_op' //=.
    replace (S q + (-1))%Z with (q : Z) by lia.
    repeat (destruct (decide)); try lia.
    by rewrite agree_idemp.
  Qed.

  (* TODO move *)
  Lemma ofe_fun_local_update `{EqualDec A} {B: A → ucmraT} f1 f2 f1' f2' :
    (∀ x, (f1 x, f2 x) ~l~> (f1' x , f2' x)) →
    (f1 : ofe_fun B, f2) ~l~> (f1', f2').
  Proof.
    intros Hupd.
    apply local_update_unital=> n mf Hmv Hm; simpl in *.
    split.
    - intros k. specialize (Hupd k). specialize (Hm k). rewrite ofe_fun_lookup_op in Hm.
      edestruct (Hupd n (Some (mf k))); eauto.
    - intros k. specialize (Hupd k). specialize (Hm k). rewrite ofe_fun_lookup_op in Hm.
      edestruct (Hupd n (Some (mf k))); eauto.
  Qed.

  Lemma gen_heap_alloc σ l v :
    σ l = None → gen_heap_ctx σ ==∗ gen_heap_ctx (<[l:=v]>σ) ∗ l ↦ v.
  Proof.
    iIntros (Hnone) "Hσ". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iMod (own_update _ _ (● to_gen_heap (<[l := v]> σ) ⋅ ◯ <[l := (Count 0, to_agree v)]>ε)
            with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc. apply ofe_fun_local_update => k.
      rewrite /to_gen_heap.
      rewrite /insert/partial_fn_insert.
      destruct ((k == l)).
      * subst. rewrite /insert/partial_fn_insert. destruct ((l == l)); last by congruence.
        rewrite Hnone.
        rewrite ofe_fun_lookup_empty.
        apply (alloc_option_local_update (Count 0, to_agree (v:leibnizC _)))=> //.
      * reflexivity.
    }
    by iFrame.
  Qed.

  Lemma gen_heap_dealloc σ l v :
    gen_heap_ctx σ -∗ l ↦ v ==∗ gen_heap_ctx (delete l σ).
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    rewrite to_gen_heap_delete. iApply (own_update_2 with "Hσ Hl").
    eapply auth_update_dealloc.
    apply ofe_fun_local_update => k.
    rewrite /delete/partial_fn_delete.
    destruct ((k == l)).
    * apply delete_option_local_update; apply _.
    * reflexivity.
  Qed.

  Lemma gen_heap_valid σ l q v : gen_heap_ctx σ -∗ l ↦{q} v -∗ ⌜σ l = Some v⌝.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_valid_discrete_2; auto.
  Qed.

  Lemma gen_heap_valid_2 σ l v : gen_heap_ctx σ -∗ l r↦ v -∗ ⌜σ l = Some v⌝.
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
    iMod (own_update_2 _ _ _ (● to_gen_heap (<[l := v2]> σ) ⋅ ◯ <[l := (Count 0, to_agree v2)]>ε)
            with "Hσ Hl") as "[Hσ Hl]".
    { eapply auth_update, ofe_fun_local_update => k.
      rewrite /to_gen_heap/insert/partial_fn_insert//=.
      destruct ((k == l)).
      * subst. rewrite Hl.
        unshelve (apply: option_local_update).
        apply exclusive_local_update=>//=.
      * reflexivity.
    }
    by iFrame.
  Qed.
End gen_heap.
