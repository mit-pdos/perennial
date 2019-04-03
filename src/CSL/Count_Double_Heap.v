(* Algebra/rules for a simple 1 level directory hierarchy *)

(* TODO: derive Count_GHeap.v from this or vice-versa *)

(* The main issue is that collapsing a gmap of gmaps to a gmap from full paths to values
   is awkward. This a case where having things in terms of arbitrary partial fns
   (as in Count_Heap.v) would be better, but there we have LockStatus, which
   doesn't work the same way here, and you lose Leibniz Equality. *)

From iris.algebra Require Import auth gmap agree.
From RecoveryRefinement.CSL Require Import Counting Count_GHeap.
From iris.base_logic.lib Require Export own.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Definition gen_dirUR (L1 L2 V : Type) `{Countable L1} `{Countable L2} : ucmraT :=
  gmapUR L1 (gmapUR L2 (prodR countingR (agreeR (leibnizC V)))).
Definition to_gen_dir {L1 L2 V} `{Countable L1} `{Countable L2} :
  gmap L1 (gmap L2 V) → gen_dirUR L1 L2 V :=
  fmap (λ m, to_gen_heap m).

(** The CMRA we need. *)
Class gen_dirG (L1 L2 V : Type) (Σ : gFunctors) `{Countable L1} `{Countable L2} := GenDirG {
  gen_dir_inG :> inG Σ (authR (gen_dirUR L1 L2 V));
  gen_dir_name : gname
}.
Arguments gen_dir_name {_ _ _ _ _ _ _ _} _ : assert.

Class gen_dirPreG (L1 L2 V : Type) (Σ : gFunctors) `{Countable L1} `{Countable L2} :=
  { gen_dir_preG_inG :> inG Σ (authR (gen_dirUR L1 L2 V)) }.

Definition gen_dirΣ (L1 L2 V : Type) `{Countable L1} `{Countable L2} : gFunctors :=
  #[GFunctor (authR (gen_dirUR L1 L2 V))].

Instance subG_gen_dirPreG {Σ L1 L2 V} `{Countable L1} `{Countable L2} :
  subG (gen_dirΣ L1 L2 V) Σ → gen_dirPreG L1 L2 V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{hG : gen_dirG L1 L2 V Σ}.

  Definition gen_dir_ctx (σ : gmap L1 (gmap L2 V)) : iProp Σ :=
    own (gen_dir_name hG) (● (to_gen_dir σ)).

  Definition mapsto_def (l1 : L1) (l2: L2) (n: Z) (v: V) : iProp Σ :=
    own (gen_dir_name hG) (◯ {[ l1 := {[ l2 := (Count n, to_agree (v : leibnizC V)) ]} ]}).
  Definition mapsto_aux : seal (@mapsto_def). by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).

  Definition read_mapsto l1 l2 v : iProp Σ := mapsto l1 l2 (-1) v.
End definitions.

Local Notation "l1 / l2 ↦{ q } v" := (mapsto l1 l2 q v)
  (at level 20, q at level 50, format "l1 / l2  ↦{ q }  v") : bi_scope.
Local Notation "l1 / l2 ↦ v" := (mapsto l1 l2 0 v) (at level 20) : bi_scope.

Local Notation "l1 / l2 ↦{ q } -" := (∃ v, l1 / l2 ↦{q} v)%I
  (at level 20, q at level 50, format "l1 / l2  ↦{ q }  -") : bi_scope.
Local Notation "l1 / l2 ↦ -" := (l1 / l2 ↦{0} -)%I (at level 20) : bi_scope.

Local Notation "l1 / l2 r↦ v" := (read_mapsto l1 l2 v) (at level 20, format "l1 / l2  r↦  v") : bi_scope.

Local Notation "l1 / l2 r↦ -" := (∃ v, l1 / l2 r↦ v)%I
  (at level 20, format "l1 / l2  r↦ -") : bi_scope.

Section to_gen_dir.
  Context (L1 L2 V : Type) `{Countable L1} `{Countable L2}.
  Implicit Types σ : gmap L1 (gmap L2 V).

  (** Conversion to dirs and back *)
  Lemma to_gen_dir_valid σ : ✓ to_gen_dir σ.
  Proof.
    intros l1. rewrite lookup_fmap.
    case (σ !! l1); last done.
    intros m l2. rewrite lookup_fmap.
    case (m !! l2); done.
  Qed.
  Lemma lookup_to_gen_dir_None σ l : σ !! l = None → to_gen_dir σ !! l = None.
  Proof. by rewrite /to_gen_dir lookup_fmap=> ->. Qed.
  Lemma lookup_to_gen_dir_Some σ σd l :
    σ !! l = Some σd → to_gen_dir σ !! l = Some (to_gen_heap σd).
  Proof. by rewrite /to_gen_dir lookup_fmap=> ->. Qed.
  Lemma lookup_to_gen_dir_None2 σ σd l1 l2 :
    σ !! l1 = Some σd →
    σd !! l2 = None →
    to_gen_dir σ !! l1 = Some (to_gen_heap σd) /\
    to_gen_heap σd !! l2 = None.
  Proof. by intros ?%lookup_to_gen_dir_Some ?%lookup_to_gen_heap_None. Qed.
  Lemma gen_dir_singleton_included σ l1 l2 q v :
    {[l1 := {[ l2 := (q, to_agree v)]} ]} ≼ to_gen_dir σ →
    ∃ σd, σ !! l1 = Some σd ∧ σd !! l2 = Some v.
  Proof.
    rewrite singleton_included=> -[[q' av] []].
    rewrite /to_gen_dir lookup_fmap fmap_Some_equiv => -[σd [Hl ->]].
    move=>/Some_included_total. eauto using gen_heap_singleton_included.
  Qed.
  Lemma to_gen_dir_insert1 l1 m σ :
    to_gen_dir (<[l1 :=m]> σ) = <[l1:=to_gen_heap m]> (to_gen_dir σ).
  Proof. by rewrite /to_gen_dir fmap_insert. Qed.
  Lemma to_gen_dir_insert2 l1 l2 v (m: gmap L2 V) σ :
    to_gen_dir (<[l1 := <[l2 := v]> m]> σ) =
    <[l1:= (<[l2 := (Count 0, to_agree (v: leibnizC V))]> (to_gen_heap m))]> (to_gen_dir σ).
  Proof. by rewrite to_gen_dir_insert1 to_gen_heap_insert. Qed.
  Lemma to_gen_dir_delete1 l σ :
    to_gen_dir (delete l σ) = delete l (to_gen_dir σ).
  Proof. by rewrite /to_gen_dir fmap_delete. Qed.
  Lemma to_gen_dir_delete2 (l1: L1) (l2: L2) (m: gmap L2 V) σ :
    to_gen_dir (<[l1 := delete l2 m]> σ) = <[l1 := delete l2 (to_gen_heap m) ]> (to_gen_dir σ).
  Proof. by rewrite to_gen_dir_insert1 to_gen_heap_delete. Qed.
End to_gen_dir.

Lemma gen_dir_init `{gen_dirPreG L1 L2 V Σ} σ :
  (|==> ∃ _ : gen_dirG L1 L2 V Σ, gen_dir_ctx σ)%I.
Proof.
  iMod (own_alloc (● to_gen_dir σ)) as (γ) "Hh".
  { apply: auth_auth_valid. exact: to_gen_dir_valid. }
  iModIntro. by iExists (GenDirG L1 L2 V Σ _ _ _ _ _ γ).
Qed.

Section gen_dir.
  Context `{gen_dirG L1 L2 V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L1 (gmap L2 V).
  Implicit Types h g : gen_dirUR L1 L2 V.
  Implicit Types v : V.
  Implicit Types d: L1.
  Implicit Types f: L2.

  (** General properties of mapsto *)
  Global Instance mapsto_timeless (l1: L1) (l2: L2) q v : Timeless (l1 / l2 ↦{q} v).
  Proof. rewrite mapsto_eq /mapsto_def. apply _. Qed.
  Global Instance read_mapsto_timeless (l1: L1) (l2: L2) v : Timeless (l1 / l2 r↦ v).
  Proof. apply _. Qed.

  Lemma mapsto_agree d f q1 v1 v2 : d / f ↦{q1} v1 -∗ d / f r↦ v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply wand_intro_r.
    rewrite /read_mapsto mapsto_eq /mapsto_def.
    rewrite -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_own_valid /=. rewrite ?op_singleton ?singleton_valid pair_op.
    by intros [_ ?%agree_op_invL'].
  Qed.

  Lemma mapsto_valid d f q1 q2 v1 v2 :
    q1 >= 0 → q2 >= 0 → d/f ↦{q1} v1 -∗ d/f ↦{q2} v2 -∗ False.
  Proof.
    intros.
    apply wand_intro_r.
    rewrite mapsto_eq /mapsto_def.
    rewrite -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_own_valid /=. rewrite ?op_singleton ?singleton_valid pair_op.
    intros [Hcount ?].
    rewrite counting_op' //= in Hcount.
    repeat destruct decide => //=. lia.
  Qed.

  Lemma read_split_join d f (q: nat) v : d/f ↦{q} v ⊣⊢ (d/f ↦{S q} v ∗ d/f r↦ v).
  Proof.
    rewrite /read_mapsto mapsto_eq /mapsto_def.
    rewrite -own_op -auth_frag_op.
    rewrite ?op_singleton pair_op.
    rewrite counting_op' //=.
    repeat destruct decide => //=. lia.
    replace (S q + (-1))%Z with (q : Z) by lia.
    by rewrite agree_idemp.
  Qed.

  Lemma gen_dir_alloc1 σ d f v :
    σ !! d = None → gen_dir_ctx σ ==∗ gen_dir_ctx (<[d := {[f:=v]}]>σ) ∗ d / f ↦ v.
  Proof.
    iIntros (?) "Hσ". rewrite /gen_dir_ctx mapsto_eq /mapsto_def.
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ {[ f := (Count 0, to_agree (v:leibnizC _))]})=> //.
        - by apply lookup_to_gen_dir_None.
        - by apply singleton_valid.
    }
    iModIntro. rewrite to_gen_dir_insert1 /to_gen_heap map_fmap_singleton. iFrame.
  Qed.

  Lemma gen_dir_alloc2 σ σd d f v :
    σ !! d = Some σd →
    σd !! f = None →
    gen_dir_ctx σ ==∗ gen_dir_ctx (<[d := <[f:=v]> σd]>σ) ∗ d / f ↦ v.
  Proof.
    iIntros (??) "Hσ". rewrite /gen_dir_ctx mapsto_eq /mapsto_def.
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc.
      eapply insert_alloc_local_update.
      - by apply lookup_to_gen_dir_Some.
      - rewrite //=.
      - eapply (alloc_singleton_local_update _ _ (Count 0, to_agree (v:leibnizC _))) => //=.
        by apply lookup_to_gen_heap_None.
    }
    iModIntro. rewrite to_gen_dir_insert1 to_gen_heap_insert. iFrame.
  Qed.

  Lemma gen_dir_dealloc σ σd d f v :
    σ !! d = Some σd →
    gen_dir_ctx σ -∗ d / f ↦ v ==∗ gen_dir_ctx (<[d := delete f σd]> σ).
  Proof.
    iIntros (?) "Hσ Hl". rewrite /gen_dir_ctx mapsto_eq /mapsto_def.
    rewrite to_gen_dir_delete2.
    iMod (own_update_2 with "Hσ Hl") as "[$ Hl]"; last by auto.
    eapply auth_update, singleton_local_update.
    { by eapply lookup_to_gen_dir_Some. }
    eapply (delete_singleton_local_update _ _ _).
  Qed.

  Lemma gen_dir_valid σ d f q v :
    gen_dir_ctx σ -∗ d / f ↦{q} v -∗ ⌜ ∃ σd, σ !! d = Some σd ∧ σd !! f = Some v⌝.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_dir_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_dir_singleton_included _]%auth_valid_discrete_2; auto.
  Qed.

  Lemma gen_dir_valid_2 σ d f v :
    gen_dir_ctx σ -∗ d / f r↦ v -∗ ⌜ ∃ σd, σ !! d = Some σd ∧ σd !! f = Some v⌝.
  Proof. apply gen_dir_valid. Qed.

  Lemma gen_dir_update σ σd d f v1 v2 :
    σ !! d = Some σd →
    gen_dir_ctx σ -∗ d / f ↦ v1 ==∗ gen_dir_ctx ((<[d := <[f:=v2]> σd]> σ)) ∗ d / f ↦ v2.
  Proof.
    iIntros (?) "Hσ Hl". rewrite /gen_dir_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_dir_singleton_included _]%auth_valid_discrete_2.
    destruct Hl as (σd'&Hlookup&Hdf). assert (σd = σd') as <- by congruence.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ Hl]".
    { eapply auth_update, singleton_local_update.
      { by eapply lookup_to_gen_dir_Some. }
      eapply singleton_local_update,
        (exclusive_local_update _ (Count 0, to_agree (v2:leibnizC _)))=> //.
      by rewrite /to_gen_dir lookup_fmap Hdf. }
    iModIntro. rewrite to_gen_dir_insert2. iFrame.
  Qed.
End gen_dir.