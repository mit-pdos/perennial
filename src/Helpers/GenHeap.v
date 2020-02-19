From stdpp Require Export namespaces.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap frac agree namespace_map.
From iris.base_logic.lib Require Export own gen_heap.
Set Default Proof Using "Type".
Import uPred.

(** This is from iris/theories/base_logic/lib/gen_heap.v with tokens removed
    so that we can support deletion. *)

(** The CMRA we need. *)
Class xgen_heapG (L V : Type) (Σ : gFunctors) `{Countable L} := XGenHeapG {
  xgen_heap_inG :> inG Σ (authR (gen_heapUR L V));
  xgen_heap_name : gname
}.
Arguments xgen_heap_name {_ _ _ _ _} _ : assert.

Class xgen_heapPreG (L V : Type) (Σ : gFunctors) `{Countable L} := {
  xgen_heap_preG_inG :> inG Σ (authR (gen_heapUR L V))
}.

Definition xgen_heapΣ (L V : Type) `{Countable L} : gFunctors := #[
  GFunctor (authR (gen_heapUR L V))
].

Instance xsubG_gen_heapPreG {Σ L V} `{Countable L} :
  subG (xgen_heapΣ L V) Σ → xgen_heapPreG L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{Countable L, hG : !xgen_heapG L V Σ}.

  Definition xgen_heap_ctx (σ : gmap L V) : iProp Σ := (
    own (xgen_heap_name hG) (● (to_gen_heap σ)))%I.

  Definition xmapsto_def (l : L) (q : Qp) (v: V) : iProp Σ :=
    own (xgen_heap_name hG) (◯ {[ l := (q, to_agree (v : leibnizO V)) ]}).
  Definition xmapsto_aux : seal (@xmapsto_def). by eexists. Qed.
  Definition xmapsto := xmapsto_aux.(unseal).
  Definition xmapsto_eq : @xmapsto = @xmapsto_def := xmapsto_aux.(seal_eq).
End definitions.

Local Notation "l ↦{ q } v" := (xmapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Local Notation "l ↦ v" := (xmapsto l 1 v) (at level 20) : bi_scope.

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

Lemma xgen_heap_init `{Countable L, !xgen_heapPreG L V Σ} σ :
  (|==> ∃ _ : xgen_heapG L V Σ, xgen_heap_ctx σ)%I.
Proof.
  iMod (own_alloc (● to_gen_heap σ)) as (γh) "Hh".
  { rewrite auth_auth_valid. exact: to_gen_heap_valid. }
  iModIntro. iExists (XGenHeapG L V Σ _ _ _ γh). done.
Qed.

Section gen_heap.
  Context {L V} `{Countable L, !xgen_heapG L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L V.
  Implicit Types h g : gen_heapUR L V.
  Implicit Types l : L.
  Implicit Types v : V.

  (** General properties of mapsto *)
  Global Instance xmapsto_timeless l q v : Timeless (l ↦{q} v).
  Proof. rewrite xmapsto_eq /xmapsto_def. apply _. Qed.
  Global Instance xmapsto_fractional l v : Fractional (λ q, l ↦{q} v)%I.
  Proof.
    intros p q. by rewrite xmapsto_eq /xmapsto_def -own_op -auth_frag_op
      op_singleton -pair_op agree_idemp.
  Qed.
  Global Instance xmapsto_as_fractional l q v :
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split. done. apply _. Qed.

  Lemma xmapsto_agree l q1 q2 v1 v2 : l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply wand_intro_r.
    rewrite xmapsto_eq /xmapsto_def -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv. rewrite auth_frag_valid op_singleton singleton_valid -pair_op.
    by intros [_ ?%agree_op_invL'].
  Qed.

  Lemma xmapsto_combine l q1 q2 v1 v2 :
    l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ l ↦{q1 + q2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (xmapsto_agree with "Hl1 Hl2") as %->.
    iCombine "Hl1 Hl2" as "Hl". eauto with iFrame.
  Qed.

  Global Instance ex_xmapsto_fractional l : Fractional (λ q, l ↦{q} -)%I.
  Proof.
    intros p q. iSplit.
    - iDestruct 1 as (v) "[H1 H2]". iSplitL "H1"; eauto.
    - iIntros "[H1 H2]". iDestruct "H1" as (v1) "H1". iDestruct "H2" as (v2) "H2".
      iDestruct (xmapsto_agree with "H1 H2") as %->. iExists v2. by iFrame.
  Qed.
  Global Instance ex_xmapsto_as_fractional l q :
    AsFractional (l ↦{q} -) (λ q, l ↦{q} -)%I q.
  Proof. split. done. apply _. Qed.

  Lemma xmapsto_valid l q v : l ↦{q} v -∗ ✓ q.
  Proof.
    rewrite xmapsto_eq /xmapsto_def own_valid !discrete_valid -auth_frag_valid.
    by apply pure_mono=> /singleton_valid [??].
  Qed.
  Lemma xmapsto_valid_2 l q1 q2 v1 v2 : l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "H1 H2". iDestruct (xmapsto_agree with "H1 H2") as %->.
    iApply (xmapsto_valid l _ v2). by iFrame.
  Qed.

  (** Update lemmas *)
  Lemma xgen_heap_alloc σ l v :
    σ !! l = None →
    xgen_heap_ctx σ ==∗ xgen_heap_ctx (<[l:=v]>σ) ∗ l ↦ v.
  Proof.
    iIntros (Hσl). rewrite /xgen_heap_ctx xmapsto_eq /xmapsto_def /=.
    iIntros "Hσ".
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ (1%Qp, to_agree (v:leibnizO _)))=> //.
      by apply lookup_to_gen_heap_None. }
    iModIntro. iFrame "Hl".
    rewrite to_gen_heap_insert //.
  Qed.

  Lemma xgen_heap_alloc_gen σ σ' :
    σ' ##ₘ σ →
    xgen_heap_ctx σ ==∗
    xgen_heap_ctx (σ' ∪ σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↦ v).
  Proof.
    revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    by iMod (xgen_heap_alloc with "Hσ'σ") as "($ & $)";
      first by apply lookup_union_None.
  Qed.

  Lemma xgen_heap_valid σ l q v : xgen_heap_ctx σ -∗ l ↦{q} v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl".
    rewrite /xgen_heap_ctx xmapsto_eq /xmapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_both_valid; auto.
  Qed.

  Lemma xgen_heap_update σ l v1 v2 :
    xgen_heap_ctx σ -∗ l ↦ v1 ==∗ xgen_heap_ctx (<[l:=v2]>σ) ∗ l ↦ v2.
  Proof.
    iIntros "Hσ Hl". rewrite /xgen_heap_ctx xmapsto_eq /xmapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_both_valid.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (1%Qp, to_agree (v2:leibnizO _)))=> //.
      by rewrite /to_gen_heap lookup_fmap Hl. }
    iModIntro. iFrame "Hl". rewrite to_gen_heap_insert //.
  Qed.

  Lemma xgen_heap_delete σ l v :
    l ↦ v ∗ xgen_heap_ctx σ ==∗ xgen_heap_ctx (delete l σ).
  Proof.
    iIntros "[Hl Hσ]".
    iDestruct (xgen_heap_valid with "Hσ Hl") as %?.
    rewrite /xgen_heap_ctx xmapsto_eq /xmapsto_def /=.
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
