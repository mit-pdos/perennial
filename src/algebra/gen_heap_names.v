From stdpp Require Import gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap lib.gmap_view.
From iris.base_logic.lib Require Export gen_heap.
From Perennial.algebra Require Export own_discrete atleast.
Set Default Proof Using "Type".
Import uPred.

(** Adds support to iris.base_logic.lib.gen_heap for extracting and changing the
names of ghost variables, to use as part of a crash "generation" and support
updating the generation of a heap. *)

Section gen_heap_defs.
  Context {L V : Type} `{Countable L}.

  Record gen_heap_names :=
  {
    gen_heap_heap_name : gname;
    gen_heap_meta_name : gname
  }.

  Definition gen_heapG_update {Σ} (hG: gen_heapG L V Σ) (names: gen_heap_names) :=
    GenHeapG _ _ _ _ _
             (@gen_heap_inG _ _ _ _ _ hG)
             (@gen_meta_inG _ _ _ _ _ hG)
             (@gen_meta_data_inG _ _ _ _ _ hG)
             (gen_heap_heap_name names)
             (gen_heap_meta_name names).

  Definition gen_heapG_update_pre {Σ} (hG: gen_heapPreG L V Σ) (names: gen_heap_names) :=
    GenHeapG _ _ _ _ _
             (@gen_heap_preG_inG _ _ _ _ _ hG)
             (@gen_meta_preG_inG _ _ _ _ _ hG)
             (@gen_meta_data_preG_inG _ _ _ _ _ hG)
             (gen_heap_heap_name names)
             (gen_heap_meta_name names).

  Definition gen_heapG_get_names {Σ} (hG: gen_heapG L V Σ) : gen_heap_names :=
    {| gen_heap_heap_name := gen_heap_name hG;
       gen_heap_meta_name := gen_meta_name hG |}.

  Lemma gen_heapG_get_update {Σ} (hG: gen_heapG L V Σ) :
    gen_heapG_update hG (gen_heapG_get_names hG) = hG.
  Proof. destruct hG => //=. Qed.

  Lemma gen_heapG_update_pre_get {Σ} (hG: gen_heapPreG L V Σ) names:
    (gen_heapG_get_names (gen_heapG_update_pre hG names)) = names.
  Proof. destruct hG, names => //=. Qed.

  Local Notation "l ↦ v" := (mapsto l 1 v) (at level 20) : bi_scope.

  (* FIXME: this breaks through *two* layers of abstraction.
   TODO: Equip upstream with support for "big-op" initialization, and then use that instead. *)
  Local Definition to_gen_heap (σ : gmap L V) : gmap_viewR L (leibnizO V) :=
    ◯V ((λ v, (DfracOwn 1, to_agree v)) <$> σ).

  Lemma heap_init_to_bigOp {Σ} {hG: gen_heapPreG L V Σ} n σ:
    own (gen_heap_name (gen_heapG_update_pre _ n)) (to_gen_heap σ) -∗
        let _ := gen_heapG_update_pre _ n in
        [∗ map] i↦v ∈ σ, i ↦ v .
  Proof.
    induction σ using map_ind.
    - iIntros. rewrite //=.
    - iIntros "Hown".
      rewrite big_opM_insert //.
      iAssert (own (gen_heap_name _)
                   (to_gen_heap m) ∗
                   (i ↦ x))%I
        with "[Hown]" as "[Hrest $]".
      {
        rewrite mapsto_eq /mapsto_def //.
        rewrite /to_gen_heap fmap_insert.
        rewrite insert_singleton_op; last first.
        { rewrite lookup_fmap. have: (m !! i = None). done. move=>-> //. }
        rewrite view_frag_op. iDestruct "Hown" as "(?&?)". iFrame.
        rewrite /gmap_view_frag. done.
      }
      by iApply IHσ.
  Qed.

  Lemma gen_heap_name_strong_init `{!gen_heapPreG L V Σ} σ :
    ⊢ |==> ∃ names : gen_heap_names, gen_heap_ctx (hG := gen_heapG_update_pre _ names) σ ∗
           let _ := gen_heapG_update_pre _ names in
           [∗ map] i↦v ∈ σ, i ↦ v .
  Proof.
    iMod (own_alloc (gmap_view_auth (V:=leibnizO V) σ ⋅ to_gen_heap σ)) as (γh) "(?&Hfrag)".
    { apply view_both_valid=>n k [df va]. rewrite lookup_fmap.
      destruct (σ !! k) as [v|] eqn:Hk; rewrite Hk; last done.
      simpl. intros [= <- <-]. eexists. done. }
    iMod (own_alloc (gmap_view_auth (V:=gnameO) ∅)) as (γm) "Hm".
    { apply gmap_view_auth_valid. }
    iModIntro. iExists {| gen_heap_heap_name := γh; gen_heap_meta_name := γm |}.
    iFrame. iSplitR "Hfrag".
    - iExists ∅; simpl. iFrame. by rewrite dom_empty_L.
    - by iApply heap_init_to_bigOp.
  Qed.

  Lemma gen_heap_name_init `{!gen_heapPreG L V Σ} σ :
    ⊢ |==> ∃ names : gen_heap_names, gen_heap_ctx (hG := gen_heapG_update_pre _ names) σ.
  Proof.
    iMod (gen_heap_name_strong_init σ) as (n) "(H&_)". iExists n. eauto.
  Qed.

  (* Cannot reuse original [gen_heap_init] because we have to make sure that the same [inG] instance remains in use. *)
  Lemma gen_heap_name_reinit {Σ} (hG: gen_heapG L V Σ) σ :
    ⊢ |==> ∃ names : gen_heap_names, gen_heap_ctx (hG := gen_heapG_update hG names) σ.
  Proof.
    iMod (own_alloc (gmap_view_auth (V:=leibnizO V) σ)) as (γh) "Hh".
    { apply gmap_view_auth_valid. }
    iMod (own_alloc (gmap_view_auth (V:=gnameO) ∅)) as (γm) "Hm".
    { apply gmap_view_auth_valid. }
    iModIntro. iExists {| gen_heap_heap_name := γh; gen_heap_meta_name := γm |}.
    iExists ∅; simpl. iFrame "Hh Hm". by rewrite dom_empty_L.
  Qed.

  Global Instance mapsto_discretizable {Σ} (hG: gen_heapG L V Σ) l q v:
    Discretizable (mapsto (hG:=hG) l q v).
  Proof. rewrite mapsto_eq. apply _. Qed.

  Global Instance mapsto_abs_timless {Σ} (hG: gen_heapG L V Σ) l q v:
    AbsolutelyTimeless (mapsto (hG:=hG) l q v).
  Proof. rewrite mapsto_eq. apply _. Qed.

  Global Instance gen_heap_ctx_abs_timeless {Σ} (hG: gen_heapG L V Σ) σ:
    AbsolutelyTimeless (gen_heap_ctx (hG:=hG) σ).
  Proof. apply _. Qed.

End gen_heap_defs.
