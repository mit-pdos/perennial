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
updating the generation of a heap.

This is used for the FFI layer in GooseLang.
([na_heap], which is used for the physical heap, contains a similar construction.)
*)

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

  Local Notation "l ↦ v" := (mapsto l (DfracOwn 1) v) (at level 20) : bi_scope.

  Lemma gen_heap_name_strong_init `{!gen_heapPreG L V Σ} σ :
    ⊢ |==> ∃ names : gen_heap_names, let _ := gen_heapG_update_pre _ names in
           gen_heap_interp (hG := gen_heapG_update_pre _ names) σ ∗
           [∗ map] i↦v ∈ σ, i ↦ v .
  Proof.
    (** Cannot reuse [gen_heap_init] as that does not guarnatee that the same [inG] will remain in use *)
    iMod (own_alloc (gmap_view_auth 1 (∅ : gmap L (leibnizO V)))) as (γh) "Hh".
    { exact: gmap_view_auth_valid. }
    iMod (own_alloc (gmap_view_auth 1 (∅ : gmap L gnameO))) as (γm) "Hm".
    { exact: gmap_view_auth_valid. }
    pose (names := {| gen_heap_heap_name := γh; gen_heap_meta_name := γm |}).
    iExists names.
    iAssert (gen_heap_interp (hG:=gen_heapG_update_pre _ names) ∅) with "[Hh Hm]" as "Hinterp".
    { iExists ∅; simpl. iFrame "Hh Hm". by rewrite dom_empty_L. }
    iMod (gen_heap_alloc_big _ σ with "Hinterp") as "(Hinterp & $ & _)".
    { apply map_disjoint_empty_r. }
    rewrite right_id_L. done.
  Qed.

  Lemma gen_heap_name_init `{!gen_heapPreG L V Σ} σ :
    ⊢ |==> ∃ names : gen_heap_names, gen_heap_interp (hG := gen_heapG_update_pre _ names) σ.
  Proof.
    iMod (gen_heap_name_strong_init σ) as (n) "(H&_)". iExists n. eauto.
  Qed.

  (* Cannot reuse original [gen_heap_init] because we have to make sure that the same [inG] instance remains in use. *)
  Lemma gen_heap_name_reinit {Σ} (hG: gen_heapG L V Σ) σ :
    ⊢ |==> ∃ names : gen_heap_names, gen_heap_interp (hG := gen_heapG_update hG names) σ.
  Proof.
    iMod (own_alloc (gmap_view_auth 1 (V:=leibnizO V) σ)) as (γh) "Hh".
    { apply gmap_view_auth_valid. }
    iMod (own_alloc (gmap_view_auth 1 (V:=gnameO) ∅)) as (γm) "Hm".
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

  Global Instance gen_heap_interp_abs_timeless {Σ} (hG: gen_heapG L V Σ) σ:
    AbsolutelyTimeless (gen_heap_interp (hG:=hG) σ).
  Proof. apply _. Qed.

End gen_heap_defs.
