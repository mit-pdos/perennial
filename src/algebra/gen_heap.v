From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import gen_heap.
Set Default Proof Using "Type".
Import uPred.

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

  Lemma gen_heap_name_init `{!gen_heapPreG L V Σ} σ :
    (|==> ∃ names : gen_heap_names, gen_heap_ctx (hG := gen_heapG_update_pre _ names) σ)%I.
  Proof.
    iMod (own_alloc (● to_gen_heap σ)) as (γh) "Hh".
    { rewrite auth_auth_valid. exact: to_gen_heap_valid. }
    iMod (own_alloc (● to_gen_meta ∅)) as (γm) "Hm".
    { rewrite auth_auth_valid. exact: to_gen_meta_valid. }
    iModIntro. iExists {| gen_heap_heap_name := γh; gen_heap_meta_name := γm |}.
    iExists ∅; simpl. iFrame "Hh Hm". by rewrite dom_empty_L.
  Qed.

  Lemma gen_heap_reinit {Σ} (hG: gen_heapG L V Σ) σ :
    (|==> ∃ names : gen_heap_names, gen_heap_ctx (hG := gen_heapG_update hG names) σ)%I.
  Proof.
    iMod (own_alloc (● to_gen_heap σ)) as (γh) "Hh".
    { rewrite auth_auth_valid. exact: to_gen_heap_valid. }
    iMod (own_alloc (● to_gen_meta ∅)) as (γm) "Hm".
    { rewrite auth_auth_valid. exact: to_gen_meta_valid. }
    iModIntro. iExists {| gen_heap_heap_name := γh; gen_heap_meta_name := γm |}.
    iExists ∅; simpl. iFrame "Hh Hm". by rewrite dom_empty_L.
  Qed.

End gen_heap_defs.

