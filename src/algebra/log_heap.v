(* Multi-generational heaps *)
From iris.algebra Require Import auth gmap frac agree functions list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export own invariants.
From iris.base_logic.lib Require Import gen_heap.
From iris.proofmode Require Import tactics.

From Perennial.algebra Require Import auth_map.

Set Default Proof Using "Type".
Import uPred.

Class log_heapG (L V: Type) (Σ : gFunctors) `{Countable L} := LogHeapG {
  log_heap_inG :> mapG Σ L V;
  log_heap_name : gname
}.

Arguments log_heap_name {_ _ _ _ _} _ : assert.

Class log_heapPreG (L V : Type) (Σ : gFunctors) `{Countable L} :=
  { log_heap_preG_inG :> mapG Σ L V }.

Definition log_heapΣ (L V : Type) `{Countable L} : gFunctors :=
  mapΣ L V.

Instance subG_log_heapPreG {Σ L V} `{Countable L} :
  subG (log_heapΣ L V) Σ → log_heapPreG L V Σ.
Proof. solve_inG. Qed.

Record async T := {
  latest : T;
  pending : list T;
}.

Arguments Build_async {_} _ _.
Arguments latest {_} _.
Arguments pending {_} _.

Definition possible {T} (ab : async T) :=
  pending ab ++ [latest ab].

Definition sync {T} (v : T) : async T :=
  Build_async v nil.

Definition async_put {T} (v : T) (a : async T) :=
  Build_async v (possible a).

Lemma length_possible_pending {T} (a : async T) :
  length (possible a) = S (length (pending a)).
Proof. rewrite /possible last_length //. Qed.
Lemma length_possible_pending' {T} (a : async T) :
  length (possible a) - 1 = length (pending a).
Proof. rewrite /possible last_length. lia. Qed.

Lemma lookup_possible_latest {T} (a : async T) :
  possible a !! length (pending a) = Some (latest a).
Proof.
  rewrite /possible.
  rewrite -> lookup_app_r by lia.
  replace (length (pending a) - length (pending a)) with 0 by lia.
  reflexivity.
Qed.
Lemma lookup_possible_latest' {T} (a : async T) :
  possible a !! (length (possible a) - 1) = Some (latest a).
Proof. rewrite length_possible_pending'. apply lookup_possible_latest. Qed.

Lemma possible_async_put {T} (v:T) a :
  possible (async_put v a) = possible a ++ [v].
Proof. rewrite /async_put /possible //. Qed.

Lemma length_possible_async_put {T} (v:T) a :
  length (possible (async_put v a)) = S (length (possible a)).
Proof. rewrite possible_async_put !app_length /=. lia. Qed.

Section definitions.
  Context `{hG : log_heapG L V Σ}.

  Definition log_heap_ctx (σl : async (gmap L V)) : iProp Σ :=
    map_ctx (log_heap_name hG) 1 (latest σl).

  Definition mapsto_cur (l: L) (v: V) : iProp Σ :=
    ptsto_mut hG.(log_heap_name) l 1 v.

End definitions.

Lemma seq_heap_init `{log_heapPreG L V Σ} σl:
  ⊢ |==> ∃ _ : log_heapG L V Σ, log_heap_ctx σl ∗
    [∗ map] l↦v ∈ latest σl, mapsto_cur l v.
Proof.
Admitted.


Section log_heap.
  Context `{log_heapG L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L V.
  Implicit Types σl : async (gmap L V).
  Implicit Types l : L.
  Implicit Types v : V.

  Lemma log_heap_valid_cur σl l v :
    log_heap_ctx σl -∗
      mapsto_cur l v -∗
      ⌜latest σl !! l = Some v⌝.
  Proof.
    rewrite /log_heap_ctx /mapsto_cur.
    iIntros "Hctx Hl".
    iDestruct (map_valid with "Hctx Hl") as %Hlookup; done.
  Qed.

  Lemma map_ptsto_to_exists_map (m: gmap L V) :
    ([∗ map] l↦_ ∈ m, ∃ v', mapsto_cur l v') -∗
    ∃ (m0: gmap L V), ⌜dom (gset _) m0 = dom (gset _) m⌝ ∗
          [∗ map] l↦v ∈ m0, mapsto_cur l v.
  Proof.
    induction m as [|l v m] using map_ind.
    - rewrite big_sepM_empty.
      iIntros "_". iExists ∅.
      iSplit; first done.
      rewrite big_sepM_empty; done.
    - rewrite big_sepM_insert //.
      iIntros "[Hl Hm]".
      iDestruct "Hl" as (v') "Hl".
      iDestruct (IHm with "Hm") as (m0 Hdom) "Hm".
      iExists (<[l:=v']> m0).
      iSplit.
      + iPureIntro.
        rewrite !dom_insert_L. congruence.
      + rewrite big_sepM_insert; [ by iFrame | ].
        apply not_elem_of_dom.
        apply not_elem_of_dom in H1.
        congruence.
  Qed.

  Lemma log_heap_append σl σmod :
    log_heap_ctx σl -∗
      ( [∗ map] l↦v ∈ σmod, ∃ v', mapsto_cur l v' ) ==∗
      let σ := σmod ∪ (latest σl) in
      log_heap_ctx (async_put σ σl) ∗
      ( [∗ map] l↦v ∈ σmod, mapsto_cur l v ).
  Proof.
    iIntros "Hctx Hm0".
    iDestruct (map_ptsto_to_exists_map with "Hm0") as (m0 Hdom) "Hm0".
    rewrite /log_heap_ctx /=.
    iMod (map_update_map with "Hctx Hm0") as "[$ Hm]"; auto.
  Qed.

End log_heap.
