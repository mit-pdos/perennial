(* Multi-generational heaps *)
From iris.algebra Require Import auth gmap frac agree functions list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export own invariants.
From iris.base_logic.lib Require Import gen_heap.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(* TODO: switch to https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/486
when it's merged, rather than using gen_heapUR (this is probably necessary for
async usage so that we can persistently own maps-to facts in a particular
version) *)
Local Definition gen_heapUR (L V : Type) `{Countable L} : ucmraT :=
  gmapUR L (prodR fracR (agreeR (leibnizO V))).
Definition log_heapUR (L V : Type) `{Countable L}: ucmraT :=
  discrete_funUR (λ (n : nat), gen_heapUR L V).

Class log_heapG (L V: Type) (Σ : gFunctors) `{Countable L} := LogHeapG {
  log_heap_inG :> inG Σ (authR (log_heapUR L V));
  log_heap_name : gname
}.

Local Definition to_gen_heap {L V} `{Countable L} : gmap L V → gen_heapUR L V :=
  fmap (λ v, (1%Qp, to_agree (v : leibnizO V))).

Definition to_log_heap {L V} `{Countable L} (s: nat -> gmap L V) : log_heapUR L V :=
  λ n, to_gen_heap (s n).

Arguments log_heap_name {_ _ _ _ _} _ : assert.

Class log_heapPreG (L V : Type) (Σ : gFunctors) `{Countable L} :=
  { log_heap_preG_inG :> inG Σ (authR (log_heapUR L V)) }.

Definition log_heapΣ (L V : Type) `{Countable L} : gFunctors :=
  #[GFunctor (authR (log_heapUR L V))].

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

Lemma lookup_possible_latest {T} (a : async T) :
  possible a !! length (pending a) = Some (latest a).
Proof.
  rewrite /possible.
  rewrite -> lookup_app_r by lia.
  replace (length (pending a) - length (pending a)) with 0 by lia.
  reflexivity.
Qed.

Lemma length_possible_async_put {T} (v:T) a :
  length (possible (async_put v a)) = S (length (possible a)).
Proof.
  rewrite /possible /async_put /=.
  rewrite !app_length /=.
  lia.
Qed.

Section definitions.
  Context `{hG : log_heapG L V Σ}.

  Definition log_heap_ctx (σl : async (gmap L V)) : iProp Σ :=
    let σfun := λ n, match possible σl !! n with
                     | Some σ => σ
                     | None => latest σl
                     end in
    own (log_heap_name hG) (● (to_log_heap σfun)).

  Definition mapsto_cur (l: L) (v: V) : iProp Σ.
  Proof using hG.
    (* l ↦ v in latest σ *)
  Admitted.

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
  Implicit Types h g : log_heapUR L V.
  Implicit Types l : L.
  Implicit Types v : V.

  Lemma log_heap_valid_cur σl l v :
    log_heap_ctx σl -∗
      mapsto_cur l v -∗
      ⌜latest σl !! l = Some v⌝.
  Proof.
  Admitted.

  Lemma log_heap_append σl σmod :
    log_heap_ctx σl -∗
      ( [∗ map] l↦v ∈ σmod, ∃ v', mapsto_cur l v' ) ==∗
      let σ := σmod ∪ (latest σl) in
      log_heap_ctx (async_put σ σl) ∗
      ( [∗ map] l↦v ∈ σmod, mapsto_cur l v ).
  Proof.
  Admitted.

End log_heap.
