From iris.base_logic Require Export lib.gen_heap.
From iris.proofmode Require Import tactics.

Section exchanger.
Context `{Countable L}.
Context `{hG1: !gen_heapGS L V Σ}.
Context `{hG2: !gen_heapGS L V Σ}.

Definition gen_heap_exchanger_key k v2 : iProp Σ :=
  ((∃ v1, mapsto (hG:=hG1) k (DfracOwn 1) v1) ∨ mapsto (hG:=hG2) k (DfracOwn 1) v2).

Definition gen_heap_exchanger (ma ma' : gmap L V) : iProp Σ :=
  gen_heap_interp (hG := hG1) ma ∗
  [∗ map] k↦va ∈ ma, ∃ va', ⌜ ma' !! k = Some va' ⌝ ∗ gen_heap_exchanger_key k va'.

Lemma gen_heap_exchanger_swap ma ma' k v :
  gen_heap_exchanger ma ma' -∗
  mapsto (hG := hG1) k (DfracOwn 1) v -∗
  gen_heap_exchanger ma ma' ∗ ∃ v', ⌜ ma !! k = Some v ∧ ma' !! k = Some v' ⌝ ∗
  mapsto (hG := hG2) k (DfracOwn 1) v'.
Proof.
  iIntros "(Hauth&Hexch) Hk".
  iDestruct (@gen_heap_valid with "[$] [$]") as %Hlook.
  iDestruct (big_sepM_lookup_acc with "[$]") as "(Hk_exch&Hexch)"; eauto.
  iDestruct "Hk_exch" as (va' Hlook') "Hk_exch".
  iDestruct "Hk_exch" as "[Htaken|Huntaken]".
  { iDestruct "Htaken" as (?) "Htaken".
    iDestruct (@mapsto_ne with "[$] [$]") as %Hval; eauto. congruence. }
  iDestruct ("Hexch" with "[Hk]") as "Hexch".
  { iExists _. iSplit; first eauto. iLeft. iExists _. by iFrame. }
  iFrame.
  iExists _. iFrame. eauto.
Qed.
End exchanger.

