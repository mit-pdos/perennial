From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
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

End gen_heap_defs.

