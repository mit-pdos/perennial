From iris.algebra Require Import auth gmap frac agree.
Require Export CSL.WeakestPre CSL.Lifting CSL.Adequacy CSL.RefinementAdequacy CSL.RefinementIdempotenceModule.
From iris.algebra Require Export functions.
From iris.base_logic.lib Require Export invariants gen_heap.
From iris.proofmode Require Export tactics.
Require Export ExMach.ExMachAPI ExMach.WeakestPre.

Class exmachPreG Σ := ExMachPreG {
  exm_preG_iris :> invPreG Σ;
  exm_preG_mem :> gen_heapPreG nat nat Σ;
  exm_preG_disk :> gen_heapPreG nat nat Σ;
  exm_preG_treg_inG :> inG Σ (csumR countingR (authR (optionUR (exclR unitC))));
}.

Definition exmachΣ : gFunctors := #[invΣ; gen_heapΣ nat nat; gen_heapΣ nat nat;
                                    GFunctor (csumR countingR (authR (optionUR (exclR unitC))))].
Instance subG_exmachPreG {Σ} : subG exmachΣ Σ → exmachPreG Σ.
Proof. solve_inG. Qed.

Import ExMach.
