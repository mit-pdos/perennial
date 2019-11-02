From iris.proofmode Require Import tactics.
From iris.program_logic Require Export total_adequacy.
From Perennial.go_lang Require Export adequacy.
From Perennial.go_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Definition heap_total `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!ffi_interp_adequacy} Σ `{!heapPreG Σ} s e σ φ :
  (∀ `{!heapG Σ}, WP e @ s; ⊤ [{ v, ⌜φ v⌝ }]%I) →
  sn erased_step ([e], σ).
Proof.
  intros Hwp; eapply (twp_total _ _); iIntros (?) "".
  iMod (gen_heap_init σ.(heap)) as (?) "Hh".
  iMod (proph_map_init [] σ.(used_proph_id)) as (?) "Hp".
  iMod (ffi_init _ _ σ.(world)) as (HffiG) "Hw".
  iModIntro.
  iExists
    (λ σ κs _, (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id) ∗ ffi_ctx HffiG σ.(world))%I),
    (λ _, True%I); iFrame.
  iApply (Hwp (HeapG _ _ _ _ _)).
Qed.
