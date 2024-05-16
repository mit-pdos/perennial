From Perennial.goose_lang Require Import automation.goose_lang_auto.
From diaframe.lib Require Import iris_hints.
From Perennial.goose_lang Require Import struct.struct.
From Perennial.goose_lang Require Import typed_mem.typed_mem.

Set Default Proof Using "Type".

Section goose_lang_instances.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  Open Scope expr_scope.

  Global Instance ref_zero_spec t Φ :
    HINT1 ε₀ ✱
      [⌜has_zero t⌝ ∗ ▷ (∀ (l:loc), l ↦[t] (zero_val t) -∗ Φ #l)]
      ⊫ [id]; WP (ref (zero_val t)) {{ Φ }}.
  Proof.
    iSteps.
    wp_apply wp_ref_of_zero; auto.
  Qed.

  Global Instance load_primitive_spec E l :
    SPEC ⟨E⟩ v q, {{ ▷ l ↦{q} v }} ! #l {{ RET v; l ↦{q} v }}.
  Proof.
    iSteps as (v q) "Hl".
    wp_apply (wp_load with "Hl").
    iSteps.
  Qed.

  Global Instance load_at_spec l E t :
    SPEC ⟨E⟩ v q, {{ ▷ l ↦[t]{q} v }} ![t] #l {{ RET v; l ↦[t]{q} v }}.
  Proof.
    iSteps as (v q) "Hl".
    wp_apply (wp_LoadAt with "Hl").
    iSteps.
  Qed.

  Global Instance alloc_spec e v t:
    IntoVal e v →
    val_ty v t →
    SPEC {{ True }} ref_to t e {{ l, RET #l; l ↦[t] v }} | 20.
  Proof.
    move => <- Hty.
    iStep.
    (* TODO: using perennial_spec_red_no_Φ_not_value made this break, should I
    be concerned? *)
    wp_apply wp_ref_to => //.
    iSteps.
  Qed.

  Global Instance store_primitive_spec l v' E :
    SPEC ⟨E⟩ v, {{ ▷ l ↦ v }} #l <- v' {{ RET #(); l ↦ v' }}.
  Proof.
    iSteps as (v) "Hl".
    iApply (wp_store with "Hl").
    iSteps.
  Qed.

  Global Instance store_at_spec l t v' E :
    val_ty v' t →
    SPEC ⟨E⟩ v, {{ ▷ l ↦[t] v }} #l <-[t] v' {{ RET #(); l ↦[t] v' }}.
  Proof.
    move => Hty.
    iSteps as (v) "Hl".
    wp_apply (wp_StoreAt with "Hl"); first done.
    iSteps.
  Qed.

End goose_lang_instances.
