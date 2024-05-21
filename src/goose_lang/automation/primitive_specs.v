From Perennial.goose_lang Require Import automation.goose_lang_auto.
From diaframe.lib Require Import iris_hints.
From Perennial.goose_lang Require Import struct.
From Perennial.goose_lang Require Import typed_mem.
From Perennial.goose_lang Require Import lock.

Set Default Proof Using "Type".

Section goose_lang_instances.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  Open Scope expr_scope.

  (*
  Below [HINT1] is a poor version of [automate_pure_exec] in [goose_lang_auto.v], modeled after the
  example in [diaframe/tuturiol/ex5_custom_proof_automation.v].
  Global Instance automate_let_in (e1 e2 : expr) (x : binder) (Φ : val → iProp Σ) :
    HINT1 ε₁ ✱ (** We use [ε₁] here as key hypothesis: only apply this rule if no other can be found. *)
      [WP e1 {{ v', ▷ WP (λ: x, e2)%V (of_val v') {{ Φ }} }} ]
      (** New goal: the same expression, but after applying [wp_bind], and doing one additional pure reduction. *)
      ⊫ [id];
      WP (let: x := e1 in e2) {{ Φ }} (** Goal: an expression that features a let binding *).
  Proof. iSteps as "HWP". wp_bind e1. iApply (wp_mono with "HWP"). iSteps. by wp_pure1. Qed.
  *)

  Global Instance ref_zero_spec t E :
    SPEC ⟨E⟩
        {{ ⌜has_zero t⌝ }}
          ref (zero_val t)
        {{ (l: loc), RET #l; l ↦[t] (zero_val t) }}.
  Proof.
    iSteps.
    wp_apply wp_ref_of_zero; auto.
  Qed.

  Global Instance ref_to_spec t v E :
    SPEC ⟨E⟩
        {{ ⌜val_ty v t⌝ }}
          ref_to t v
        {{ (l: loc), RET #l; l ↦[t] v }}.
  Proof.
    iSteps.
    wp_apply wp_ref_to; auto.
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

  Global Instance alloc_spec E e v t:
    IntoVal e v →
    val_ty v t →
    SPEC ⟨E⟩ {{ emp }} ref_to t e {{ l, RET #l; l ↦[t] v }} | 20.
  Proof.
    move => <- Hty.
    iStep.
    wp_apply wp_ref_to => //.
    iSteps.
  Qed.

  Global Instance struct_alloc_spec E d v :
      SPEC ⟨E⟩
        {{ ⌜val_ty v (struct.t d)⌝ }}
        struct.alloc d v
        {{ l, RET #l; l ↦[struct.t d] v }}.
  Proof.
    iSteps.
    wp_apply wp_allocStruct; [ done | ].
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
    SPEC ⟨E⟩ v, {{ ⌜val_ty v' t ⌝ ∗ ▷ l ↦[t] v }} #l <-[t] v' {{ RET #(); l ↦[t] v' }}.
  Proof.
    iSteps as (v Hty) "Hl".
    wp_apply (wp_StoreAt with "Hl"); first done.
    iSteps.
  Qed.

  Global Instance loadField_spec l d f E :
    SPEC ⟨E⟩ q v, {{ ▷ l ↦[d :: f]{q} v }}
                  struct.loadF d f #l
                {{ RET v; l ↦[d :: f]{q} v }}.
  Proof.
    iSteps. wp_loadField. iSteps.
  Qed.

  Global Instance storeField_spec l d f E fv' :
    SPEC ⟨E⟩ fv, {{ ⌜val_ty fv' (field_ty d f)⌝ ∗ ▷ l ↦[d :: f] fv }}
                  struct.storeF d f #l fv'
                {{ RET #(); l ↦[d :: f] fv' }}.
  Proof.
    iSteps as (v' ?) "Hx".
    wp_apply (wp_storeField with "Hx"); auto.
  Qed.

  Global Instance readonly_struct_field_hint l d f v E :
    (* Note that quantifier [q] is _before_ the semicolon!
      The goal resource of the HINT (in this case [l ↦[d::f]{q} v]) should always be an atom:
      ie not of the form [A ∗ B] or [∃ q, P q]. If the resource is existentially quantified,
      move all these quantifiers to before the semicolon. *)
    HINT (readonly (l ↦[d :: f] v)) ✱ [- ; emp] ⊫ [fupd E E] q; l ↦[d :: f]{q} v ✱ [emp] | 50.
  Proof.
    iSteps as "#Hf".
    iMod (readonly_load with "[$]") as "H".
    iSteps.
  Qed.

  (* Unfortunately, above HINT does not work when looking for [∃ q v, l ↦[d:: f]{q} v]. It would work for
    [∃ v q, l ↦[d:: f]{q} v], ie when the quantified variables are ordered differently. Diaframe is
    not currently smart enough to handle that *)

  (* To overcome that, we add this extra HINT: *)
  Global Instance readonly_struct_field_hint2 l d f v E :
    HINT (readonly (l ↦[d :: f] v)) ✱ [- ; emp] ⊫ [fupd E E] q v'; l ↦[d :: f]{q} v' ✱ [⌜v = v'⌝] | 50.
  Proof.
    iSteps as "#Hf".
    iMod (readonly_load with "[$]") as "H".
    iSteps.
  Qed.

End goose_lang_instances.

#[global] Typeclasses Opaque ref_to.
#[global] Opaque ref_to.
