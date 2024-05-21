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

  (* [struct_fields] with f excluded *)
  Local Fixpoint struct_big_fields_except_rec l q (d: descriptor) (fs:descriptor) (f_rem: string) (v:val): iProp Σ :=
    match fs with
    | [] => "_" ∷ ⌜v = #()⌝
    | cons (f, t) fs =>
        match v with
        | PairV v1 v2 =>
          if (f =? f_rem)%string then
            struct.struct_big_fields_rec l q d fs v2
          else
            f ∷ struct_field_pointsto l q d f v1 ∗
            struct_big_fields_except_rec l q d fs f_rem v2
        | _ => False
        end
    end%core%I.

  Lemma bi_sep_false_l {PROP: bi} (P: PROP) : False ∗ P ⊣⊢ False.
  Proof.
    iSplit.
    - iIntros "[% _]"; contradiction.
    - iIntros "%"; contradiction.
  Qed.

  Lemma bi_sep_false_r {PROP: bi} (P: PROP) : P ∗ False ⊣⊢ False.
  Proof. rewrite (comm bi_sep) bi_sep_false_l //. Qed.

  Local Lemma struct_big_fields_except_rec_split l q d fs v f_rem :
    (∃ (i: nat), fs.*1 !! i = Some f_rem)%core%type →
    struct.struct_big_fields_rec l q d fs v ⊣⊢
        struct_big_fields_except_rec l q d fs f_rem v ∗
        l ↦[d :: f_rem]{q} (getField_f fs f_rem v).
  Proof.
    generalize dependent v.
    induction fs as [|[f t] fs']; simpl.
    - intros v Hrem_ex. destruct Hrem_ex as [i Hlookup].
      rewrite lookup_nil in Hlookup. congruence.
    - intros v Hrem_ex. destruct v; rewrite ?bi_sep_false_l //.
      destruct (String.eqb_spec f f_rem); subst.
      + (* this is the right field *)
        iSplit; iIntros "[$ $]".
      + rewrite -assoc.
        f_equiv.
        rewrite IHfs' //.
        destruct Hrem_ex as [i Hlookup].
        destruct i.
        { exfalso.
          simpl in Hlookup; inversion Hlookup; congruence. }
        exists i.
        simpl in Hlookup; auto.
  Qed.

  Local Lemma struct_big_fields_except_missing l q d fs v f_rem :
    f_rem ∉ fs.*1 →
    struct_big_fields_except_rec l q d fs f_rem v ⊣⊢
    struct.struct_big_fields_rec l q d fs v.
  Proof.
    generalize dependent v.
    induction fs as [|[f t] fs']; simpl; intros v Hnotin.
    - auto.
    - destruct v; auto.
      destruct (String.eqb_spec f f_rem); subst.
      + contradiction Hnotin. apply elem_of_list_here.
      + rewrite IHfs' //.
        apply not_elem_of_cons in Hnotin; intuition auto.
  Qed.

  (* [struct_fields_except_split] fully characterizes this definition *)
  Definition struct_fields_except l q d f_rem v : iProp Σ :=
    struct_big_fields_except_rec l q d d f_rem v.

  Lemma field_offset_none_not_in fs f_rem:
    f_rem ∉ fs.*1 → field_offset fs f_rem = None.
  Proof.
    intros Hnotin.
    induction fs as [|[f t] fs']; simpl; auto.
    destruct (String.eqb_spec f f_rem); subst.
    - contradiction Hnotin.
      simpl; apply elem_of_list_here.
    - rewrite IHfs' //.
      apply not_elem_of_cons in Hnotin; intuition auto.
  Qed.

  (* note that if f_rem is not actually in the struct, this lemma still holds.
  The field points-to fact becomes a trivial statement ⌜#() = #()⌝, and
  [struct_fields_except] is actually the entire struct. *)
  Lemma struct_fields_except_split f_rem l q d v :
    struct_fields l q d v ⊣⊢
      struct_fields_except l q d f_rem v ∗ l ↦[d :: f_rem]{q} (getField_f d f_rem v).
  Proof.
    rewrite /struct_fields_except /struct_fields.
    destruct (list_exist_dec (λ x, x = f_rem)%type d.*1).
    { tc_solve. }
    - rewrite struct_big_fields_except_rec_split //.
      destruct e as [? [Helem%elem_of_list_lookup ->]].
      intuition eauto.
    - assert (f_rem ∉ d.*1).
      { intuition eauto. }
      assert (field_offset d f_rem = None).
      { eauto using field_offset_none_not_in. }
      rewrite struct_big_fields_except_missing //.
      rewrite struct_field_pointsto_none' //.
      assert (getField_f d f_rem v = #()).
      { apply getField_f_none; auto. }
      iSplit.
      + iIntros "$ //".
      + iIntros "[$ _]".
  Qed.

  Global Instance struct_pointsto_get_field l q d v f fv :
    struct.wf d →
    HINT (l ↦[struct.t d]{q} v) ✱ [-; ⌜fv = getField_f d f v⌝] ⊫
      [id]; (l ↦[d :: f]{q} fv) ✱ [struct_fields_except l q d f v].
  Proof.
    intros Hwf.
    rewrite struct_fields_split.
    rewrite (struct_fields_except_split f).
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
