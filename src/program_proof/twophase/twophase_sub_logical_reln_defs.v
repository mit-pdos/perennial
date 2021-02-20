From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import proph_map.
From iris.program_logic Require Export weakestpre adequacy.
From Perennial.algebra Require Import proph_map frac_count big_op.
From Perennial.goose_lang Require Import proofmode notation wpc_proofmode.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy spec_assert language_ctx.
From Perennial.goose_lang Require Import typing typed_translate adequacy refinement.
From Perennial.goose_lang Require Export recovery_adequacy spec_assert refinement_adequacy.
From Perennial.goose_lang Require Import metatheory.
From Perennial.goose_lang.lib Require Import list.
From Perennial.Helpers Require Import Qextra.
From Perennial.Helpers Require List.

From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang.ffi Require Import disk.
From Perennial.program_proof Require Import twophase.twophase_refinement.

Set Default Proof Using "Type".

Section reln.

  (* Records for the target language *)
  Notation ext := disk_op.
  Notation ffi := ffi_model.
  Notation ffi_semantics := (ext_semantics ext ffi).
  Notation interp := (ffi_interp ffi).
  Notation interp_adeq := (ffi_interp ffi).
  Notation impl_ty := (ext_types ext).

Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp jrnl_spec_interp_adequacy.

  (* Records defining spec language extensions *)
  Notation spec_ext := jrnl_spec_ext.
  Notation spec_ffi := jrnl_spec_ffi_model.
  Notation spec_ffi_semantics := jrnl_spec_ext_semantics.
  Notation spec_interp := jrnl_spec_ffi_interp.
  Notation spec_ty := jrnl_ty.
  Notation spec_adeq := jrnl_spec_interp_adequacy.


  (*
  Notation sexpr := (@expr spec_ext).
  Notation sval := (@val spec_ext).
*)
  Notation iexpr := (@expr ext).
  Notation ival := (@val ext).
  (*
  Notation sty := (@ty (@val_tys _ spec_ty)).
  Notation SCtx := (@Ctx (@val_tys _ spec_ty)).
   *)

Notation sstate := (@state (@spec_ext_op_field spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ext_op_field spec_ext)).
Notation sval := (@val (@spec_ext_op_field spec_ext)).
Notation istate := (@state ext).
Notation sty := (@ty (@val_tys _ spec_ty)).
Notation SCtx := (@Ctx (@val_tys _ spec_ty)).

Definition val_semTy `{!heapG Σ} `{refinement_heapG Σ} := sval → ival → iProp Σ.

Section reln_defs.
Context `{hG: !heapG Σ}.
Context {hRG: refinement_heapG Σ}.
Context (SIZE: nat).


Existing Instances spec_ffi_model_field (* spec_ext_op_field *) spec_ext_semantics_field (* spec_ffi_interp_field  *) spec_ffi_interp_adequacy_field.

(* XXX: Replace j ↦ K es with an always_steps + the non-persistent resourceses accumulated by
   twophase ops *)
Definition atomically_has_semTy (es: sexpr) (e: iexpr) (vty: val_semTy) : iProp Σ :=
  (∀ (j: nat) (K: sexpr → sexpr) (CTX: LanguageCtx K),
      j ⤇ K es -∗ WPC e @ (logical_reln_defns.sty_lvl_ops (specTy_model := jrnlTy_model SIZE)); ⊤
                    {{ v, ∃ vs, j ⤇ K (of_val vs) ∗ vty vs v }} {{ True }})%I.

Definition atomically_base_ty_interp (t: base_ty) :=
  λ (v1: sval) (v2: ival),
  match t with
    | uint64BT => (∃ x, ⌜ v1 = LitV $ LitInt x ∧ v2 = LitV $ LitInt x ⌝ : iProp Σ)%I
    | uint32BT => (∃ x, ⌜ v1 = LitV $ LitInt32 x ∧ v2 = LitV $ LitInt32 x ⌝ : iProp Σ)%I
    | byteBT => (∃ x, ⌜ v1 = LitV $ LitByte x ∧ v2 = LitV $ LitByte x ⌝ : iProp Σ)%I
    | boolBT => (∃ x, ⌜ v1 = LitV $ LitBool x ∧ v2 = LitV $ LitBool x ⌝ : iProp Σ)%I
    | unitBT => (⌜ v1 = LitV $ LitUnit ∧ v2 = LitV $ LitUnit ⌝ : iProp Σ)%I
    | stringBT => (∃ x, ⌜ v1 = LitV $ LitString x ∧ v2 = LitV $ LitString x ⌝ : iProp Σ)%I
  end.

Definition atomically_prodT_interp (t1 t2: sty) val_interp : sval → ival → iProp Σ :=
  λ vs v, (∃ v1 v2 vs1 vs2, ⌜ v = (v1, v2)%V ∧ vs = (vs1, vs2)%V⌝
                   ∗ val_interp t1 vs1 v1
                   ∗ val_interp t2 vs2 v2)%I.

Fixpoint atomically_listT_interp_aux (val_interp : sval → ival → iProp Σ)
         (lvs : list sval) (lv : list ival) : iProp Σ :=
  (match lvs, lv with
  | nil, nil => True%I
  | vs :: lvs, v :: lv =>
    val_interp vs v ∗ atomically_listT_interp_aux val_interp lvs lv
  | _, _ => False%I
  end)%I.

Definition atomically_listT_interp (t: sty) (val_interp : sty → sval → ival → iProp Σ) : sval → ival → iProp Σ :=
  λ vs v, (∃ lvs lv, ⌜ vs = val_of_list lvs ∧ v = val_of_list lv ⌝ ∗ atomically_listT_interp_aux (val_interp t) lvs lv)%I.

Definition atomically_sumT_interp (t1 t2: sty) val_interp : sval → ival → iProp Σ :=
  λ vs v, ((∃ v' vs', ⌜ v = InjLV v' ∧
                                vs = InjLV vs'⌝
                              ∗ val_interp t1 vs' v')
                     ∨
                   (∃ v' vs', ⌜ v = InjRV v' ∧
                                vs = InjRV vs'⌝
                              ∗ val_interp t2 vs' v'))%I.

Definition atomically_arrowT_interp (t1 t2: sty) (val_interp: sty → sval → ival → iProp Σ) :
  sval → ival → iProp Σ :=
  λ vs v,
    (∃ f x e fs xs es,
        ⌜ v = RecV f x e ∧
          vs = RecV fs xs es ⌝
        ∗ □ (∀ varg vsarg,
              val_interp t1 vsarg varg -∗
              atomically_has_semTy (App vs vsarg) (App v varg) (val_interp t2)))%I.

Fixpoint atomically_val_interp (t: sty) {struct t} :=
  match t with
  | baseT bt => atomically_base_ty_interp bt
  | prodT t1 t2 => atomically_prodT_interp t1 t2 atomically_val_interp
  | listT t => atomically_listT_interp t atomically_val_interp
  | sumT t1 t2 => atomically_sumT_interp t1 t2 atomically_val_interp
  | arrowT t1 t2 => atomically_arrowT_interp t1 t2 atomically_val_interp
  | _ => λ _ _, False%I
  end.

Lemma atomically_val_interp_list_unfold t:
  atomically_val_interp (listT t) = atomically_listT_interp t (atomically_val_interp).
Proof. rewrite //=. Qed.

Record subst_tuple :=
  { subst_ty : sty ; subst_sval : sval; subst_ival: ival }.
Definition subst_ctx := gmap string subst_tuple.

Definition ctx_has_semTy `{hG: !heapG Σ} `{hRG: !refinement_heapG Σ}
           (Γ: Ctx) es e τ : iProp Σ :=
  ∀ Γsubst (HPROJ: subst_ty <$> Γsubst = Γ),
  spec_ctx -∗
  ([∗ map] x ↦ t ∈ Γsubst, (atomically_val_interp (subst_ty t) (subst_sval t) (subst_ival t))) -∗
  atomically_has_semTy (subst_map (subst_sval <$> Γsubst) es)
            (subst_map (subst_ival <$> Γsubst) e)
            (atomically_val_interp τ).

Global Instance base_interp_pers es e t:
      Persistent (atomically_base_ty_interp t es e).
Proof. destruct t; apply _. Qed.

Instance atomically_listT_interp_aux_pers ls l
       (vTy: sval → ival → iProp Σ) :
       (∀ es' e', Persistent (vTy es' e')) →
       Persistent (atomically_listT_interp_aux vTy ls l).
Proof. intros ?. revert l. induction ls; destruct l => //=; apply _. Qed.

Instance atomically_listT_interp_pers  es e t
       (vTy: sty → sval → ival → iProp Σ) :
       (∀ t' es' e', Persistent (vTy t' es' e')) →
       Persistent (atomically_listT_interp t vTy es e).
Proof. intros. rewrite /atomically_listT_interp. apply _. Qed.

Global Instance atomically_val_interp_pers es e t:
      Persistent (atomically_val_interp t es e).
Proof. revert es e. induction t => ?? //=; try apply _. Qed.

Global Instance sty_ctx_prop_pers (Γsubst: gmap string subst_tuple) :
      Persistent ([∗ map] t ∈ Γsubst, atomically_val_interp (subst_ty t) (subst_sval t) (subst_ival t))%I.
Proof.
  apply big_sepM_persistent => ??. apply atomically_val_interp_pers.
Qed.

End reln_defs.

(*
Arguments val_interp {ext ffi ffi_semantics interp spec_ext spec_ffi spec_ffi_semantics spec_interp _ Σ hG hRG
  smodel hS} _%heap_type (_ _)%val_scope.

Arguments ctx_has_semTy {ext ffi ffi_semantics interp spec_ext spec_ffi spec_ffi_semantics spec_interp _
  hsT_model Σ hG hRG hS} _ (_ _)%expr_scope _%heap_type.

Arguments specTy_model {ext ffi interp spec_ext spec_ffi spec_ffi_semantics spec_interp} spec_ty.
*)
End reln.
