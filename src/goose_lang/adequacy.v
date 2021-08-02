From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.program_logic Require Export weakestpre.
From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import proofmode notation.
Set Default Proof Using "Type".

(** No actual adequacy theorem here, just definitions that are shared between
recovery_adequacy and (in the future) distrib_adequacy. *)

Class ffi_interp_adequacy `{FFI: !ffi_interp ffi} `{EXT: !ffi_semantics ext ffi} :=
  { ffi_preG: gFunctors -> Type;
    ffiΣ: gFunctors;
    (* modeled after subG_gen_heapPreG and gen_heap_init *)
    subG_ffiPreG : forall Σ, subG ffiΣ Σ -> ffi_preG Σ;
    ffi_initgP: ffi_global_state → Prop;
    ffi_initP: ffi_state → ffi_global_state → Prop;
    ffi_update_pre: ∀ Σ, ffi_preG Σ -> ffi_local_names -> ffi_global_names -> ffiG Σ;
    ffi_update_pre_update: ∀ Σ (hPre: ffi_preG Σ) names1 names2 namesg,
        ffi_update_local Σ (ffi_update_pre _ hPre names1 namesg) names2 =
        ffi_update_pre _ hPre names2 namesg;
    ffi_update_pre_get_local: ∀ Σ (hPre: ffi_preG Σ) names namesg,
        ffi_get_local_names _ (ffi_update_pre _ hPre names namesg) = names;
    ffi_update_pre_get_global: ∀ Σ (hPre: ffi_preG Σ) names namesg,
        ffi_get_global_names _ (ffi_update_pre _ hPre names namesg) = namesg;
    ffi_pre_global_start : forall Σ (hPre: ffi_preG Σ), ffi_global_names → global_state → iProp Σ;
    ffi_pre_global_ctx : forall Σ (hPre: ffi_preG Σ), ffi_global_names → global_state → iProp Σ;
    ffi_pre_global_ctx_spec :
      ∀ Σ hPre names namesg g,
        ffi_global_ctx (ffi_update_pre Σ hPre names namesg) g ≡
        ffi_pre_global_ctx Σ hPre namesg g;
    ffi_name_global_init : forall Σ (hPre: ffi_preG Σ) (g:ffi_global_state),
        ffi_initgP g →
          ⊢ |==> ∃ (namesg: ffi_global_names),
              ffi_pre_global_ctx Σ hPre namesg g ∗
              ffi_pre_global_start Σ hPre namesg g;
    ffi_name_init : forall Σ (hPre: ffi_preG Σ) (σ:ffi_state) (g:ffi_global_state) (namesg: ffi_global_names),
        ffi_initP σ g →
          ⊢ ffi_pre_global_ctx Σ hPre namesg g ==∗ ∃ (names: ffi_local_names),
              let H0 := ffi_update_pre _ hPre names namesg in
                   ffi_ctx H0 σ ∗ ffi_global_ctx H0 g ∗ ffi_local_start H0 σ g;
    ffi_crash : forall Σ,
          ∀ (σ σ': ffi_state) (g: ffi_global_state) (CRASH: ffi_crash_step σ σ') (Hold: ffiG Σ),
           ⊢ ffi_ctx Hold σ -∗ ffi_global_ctx Hold g ==∗
             ∃ (new: ffi_local_names), ffi_ctx (ffi_update_local Σ Hold new) σ' ∗
                                 ffi_global_ctx (ffi_update_local Σ Hold new) g ∗
                                 ffi_crash_rel Σ Hold σ (ffi_update_local Σ Hold new) σ' ∗
                                 ffi_restart (ffi_update_local Σ Hold new) σ';
  }.

(* this is the magic that lets subG_ffiPreG solve for an ffi_preG using only
typeclass resolution, which is the one thing solve_inG tries. *)
Existing Class ffi_preG.
Hint Resolve subG_ffiPreG : typeclass_instances.

Class heapGpreS `{ext: ffi_syntax} `{EXT_SEM: !ffi_semantics ext ffi}
      `{INTERP: !ffi_interp ffi} {ADEQ: ffi_interp_adequacy} Σ
  := HeapGpreS {
  heap_preG_iris :> invGpreS Σ;
  heap_preG_crash :> crashPreG Σ;
  heap_preG_heap :> na_heapPreG loc val Σ;
  heap_preG_ffi : ffi_preG Σ;
  heap_preG_trace :> trace_preG Σ;
  heap_preG_credit :> credit_preG Σ;
}.

Definition heap_update_pre Σ `(hpreG : heapGpreS Σ) (Hinv: invGS Σ) (Hcrash: crashG Σ) (names: heap_names) :=
  {| heapG_invG := Hinv;
     heapG_crashG := Hcrash;
     heapG_ffiG := ffi_update_pre Σ (heap_preG_ffi) (heap_ffi_local_names names) (heap_ffi_global_names names);
     heapG_na_heapG := na_heapG_update_pre (heap_preG_heap) (heap_heap_names names);
     heapG_traceG := traceG_update_pre Σ (heap_preG_trace) (heap_trace_names names);
     heapG_creditG := creditGS_update_pre Σ (heap_preG_credit) (heap_credit_names names)
 |}.

Lemma heap_update_pre_get Σ `(hpreG : heapGpreS Σ) (Hinv: invGS Σ) (Hcrash: crashG Σ) (names: heap_names) :
  heap_get_names _ (heap_update_pre Σ hpreG Hinv Hcrash names) = names.
Proof.
  rewrite /heap_get_names/heap_update_pre ffi_update_pre_get_local ffi_update_pre_get_global.
  rewrite  na_heapG_update_pre_get //=.
  destruct names => //=.
Qed.

(*
Lemma heap_update_pre_update Σ `(hpreG : heapGpreS Σ) (Hinv1 Hinv2: invGS Σ) (Hcrash1 Hcrash2: crashG Σ)
      (names1 names2: heap_names) :
  heap_update _ (heap_update_pre Σ hpreG Hinv1 Hcrash1 names2) Hinv2 Hcrash2 names2 =
  (heap_update_pre Σ hpreG Hinv2 Hcrash2 names2).
Proof.
  rewrite /heap_update/heap_update_pre ffi_update_pre_update/traceG_update/gen_heapG_update//=.
Qed.
*)

Hint Resolve heap_preG_ffi : typeclass_instances.

Ltac solve_inG_deep :=
  intros;
  (* XXX: had to add cases with more _'s compared to solve_inG to get this work *)
   lazymatch goal with
   | H:subG (?xΣ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _) _ |- _ => try unfold xΣ in H
   | H:subG ?xΣ _ |- _ => try unfold xΣ in H
   end; repeat match goal with
               | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
               end; repeat match goal with
                           | H:subG _ _ |- _ => move : H; apply subG_inG in H || clear H
                           end; intros; try done; split; assumption || by apply _.

Definition heapΣ `{ext: ffi_syntax} `{ffi_interp_adequacy} : gFunctors :=
  #[invΣ; crashΣ; na_heapΣ loc val; ffiΣ; traceΣ; creditΣ].
Instance subG_heapPreG `{ext: ffi_syntax} `{@ffi_interp_adequacy ffi Hinterp ext EXT} {Σ} :
  subG heapΣ Σ → heapGpreS Σ.
Proof.
  solve_inG_deep.
Qed.
