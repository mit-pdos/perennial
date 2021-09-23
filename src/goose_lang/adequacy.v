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
  { ffiΣ: gFunctors;
    ffiGpreS: gFunctors -> Type;
    (* modeled after subG_gen_heapPreG and gen_heap_init *)
    subG_ffiPreG : forall Σ, subG ffiΣ Σ -> ffiGpreS Σ;
    ffi_initgP: ffi_global_state → Prop;
    (* Valid local starting states may depend on whatever the current global state is. *)
    ffi_initP: ffi_state → ffi_global_state → Prop;
    ffi_global_init : forall Σ (hPre: ffiGpreS Σ) (g:ffi_global_state),
        ffi_initgP g →
          ⊢ |==> ∃ (hG: ffiGlobalGS Σ),
              ffi_global_ctx hG g ∗ ffi_global_start hG g;
    ffi_local_init : forall Σ (hPre: ffiGpreS Σ) (σ:ffi_state) (g:ffi_global_state),
        ffi_initP σ g →
          ⊢ |==> ∃ (hL: ffiLocalGS Σ),
                   ffi_local_ctx hL σ ∗ ffi_local_start hL σ;
    ffi_crash : forall Σ,
          ∀ (σ σ': ffi_state) (CRASH: ffi_crash_step σ σ') (Hold: ffiLocalGS Σ),
           ⊢ ffi_local_ctx Hold σ ==∗
             ∃ (Hnew: ffiLocalGS Σ), ffi_local_ctx Hnew σ' ∗
                                 ffi_crash_rel Σ Hold σ Hnew σ' ∗
                                 ffi_restart Hnew σ';
  }.

(* this is the magic that lets subG_ffiPreG solve for an ffiGpreS using only
typeclass resolution, which is the one thing solve_inG tries. *)
Existing Class ffiGpreS.
Hint Resolve subG_ffiPreG : typeclass_instances.

Class gooseGpreS `{ext: ffi_syntax} `{EXT_SEM: !ffi_semantics ext ffi}
      `{INTERP: !ffi_interp ffi} `{!ffi_interp_adequacy} Σ
  := GooseGpreS {
  goose_preG_iris :> invGpreS Σ;
  goose_preG_crash :> crashGpreS Σ;
  goose_preG_heap :> na_heapGpreS loc val Σ;
  goose_preG_ffi :> ffiGpreS Σ;
  goose_preG_trace :> trace_preG Σ;
  goose_preG_credit :> credit_preG Σ;
}.

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
  subG heapΣ Σ → gooseGpreS Σ.
Proof.
  solve_inG_deep.
Qed.
