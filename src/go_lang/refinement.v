From iris.algebra Require Import auth frac agree gmap list excl.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export language.
From iris.program_logic Require Import lifting.
From Perennial.program_logic Require Import refinement.
From Perennial.go_lang Require Export lang.
From Perennial.go_lang Require Import tactics notation map lifting.

(* Wrapper around ffi_models and so on to avoid clashes between the ffi for
   the spec and the concrete *)

Class spec_ffi_model := { spec_ffi_model_field : ffi_model }.
Class spec_ext_op := { spec_ext_op_field : ext_op }.
Class spec_ext_semantics (H1: spec_ext_op) (H2: spec_ffi_model) :=
  { spec_ext_semantics_field : ext_semantics (spec_ext_op_field) (spec_ffi_model_field) }.
Class spec_ffi_interp (spec_ffi: spec_ffi_model) :=
  { spec_ffi_interp_field : ffi_interp (spec_ffi_model_field) }.

Section go_refinement.
Context {spec_ext: spec_ext_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{!spec_ffi_interp spec_ffi}.
Canonical Structure spec_lang : language :=
  @heap_lang (spec_ext_op_field) (spec_ffi_model_field) (spec_ext_semantics_field).

Existing Instance spec_ffi_interp_field.
Existing Instance spec_ext_semantics_field.
Existing Instance spec_ext_op_field.
Existing Instance spec_ffi_model_field.


Class refinement_heapG Σ := refinement_HeapG {
  refinement_spec_ffiG : ffiG Σ;
  refinement_traceG :> traceG Σ;
  refinement_cfgG :> @cfgG spec_lang Σ;
  refinement_gen_heapG :> gen_heapG loc (nonAtomic (@val spec_ext_op_field)) Σ;
  (* TODO: do we need prophecies at the spec level? *)
  (*
  refinement_proph_mapG :> proph_mapG proph_id (val * val) Σ;
   *)
}.

Context {Σ: gFunctors}.
Context {hR: refinement_heapG Σ}.
Context `{invG Σ}.

Definition spec_interp σ : iProp Σ :=
    (gen_heap_ctx σ.(heap) ∗ (* proph_map_ctx κs σ.(used_proph_id) ∗ *) ffi_ctx refinement_spec_ffiG σ.(world)
      ∗ trace_auth σ.(trace))%I.

Definition spec_stateN := nroot .@ "source".@  "state".

(* TODO: these names are terrible *)
Definition spec_ctx : iProp Σ :=
  source_ctx ∗ inv spec_stateN (∃ σ, source_state σ ∗ spec_interp σ)%I.

Global Instance spec_ctx_persistent : Persistent (spec_ctx).
Proof. apply _. Qed.

(** Override the notations so that scopes and coercions work out *)
Notation "l s↦{ q } v" := (mapsto (L:=loc) (V:=nonAtomic val) (hG := refinement_heapG) l q v%V)
  (at level 20, q at level 50, format "l  s↦{ q }  v") : bi_scope.
Notation "l s↦ v" :=
  (mapsto (L:=loc) (V:=nonAtomic val) (hG := refinement_heapG) l 1 v%V) (at level 20) : bi_scope.
Notation "l s↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  s↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

Section go_ghost_step.

Lemma sourceN_sub_minus_state E:
  nclose sourceN_root ⊆ E →
  nclose sourceN ⊆ E ∖ ↑spec_stateN.
Proof.
  rewrite /sourceN/sourceN_root/spec_stateN. intros Hsub.
  assert (nclose (nroot.@"source".@"base") ##
                 ↑nroot.@"source".@"state").
  { solve_ndisj. }
  assert (nclose (nroot.@"source".@"base") ⊆ E).
  { etransitivity; last eassumption. apply nclose_subseteq. }
  set_solver.
Qed.

Hint Resolve sourceN_sub_minus_state.

Lemma ghost_load j K E l q v:
  nclose sourceN_root ⊆ E →
  spec_ctx -∗
  l ↦{q} Free v -∗
  j ⤇ fill K (Load (Val $ LitV $ LitLoc l)) ={E}=∗
  l ↦{q} Free v ∗ j ⤇ fill K v.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { eapply head_prim_step; econstructor; eauto. }
  { eauto. }
  iMod ("Hclo" with "[Hσ H Hrest]").
  { iNext. iExists _. iFrame. }
  iFrame. eauto.
Qed.

End go_ghost_step.

End go_refinement.
