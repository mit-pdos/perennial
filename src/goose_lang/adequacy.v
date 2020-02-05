From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import proph_map.
From iris.program_logic Require Export weakestpre adequacy.
From Perennial.goose_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Class ffi_interp_adequacy `{!ffi_interp ffi} `{EXT: !ext_semantics ext ffi} :=
  { ffi_preG: gFunctors -> Type;
    ffiΣ: gFunctors;
    (* modeled after subG_gen_heapPreG and gen_heap_init *)
    subG_ffiPreG : forall Σ, subG ffiΣ Σ -> ffi_preG Σ;
    ffi_init : forall Σ, ffi_preG Σ -> forall (σ:ffi_state),
          (|==> ∃ (H0: ffiG Σ), ffi_ctx H0 σ)%I;
    ffi_crash_rel: ∀ Σ, ffiG Σ → ffi_state → ffiG Σ → ffi_state → iProp Σ;
    ffi_crash : forall Σ, ffi_preG Σ ->
          (∀ (σ σ': ffi_state) (CRASH: ext_crash σ σ') (Hold: ffiG Σ),
           ffi_ctx Hold σ ==∗ ∃ (new: ffi_names), ffi_ctx (ffi_update Σ Hold new) σ' ∗
                                                  ffi_crash_rel Σ Hold σ (ffi_update Σ Hold new) σ')%I;
  }.

(* this is the magic that lets subG_ffiPreG solve for an ffi_preG using only
typeclass resolution, which is the one thing solve_inG tries. *)
Existing Class ffi_preG.
Hint Resolve subG_ffiPreG : typeclass_instances.

Class heapPreG `{ext: ext_op} `{ffi_interp_adequacy} Σ := HeapPreG {
  heap_preG_iris :> invPreG Σ;
  heap_preG_heap :> gen_heapPreG loc (nonAtomic val) Σ;
  heap_preG_proph :> proph_mapPreG proph_id (val * val) Σ;
  heap_preG_ffi : ffi_preG Σ;
  heap_preG_trace :> trace_preG Σ;
}.

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

Definition heapΣ `{ext: ext_op} `{ffi_interp_adequacy} : gFunctors := #[invΣ; gen_heapΣ loc (nonAtomic val); ffiΣ; proph_mapΣ proph_id (val * val); traceΣ].
Instance subG_heapPreG `{ext: ext_op} `{@ffi_interp_adequacy ffi Hinterp ext EXT} {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof.
  solve_inG_deep.
Qed.

Definition heap_adequacy `{ffi_sem: ext_semantics} `{!ffi_interp ffi} {Hffi_adequacy:ffi_interp_adequacy} Σ `{!heapPreG Σ} s e σ φ :
  (∀ `{!heapG Σ}, trace_frag σ.(trace) -∗ oracle_frag σ.(oracle) -∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}%I) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??) "".
  iMod (gen_heap_init σ.(heap)) as (?) "Hh".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iMod (ffi_init _ _ σ.(world)) as (HffiG) "Hw".
  iMod (trace_init σ.(trace) σ.(oracle)) as (HtraceG) "(Htr&?&Hor&?)".
  iModIntro. iExists
    (λ σ κs, (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id) ∗ ffi_ctx HffiG σ.(world) ∗ trace_auth σ.(trace) ∗ oracle_auth σ.(oracle))%I),
    (λ _, True%I).
  iFrame. by iApply (Hwp (HeapG _ _ HffiG _ _ _ HtraceG) with "[$] [$]").
Qed.
