From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import proph_map.
From iris.program_logic Require Export weakestpre adequacy.
From Perennial.algebra Require Import gen_heap.
From Perennial.goose_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Class ffi_interp_adequacy `{!ffi_interp ffi} `{EXT: !ext_semantics ext ffi} :=
  { ffi_preG: gFunctors -> Type;
    ffiΣ: gFunctors;
    (* modeled after subG_gen_heapPreG and gen_heap_init *)
    subG_ffiPreG : forall Σ, subG ffiΣ Σ -> ffi_preG Σ;
    ffi_update_pre: ∀ Σ, ffi_preG Σ -> ffi_names -> ffiG Σ;
    ffi_update_pre_update: ∀ Σ (hPre: ffi_preG Σ) names1 names2,
        ffi_update Σ (ffi_update_pre _ hPre names1) names2 =
        ffi_update_pre _ hPre names2;
    ffi_update_pre_get: ∀ Σ (hPre: ffi_preG Σ) names,
        ffi_get_names _ (ffi_update_pre _ hPre names) = names;
    ffi_name_init : forall Σ (hPre: ffi_preG Σ) (σ:ffi_state),
          (|==> ∃ (names: ffi_names), let H0 := ffi_update_pre _ hPre names in ffi_ctx H0 σ ∗ ffi_start H0 σ)%I;
    ffi_crash_rel: ∀ Σ, ffiG Σ → ffi_state → ffiG Σ → ffi_state → iProp Σ;
    ffi_crash : forall Σ,
          ∀ (σ σ': ffi_state) (CRASH: ext_crash σ σ') (Hold: ffiG Σ),
           (ffi_ctx Hold σ ==∗ ∃ (new: ffi_names), ffi_ctx (ffi_update Σ Hold new) σ' ∗
                                                  ffi_crash_rel Σ Hold σ (ffi_update Σ Hold new) σ' ∗
                                                  ffi_restart (ffi_update Σ Hold new) σ')%I;
  }.

(* this is the magic that lets subG_ffiPreG solve for an ffi_preG using only
typeclass resolution, which is the one thing solve_inG tries. *)
Existing Class ffi_preG.
Hint Resolve subG_ffiPreG : typeclass_instances.

Class heapPreG `{ext: ext_op} `{EXT_SEM: !ext_semantics ext ffi}
      `{INTERP: !ffi_interp ffi} {ADEQ: ffi_interp_adequacy} Σ
  := HeapPreG {
  heap_preG_iris :> invPreG Σ;
  heap_preG_heap :> gen_heapPreG loc (nonAtomic val) Σ;
  heap_preG_proph :> proph_mapPreG proph_id (val * val) Σ;
  heap_preG_ffi : ffi_preG Σ;
  heap_preG_trace :> trace_preG Σ;
}.

Definition heap_update_pre Σ `(hpreG : heapPreG Σ) (Hinv: invG Σ) (names: heap_names) :=
  {| heapG_invG := Hinv;
     heapG_ffiG := ffi_update_pre Σ (heap_preG_ffi) (heap_ffi_names names);
     heapG_gen_heapG := gen_heapG_update_pre (heap_preG_heap) (heap_heap_names names);
     heapG_proph_mapG :=
       {| proph_map_inG := proph_map_preG_inG;
          proph_map_name := (heap_proph_name names) |};
     heapG_traceG := traceG_update_pre Σ (heap_preG_trace) (heap_trace_names names)
 |}.

Lemma heap_update_pre_get Σ `(hpreG : heapPreG Σ) (Hinv: invG Σ) (names: heap_names) :
  heap_get_names _ (heap_update_pre Σ hpreG Hinv names) = names.
Proof.
  rewrite /heap_get_names/heap_update_pre ffi_update_pre_get gen_heapG_update_pre_get //=.
  destruct names => //=.
Qed.

Lemma heap_update_pre_update Σ `(hpreG : heapPreG Σ) (Hinv1 Hinv2: invG Σ) (names1 names2: heap_names) :
  heap_update _ (heap_update_pre Σ hpreG Hinv1 names1) Hinv2 names2 = (heap_update_pre Σ hpreG Hinv2 names2).
Proof.
  rewrite /heap_update ffi_update_pre_update/traceG_update/gen_heapG_update//=.
Qed.

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
  (∀ `{!heapG Σ}, ffi_start (heapG_ffiG) σ.(world) -∗
                  trace_frag σ.(trace) -∗ oracle_frag σ.(oracle) -∗
                  WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}%I) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??) "".
  iMod (gen_heap_init σ.(heap)) as (?) "Hh".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iMod (ffi_name_init _ _ σ.(world)) as (HffiG) "(Hw&Hstart)".
  iMod (trace_init σ.(trace) σ.(oracle)) as (HtraceG) "(Htr&?&Hor&?)".
  iModIntro. iExists
    (λ σ κs, (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id) ∗ ffi_ctx (ffi_update_pre _ _ HffiG) σ.(world) ∗ trace_auth σ.(trace) ∗ oracle_auth σ.(oracle))%I),
    (λ _, True%I).
  iFrame. by iApply (Hwp (HeapG _ _ _ _ _ HtraceG) with "[$] [$] [$]").
Qed.
