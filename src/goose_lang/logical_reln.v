From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import proph_map.
From iris.program_logic Require Export weakestpre adequacy.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy spec_assert.
From Perennial.goose_lang Require Import typing adequacy refinement.
From Perennial.goose_lang Require Export recovery_adequacy spec_assert refinement_adequacy.

Set Default Proof Using "Type".

Section reln.
Context {ext: ext_op}.
Context {ffi: ffi_model}.
Context {ffi_semantics: ext_semantics ext ffi}.
Context `{interp: !ffi_interp ffi}.
Context `{interp_adeq: !ffi_interp_adequacy}.
Context (impl_ty: ext_types ext).

Context {spec_ext: spec_ext_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{spec_interp: @spec_ffi_interp spec_ffi}.
Context `{spec_adeq: !spec_ffi_interp_adequacy}.
Context (spec_ty: ext_types (@spec_ext_op_field spec_ext)).

Context {MAX: nat}.

Notation sstate := (@state (@spec_ext_op_field spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ext_op_field spec_ext)).
Notation sval := (@val (@spec_ext_op_field spec_ext)).
Notation istate := (@state ext).
Notation iexpr := (@expr ext).
Notation ival := (@val ext).
Notation sty := (@ty (@val_tys _ spec_ty)).

Definition val_semTy `{!heapG Σ} `{refinement_heapG Σ} `{crashG Σ} := sval → ival → iProp Σ.

Class specTy_model :=
  { styG : gFunctors → Set;
    sty_names : Set;
    sty_get_names : ∀ Σ : gFunctors, styG Σ → sty_names;
    sty_update : ∀ Σ : gFunctors, styG Σ → sty_names → styG Σ;
    sty_update_get : ∀ (Σ : gFunctors) (hF : styG Σ) (names : sty_names),
                       sty_get_names Σ (sty_update Σ hF names) = names;
    sty_get_update : ∀ (Σ : gFunctors) (hF : styG Σ), sty_update Σ hF (sty_get_names Σ hF) = hF;
    sty_update_update : ∀ (Σ : gFunctors) (hF : styG Σ) (names1 names2 : sty_names),
                          sty_update Σ (sty_update Σ hF names1) names2 = sty_update Σ hF names2;
    sty_inv : ∀ {Σ} `{!heapG Σ} `{refinement_heapG} `{crashG Σ}, styG Σ → iProp Σ;
    sty_val_interp : ∀ {Σ} `{!heapG Σ} `{refinement_heapG Σ} `{crashG Σ} (hS: styG Σ),
                     @ext_tys (@val_tys _ spec_ty) → val_semTy }.

(*
Context `{Hhpre: @heapPreG ext ffi ffi_semantics interp _ Σ}.
Context `{Hcpre: @cfgPreG spec_lang Σ}.
Context `{Hrpre: @refinement_heapPreG spec_ext spec_ffi spec_interp _ spec_adeq Σ}.
*)

Section reln_defs.
Context `{hG: !heapG Σ}.
Context {hRG: refinement_heapG Σ}.
Context {hC: crashG Σ}.
Context `{hS: @styG smodel Σ}.


Existing Instances spec_ffi_model_field (* spec_ext_op_field *) spec_ext_semantics_field (* spec_ffi_interp_field  *) (* spec_ffi_interp_adequacy_field *).

Definition has_semTy (es: sexpr) (e: iexpr) (vty: val_semTy) : iProp Σ :=
  (∀ (j: nat) (K: sexpr → sexpr) (CTX: LanguageCtx K),
      j ⤇ K es -∗ WPC e @ NotStuck; MAX; ⊤; (⊤ ∖ ↑sN) {{ v, ∃ vs, j ⤇ K (of_val vs)
                                                                    ∗ vty vs v }}
                                                      {{ True }})%I.

Definition base_ty_interp (t: base_ty) :=
  λ (v1: sval) (v2: ival),
  match t with
    | uint64BT => (∃ x, ⌜ v1 = LitV $ LitInt x ∧ v2 = LitV $ LitInt x ⌝ : iProp Σ)%I
    | uint32BT => (∃ x, ⌜ v1 = LitV $ LitInt32 x ∧ v2 = LitV $ LitInt32 x ⌝ : iProp Σ)%I
    | byteBT => (∃ x, ⌜ v1 = LitV $ LitByte x ∧ v2 = LitV $ LitByte x ⌝ : iProp Σ)%I
    | boolBT => (∃ x, ⌜ v1 = LitV $ LitBool x ∧ v2 = LitV $ LitBool x ⌝ : iProp Σ)%I
    | unitBT => (⌜ v1 = LitV $ LitUnit ∧ v2 = LitV $ LitUnit ⌝ : iProp Σ)%I
    | stringBT => (∃ x, ⌜ v1 = LitV $ LitString x ∧ v2 = LitV $ LitString x ⌝ : iProp Σ)%I
  end.

Inductive loc_status :=
| loc_readable
| loc_writing.
Canonical Structure loc_statusO := leibnizO loc_status.

Context `{!inG Σ (authR (optionUR (exclR loc_statusO)))}.

Definition loc_inv (ls: loc) (l: loc) (vTy: val_semTy) :=
  (∃ (stat: loc_status),
    match stat with
    | loc_readable => ∃ q vs v, vTy vs v ∗ ls s↦{q} vs ∗ l ↦{q} v
    | loc_writing => ∃ vs, na_heap_mapsto_st WSt ls 1 vs
   end)%I.

Definition locN := nroot.@"loc".

Definition is_loc ls l vTy :=
  inv locN (loc_inv ls l vTy).

Fixpoint val_interp (t: sty) (vs: sval) (v: ival) :=
  match t with
  | baseT bt => base_ty_interp bt vs v
  | prodT t1 t2 => (∃ v1 v2 vs1 vs2, ⌜ v = (v1, v2)%V ∧
                                       vs = (vs1, vs2)%V⌝
                   ∗ val_interp t1 vs1 v1
                   ∗ val_interp t2 vs2 v2)%I
  | sumT t1 t2 => ((∃ v' vs', ⌜ v = InjLV v' ∧
                                vs = InjLV vs'⌝
                              ∗ val_interp t1 vs' v')
                     ∨
                   (∃ v' vs', ⌜ v = InjRV v' ∧
                                vs = InjRV vs'⌝
                              ∗ val_interp t2 vs' v'))%I
  | arrayT t => ((∃ l ls (indices: list unit),
                     ⌜ vs = LitV $ LitLoc ls ∧ v = LitV $ LitLoc l ⌝ ∗
                     [∗ list] i↦_ ∈ indices, is_loc (ls +ₗ i) (l +ₗ i) (val_interp t))
                 ∨ (⌜ vs = #null ∧ v = #null⌝))%I
  | arrowT t1 t2 =>
    (∃ f x e fs xs es,
        ⌜ v = RecV f x e ∧
          vs = RecV fs xs es ⌝
        ∗ □ (∀ varg vsarg,
              val_interp t1 vsarg varg -∗
              has_semTy (App vs vsarg) (App v varg) (val_interp t2)))%I
  | extT x => sty_val_interp hS x vs v
  | mapValT vt => False%I
  | structRefT ts => False%I
  end.

End reln_defs.


Class specTy_model_adequacy `{!specTy_model} (spec_op_trans: @external (spec_ext_op_field) → iexpr)
      `{!ffi_interp_adequacy (FFI := spec_ffi_interp_field)
                             (EXT := (spec_ffi_semantics_field spec_ffi_semantics))} :=
  { sty_preG : gFunctors → Type;
    styΣ: gFunctors;
    subG_styPreG : forall Σ, subG styΣ Σ -> sty_preG Σ;
    sty_initP : sstate → istate → Prop;
    sty_update_pre: ∀ Σ, sty_preG Σ -> sty_names -> styG Σ;
    sty_update_pre_update: ∀ Σ (hPre: sty_preG Σ) names1 names2,
        sty_update Σ (sty_update_pre _ hPre names1) names2 =
        sty_update_pre _ hPre names2;
    sty_update_pre_get: ∀ Σ (hPre: sty_preG Σ) names,
        sty_get_names _ (sty_update_pre _ hPre names) = names;
    styN: coPset;
    sty_init :
      forall Σ `(hG: !heapG Σ) `(hRG: !refinement_heapG Σ) `(hC: crashG Σ) (hPre: sty_preG Σ) σs σ
      (HINIT: sty_initP σs σ),
        (ffi_start (heapG_ffiG) σ.(world) -∗
         ffi_start (refinement_spec_ffiG) σs.(world) -∗
         |={styN}=> ∃ (names: sty_names), let H0 := sty_update_pre _ hPre names in sty_inv H0)%I;
    sty_crash :
       forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ),
           (sty_inv hS ={styN, ∅}=∗
           ∀ (hC': crashG Σ) σs,
           (∃ σ0 σ1, ffi_restart (heapG_ffiG) σ1.(world) ∗
           ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ0.(world) (heapG_ffiG (hG := hG')) σ1.(world)) -∗
           ffi_ctx (refinement_spec_ffiG) σs.(world) -∗
           ∃ (σs': sstate) (HCRASH: crash_prim_step (spec_crash_lang) σs σs'),
           ffi_ctx (refinement_spec_ffiG) σs.(world) ∗
           ∀ (hRG': refinement_heapG Σ),
           ffi_crash_rel Σ (refinement_spec_ffiG (hRG := hRG)) σs.(world)
                           (refinement_spec_ffiG (hRG := hRG')) σs'.(world) -∗
           ffi_restart (refinement_spec_ffiG) σs'.(world) -∗
           |={styN}=> ∃ (new: sty_names), sty_inv (sty_update Σ hS new))%I;
    sty_rules_sound :
      ∀ op (es: sexpr) e t1 t2,
        get_ext_tys op = (t1, t2) →
        forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ),
        sty_inv hS -∗
        has_semTy es e (val_interp (hS := hS) t1) -∗
        has_semTy (ExternalOp op es) ((spec_op_trans) op e) (val_interp (hS := hS) t2)
}.

End reln.
