From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map frac_count big_op.
From Perennial.goose_lang Require Import proofmode notation wpc_proofmode.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy spec_assert language_ctx.
From Perennial.goose_lang Require Import typing typed_translate adequacy refinement.
From Perennial.goose_lang Require Export recovery_adequacy spec_assert refinement_adequacy.
From Perennial.goose_lang Require Import metatheory crash_borrow.
From Perennial.goose_lang.lib Require Import list.
From Perennial.Helpers Require Import Qextra.
From Perennial.Helpers Require List.

Set Default Proof Using "Type".

Section reln.
Context {ext: ffi_syntax}.
Context {ffi: ffi_model}.
Context {ffi_semantics: ffi_semantics ext ffi}.
Context `{interp: !ffi_interp ffi}.
Context `{interp_adeq: !ffi_interp_adequacy}.
Context (impl_ty: ext_types ext).

Context {spec_ext: spec_ffi_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{spec_interp: @spec_ffi_interp spec_ffi}.
Context `{spec_adeq: !spec_ffi_interp_adequacy}.
Context {spec_ty: ext_types (@spec_ffi_op_field spec_ext)}.

Notation sstate := (@state (@spec_ffi_op_field spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ffi_op_field spec_ext)).
Notation sval := (@val (@spec_ffi_op_field spec_ext)).
Notation istate := (@state ext).
Notation iexpr := (@expr ext).
Notation ival := (@val ext).
Notation sty := (@ty (@val_tys _ spec_ty)).
Notation SCtx := (@Ctx (@val_tys _ spec_ty)).

Definition val_semTy `{!heapGS Σ} `{refinement_heapG Σ} := sval → ival → iProp Σ.

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
    sty_inv : ∀ {Σ} `{!heapGS Σ} `{!refinement_heapG Σ}, styG Σ → iProp Σ;
    sty_init : ∀ {Σ} `{!heapGS Σ} `{!refinement_heapG Σ}, styG Σ → iProp Σ;
    sty_crash_cond : ∀ {Σ} `{!heapGS Σ} `{!refinement_heapG Σ}, styG Σ → iProp Σ;
    sty_crash_tok : ∀ {Σ} `{!heapGS Σ} `{!refinement_heapG Σ}, iProp Σ;
    sty_crash_tok_excl : ∀ {Σ} `{!heapGS Σ} `{!refinement_heapG Σ},
        sty_crash_tok -∗ sty_crash_tok -∗ False;
    sty_crash_tok_timeless : ∀ {Σ} `{!heapGS Σ} `{!refinement_heapG Σ}, Timeless sty_crash_tok;
    styN: coPset;
    styN_disjoint : ↑ sN ## styN;
    sty_val_interp : ∀ {Σ} `{!heapGS Σ} `{!refinement_heapG Σ} (hS: styG Σ),
                     @ext_tys (@val_tys (@spec_ffi_op_field spec_ext) spec_ty) → val_semTy;
    sty_val_persistent:
      forall Σ `(hG: !heapGS Σ) `(hRG: !refinement_heapG Σ) (hG': heapGS Σ) (hS: styG Σ) τ es e,
        Persistent (sty_val_interp hS τ es e);
    sty_val_flatten:
      forall Σ `(hG: !heapGS Σ) `(hRG: !refinement_heapG Σ) (hG': heapGS Σ) (hS: styG Σ) τ vs v,
        sty_val_interp hS τ vs v -∗
        ⌜ flatten_struct vs = [vs] ∧ flatten_struct v = [v] ⌝;
    sty_lvl_init: nat;
    sty_lvl_ops: nat;
    sty_inv_persistent:
      forall Σ `(hG: !heapGS Σ) `(hRG: !refinement_heapG Σ) (hG': heapGS Σ) (hS: styG Σ),
        Persistent (sty_inv hS) }.

Section reln_defs.
Context `{hG: !heapGS Σ}.
Context {hRG: refinement_heapG Σ}.
Context `{hS: @styG smodel Σ}.


Existing Instances spec_ffi_model_field (* spec_ffi_op_field *) spec_ext_semantics_field (* spec_ffi_interp_field  *) spec_ffi_interp_adequacy_field.

Definition has_semTy (es: sexpr) (e: iexpr) (vty: val_semTy) : iProp Σ :=
  (∀ (j: nat) (K: sexpr → sexpr) (CTX: LanguageCtx K),
      j ⤇ K es -∗ WPC e @ sty_lvl_ops; ⊤ {{ v, ∃ vs, j ⤇ K (of_val vs)
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

Definition loc_inv γ (ls: loc) (l: loc) (vTy: val_semTy) :=
   (∃ vs v, (fc_auth γ None ∗ ls s↦ vs ∗ l ↦ v ∗ vTy vs v) ∨
            (∃ q q' (n: positive), ⌜ (q + q' = 1)%Qp ⌝ ∗
                fc_auth γ (Some (q, n)) ∗
                na_heap_mapsto_st (RSt (Pos.to_nat n)) ls q' vs ∗
                (∀ v', na_heap_mapsto (hG := refinement_na_heapG) ls 1 v' -∗ ls s↦ v') ∗
                l ↦{q'} v ∗ vTy vs v)
            ∨
            (fc_auth γ (Some ((1/2)%Qp, 1%positive)) ∗
             na_heap_mapsto_st WSt ls (1/2)%Qp vs))%I.

Definition locN := nroot.@"loc".

Definition rlN := nroot.@"reln".@"eq".

Definition loc_paired ls l :=
  (meta (hG := refinement_na_heapG) ls rlN l ∗
   meta (hG := heapG_na_heapG) l rlN ls)%I.

Definition is_loc ls l vTy :=
  ((∃ γ, inv locN (loc_inv γ ls l vTy)) ∗ loc_paired ls l)%I.

Definition prodT_interp (t1 t2: sty) val_interp : sval → ival → iProp Σ :=
  λ vs v, (∃ v1 v2 vs1 vs2, ⌜ v = (v1, v2)%V ∧ vs = (vs1, vs2)%V⌝
                   ∗ val_interp t1 vs1 v1
                   ∗ val_interp t2 vs2 v2)%I.

Fixpoint listT_interp_aux (val_interp : sval → ival → iProp Σ)
         (lvs : list sval) (lv : list ival) : iProp Σ :=
  (match lvs, lv with
  | nil, nil => True%I
  | vs :: lvs, v :: lv =>
    val_interp vs v ∗ listT_interp_aux val_interp lvs lv
  | _, _ => False%I
  end)%I.

Definition listT_interp (t: sty) (val_interp : sty → sval → ival → iProp Σ) : sval → ival → iProp Σ :=
  λ vs v, (∃ lvs lv, ⌜ vs = val_of_list lvs ∧ v = val_of_list lv ⌝ ∗ listT_interp_aux (val_interp t) lvs lv)%I.

Definition sumT_interp (t1 t2: sty) val_interp : sval → ival → iProp Σ :=
  λ vs v, ((∃ v' vs', ⌜ v = InjLV v' ∧
                                vs = InjLV vs'⌝
                              ∗ val_interp t1 vs' v')
                     ∨
                   (∃ v' vs', ⌜ v = InjRV v' ∧
                                vs = InjRV vs'⌝
                              ∗ val_interp t2 vs' v'))%I.

Definition arrayT_interp (t: sty) (val_list_interp: sty → list (sval → ival → iProp Σ)) : sval → ival → iProp Σ :=
  λ vs v, ((∃ l ls (n: nat) (idx: Z) (Hnz: (0 < n)%nat) (Hnonempty: flatten_ty t ≠ []),
                     ⌜ vs = LitV $ LitLoc ls ∧ v = LitV $ LitLoc l ∧ addr_base ls ≠ null ∧ addr_base l ≠ null ∧
                     addr_offset l = (idx * length (flatten_ty t))%Z ∧
                     addr_offset ls = (idx * length (flatten_ty t))%Z ⌝ ∗
                     (na_block_size (hG := refinement_na_heapG) (addr_base ls) (n * length (flatten_ty t))) ∗
                     (na_block_size (hG := heapG_na_heapG) (addr_base l) (n * length (flatten_ty t))) ∗
                     [∗ list] i ∈ seq 0 n,
                     [∗ list] j↦vty ∈ (val_list_interp t),
                         is_loc (addr_base ls +ₗ (length (flatten_ty t) * Z.of_nat i) +ₗ j)
                                (addr_base l +ₗ (length (flatten_ty t) * Z.of_nat i) +ₗ j)
                                vty)
                 ∨ (∃ off, ⌜ vs = #(null +ₗ off) ∧ v = #(null +ₗ off) ⌝))%I.

Definition structRefT_interp (ts: list (sval → ival → iProp Σ)) (* (val_list_interp: sty → list (sval → ival → iProp Σ) *) :
  sval → ival → iProp Σ :=
  λ vs v, ((∃ l ls (n: nat) (Hnz: (0 < n)%nat) (Hnonempty: ts ≠ []),
                     ⌜ vs = LitV $ LitLoc ls ∧ v = LitV $ LitLoc l ∧ addr_base ls ≠ null ∧ addr_base l ≠ null ∧
                       addr_offset l = addr_offset ls⌝ ∗
                       loc_paired (addr_base ls) (addr_base l) ∗
                     (na_block_size (hG := refinement_na_heapG) (addr_base ls) n) ∗
                     (na_block_size (hG := heapG_na_heapG) (addr_base l) n) ∗
                     (([∗ list] j↦vty ∈ (ts),
                       is_loc (ls +ₗ j) (l +ₗ j) vty)
                       ∨
                      ⌜addr_offset l + length ts ≤ 0 ∨ n ≤ addr_offset l⌝))
                 ∨ (∃ off, ⌜ vs = #(null +ₗ off) ∧ v = #(null +ₗ off) ⌝))%I.

Definition arrowT_interp (t1 t2: sty) (val_interp: sty → sval → ival → iProp Σ) : sval → ival → iProp Σ :=
  λ vs v,
    (∃ f x e fs xs es,
        ⌜ v = RecV f x e ∧
          vs = RecV fs xs es ⌝
        ∗ □ (∀ varg vsarg,
              val_interp t1 vsarg varg -∗
              has_semTy (App vs vsarg) (App v varg) (val_interp t2)))%I.

Fixpoint val_interp (t: sty) {struct t} :=
  match t with
  | baseT bt => base_ty_interp bt
  | prodT t1 t2 => prodT_interp t1 t2 val_interp
  | listT t => listT_interp t val_interp
  | sumT t1 t2 => sumT_interp t1 t2 val_interp
  | arrayT t => arrayT_interp t flatten_val_interp
  | arrowT t1 t2 => arrowT_interp t1 t2 val_interp
  | extT x => sty_val_interp hS x
  | mapValT vt => λ _ _, False%I
  | structRefT ts => structRefT_interp (map val_interp ts)
  end with
 flatten_val_interp (t: sty) {struct t} : list (sval → ival → iProp Σ) :=
    match t with
    | prodT t1 t2 => flatten_val_interp t1 ++ flatten_val_interp t2
    | listT t => [listT_interp t val_interp]
    | baseT unitBT => []
    | baseT ty => [base_ty_interp ty]
    | sumT t1 t2 => [sumT_interp t1 t2 val_interp]
    | arrayT t => [arrayT_interp t flatten_val_interp]
    | arrowT t1 t2 => [arrowT_interp t1 t2 val_interp]
    | extT x => [sty_val_interp hS x]
    | mapValT vt => [λ _ _, False%I]
    | structRefT ts => [structRefT_interp (map val_interp ts)]
    end.

Lemma flatten_val_interp_flatten_ty t:
  flatten_val_interp t = map val_interp (flatten_ty t).
Proof.
  induction t => //=.
  - destruct t; eauto.
  - rewrite map_app IHt1 IHt2 //.
Qed.

Lemma val_interp_list_unfold t:
  val_interp (listT t) = listT_interp t (val_interp).
Proof. rewrite //=. Qed.

Lemma val_interp_array_unfold t:
  val_interp (arrayT t) = arrayT_interp t (λ t, map val_interp (flatten_ty t)).
Proof. rewrite //= /arrayT_interp flatten_val_interp_flatten_ty //=. Qed.

Lemma val_interp_struct_unfold ts:
  val_interp (structRefT ts) = structRefT_interp (map val_interp ts).
Proof. rewrite //= flatten_val_interp_flatten_ty //=. Qed.

End reln_defs.

Class specTy_update `(hsT_model: !specTy_model) :=
  { sty_preG : gFunctors → Type;
    styΣ: gFunctors;
    subG_styPreG : forall Σ, subG styΣ Σ -> sty_preG Σ;
    sty_update_pre: ∀ Σ, sty_preG Σ -> sty_names -> styG Σ;
    sty_update_pre_update: ∀ Σ (hPre: sty_preG Σ) names1 names2,
        sty_update Σ (sty_update_pre _ hPre names1) names2 =
        sty_update_pre _ hPre names2;
    sty_update_pre_get: ∀ Σ (hPre: sty_preG Σ) names,
        sty_get_names _ (sty_update_pre _ hPre names) = names;
  }.

Section reln_obligations.

Context `{hsT_model: !specTy_model} (spec_trans: sval → ival → Prop).
Context (spec_atomic_transTy : SCtx → sexpr → iexpr → sty → sexpr → iexpr → sty → Prop).

Existing Instances spec_ffi_model_field spec_ffi_op_field spec_ext_semantics_field spec_ffi_interp_field spec_ffi_interp_adequacy_field.


Context (upd: specTy_update hsT_model).

Definition sty_init_obligation1 (sty_initP: istate → sstate → Prop) :=
      forall Σ `(hG: !heapGS Σ) `(hRG: !refinement_heapG Σ) (hPre: sty_preG Σ) σs gs σ g
      (HINIT: sty_initP σ σs),
        ⊢ ffi_local_start (heapG_ffiG) σ.(world) g -∗
         ffi_local_start (refinement_spec_ffiG) σs.(world) gs -∗
         pre_borrowN (sty_lvl_init) -∗
         |={styN}=> ∃ (names: sty_names), let H0 := sty_update_pre _ hPre names in sty_init H0.

Definition sty_init_obligation2 (sty_initP: istate → sstate → Prop) :=
  ∀ σ g σs gs, sty_initP σ σs → null_non_alloc σs.(heap) ∧ ffi_initP σ.(world) g ∧ ffi_initP σs.(world) gs ∧
                                ffi_initgP g ∧ ffi_initgP gs.

Definition sty_crash_obligation :=
  forall Σ `(hG: !heapGS Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ),
      ⊢ sty_inv hS -∗ ▷ sty_crash_cond hS -∗ |sty_lvl_init={styN}=> ▷ ∀ (hG': heapGS Σ), |={⊤}=>
      ∀ σs,
      (∃ σ0 σ1, ffi_restart (heapG_ffiG) σ1.(world) ∗
      ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ0.(world) (heapG_ffiG (hG := hG')) σ1.(world)) -∗
      ffi_ctx (refinement_spec_ffiG) σs.(world) -∗
      ∃ (σs': sstate) (HCRASH: crash_prim_step (spec_crash_lang) σs σs'),
      ffi_ctx (refinement_spec_ffiG) σs.(world) ∗
      ∀ (hRG': refinement_heapG Σ),
      ffi_crash_rel Σ (refinement_spec_ffiG (hRG := hRG)) σs.(world)
                      (refinement_spec_ffiG (hRG := hRG')) σs'.(world) -∗
      ffi_restart (refinement_spec_ffiG) σs'.(world) -∗
      pre_borrowN (sty_lvl_init) -∗
      |={styN}=> ∃ (new: sty_names), sty_init (sty_update Σ hS new).

Definition sty_rules_obligation :=
  ∀ (es: sval) (vs: sval) e v t1 t2,
    get_ext_tys es (t1, t2) →
    spec_trans es e →
    forall Σ `(hG: !heapGS Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ) ,
    sty_inv hS -∗
    spec_ctx -∗
    val_interp (hS := hS) t1 vs v -∗
    has_semTy (es vs) (e v) (val_interp (hS := hS) t2).

Definition sty_crash_inv_obligation :=
  (forall Σ `(hG: !heapGS Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ),
    ⊢ sty_init hS -∗
    spec_ctx -∗
    spec_crash_ctx (sty_crash_tok) -∗
    |={⊤}=> init_cancel (sty_inv hS) (sty_crash_cond hS ∗ sty_crash_tok)).
(*
    WPC e @ sty_lvl_init; ⊤ {{ Φ }} {{ sty_crash_cond hS ∗ sty_crash_tok }}).
 *)

Record subst_tuple :=
  { subst_ty : sty ; subst_sval : sval; subst_ival: ival }.
Definition subst_ctx := gmap string subst_tuple.

Definition sty_atomic_obligation :=
  forall Σ `(hG: !heapGS Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ)
         el1 el2 tl e1 e2 t (Γsubst: gmap string subst_tuple),
  (spec_atomic_transTy (subst_ty <$> Γsubst) el1 el2 tl e1 e2 (sumT unitT t)) ->
  sty_inv hS -∗
  spec_ctx -∗
  trace_ctx -∗
  ([∗ map] t0 ∈ Γsubst, val_interp (hS:=hS) (subst_ty t0) (subst_sval t0) (subst_ival t0)) -∗
  has_semTy (subst_map (subst_sval <$> Γsubst) el1) (subst_map (subst_ival <$> Γsubst) el2)
    (val_interp (hS := hS) tl) -∗
  has_semTy (subst_map (subst_sval <$> Γsubst) (Atomically el1 e1)) (subst_map (subst_ival <$> Γsubst) e2)
    (val_interp (hS := hS) (sumT unitT t)).

Definition ctx_has_semTy `{hG: !heapGS Σ} `{hRG: !refinement_heapG Σ} {hS: styG Σ}
           (Γ: Ctx) es e τ : iProp Σ :=
  ∀ Γsubst (HPROJ: subst_ty <$> Γsubst = Γ),
  sty_inv hS -∗
  spec_ctx -∗
  trace_ctx -∗
  ([∗ map] x ↦ t ∈ Γsubst, (val_interp (hS := hS) (subst_ty t) (subst_sval t) (subst_ival t))) -∗
  has_semTy (subst_map (subst_sval <$> Γsubst) es)
            (subst_map (subst_ival <$> Γsubst) e)
            (val_interp (hS := hS) τ).

Global Instance base_interp_pers Σ es e t:
      Persistent (base_ty_interp (Σ := Σ) t es e).
Proof. destruct t; apply _. Qed.

Instance listT_interp_aux_pers `{hG: !heapGS Σ} `{hRG: !refinement_heapG Σ} ls l
       (vTy: sval → ival → iProp Σ) :
       (∀ es' e', Persistent (vTy es' e')) →
       Persistent (listT_interp_aux vTy ls l).
Proof.
  intros ?. revert l. induction ls; destruct l => //=; apply _.
Qed.

Instance listT_interp_pers `{hG: !heapGS Σ} `{hRG: !refinement_heapG Σ} {hS: styG Σ} es e t
       (vTy: sty → sval → ival → iProp Σ) :
       (∀ t' es' e', Persistent (vTy t' es' e')) →
       Persistent (listT_interp t vTy es e).
Proof.
  intros. rewrite /listT_interp. apply _.
Qed.

Global Instance val_interp_pers `{hG: !heapGS Σ} `{hRG: !refinement_heapG Σ} {hS: styG Σ} es e t:
      Persistent (val_interp (hS := hS) t es e).
Proof.
 revert es e. induction t => ?? //=; try apply _.
 by apply sty_val_persistent.
Qed.

Global Instance sty_ctx_prop_pers `{hG: !heapGS Σ} `{hRG: !refinement_heapG Σ} {hS: styG Σ}
      (Γsubst: gmap string subst_tuple) :
      Persistent ([∗ map] t ∈ Γsubst, val_interp (hS := hS) (subst_ty t) (subst_sval t) (subst_ival t))%I.
Proof.
  apply big_sepM_persistent => ??. by apply val_interp_pers.
Qed.

End reln_obligations.

Existing Instances sty_inv_persistent.
End reln.

Arguments val_interp {ext ffi ffi_semantics interp spec_ext spec_ffi spec_ffi_semantics spec_interp _ Σ hG hRG
  smodel hS} _%heap_type (_ _)%val_scope.

Arguments ctx_has_semTy {ext ffi ffi_semantics interp spec_ext spec_ffi spec_ffi_semantics spec_interp _
  hsT_model Σ hG hRG hS} _ (_ _)%expr_scope _%heap_type.

Arguments specTy_model {ext ffi interp spec_ext spec_ffi spec_ffi_semantics spec_interp} spec_ty.
