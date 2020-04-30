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

Context {LVL_INIT: nat}.
Context {LVL_OPS: nat}.

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
    sty_inv : ∀ {Σ} `{!heapG Σ} `{!refinement_heapG Σ} `{crashG Σ}, styG Σ → iProp Σ;
    sty_init : ∀ {Σ} `{!heapG Σ} `{!refinement_heapG Σ} `{crashG Σ}, styG Σ → iProp Σ;
    sty_crash_cond : ∀ {Σ} `{!heapG Σ} `{!refinement_heapG Σ} `{crashG Σ}, styG Σ → iProp Σ;
    styN: coPset;
    styN_disjoint : ↑ sN ## styN;
    sty_val_interp : ∀ {Σ} `{!heapG Σ} `{!refinement_heapG Σ} `{crashG Σ} (hS: styG Σ),
                     @ext_tys (@val_tys (@spec_ext_op_field spec_ext) spec_ty) → val_semTy;
    sty_val_persistent:
      forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ) τ es e,
        Persistent (sty_val_interp hS τ es e);
    sty_val_flatten:
      forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ) τ vs v,
        sty_val_interp hS τ vs v -∗
        ⌜ flatten_struct vs = [vs] ∧ flatten_struct v = [v] ⌝;
    (*
    sty_val_size:
      forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ) τ vs v,
        sty_val_interp hS τ vs v -∗
        ⌜ length (flatten_struct vs) = 1%nat ∧
          length (flatten_struct v) = 1%nat ⌝;
    *)
    sty_inv_persistent:
      forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ),
        Persistent (sty_inv hS) }.

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


Existing Instances spec_ffi_model_field (* spec_ext_op_field *) spec_ext_semantics_field (* spec_ffi_interp_field  *) spec_ffi_interp_adequacy_field.

Definition has_semTy (es: sexpr) (e: iexpr) (vty: val_semTy) : iProp Σ :=
  (∀ (j: nat) (K: sexpr → sexpr) (CTX: LanguageCtx K),
      j ⤇ K es -∗ WPC e @ NotStuck; LVL_OPS; ⊤; (⊤ ∖ ↑sN ∖ styN) {{ v, ∃ vs, j ⤇ K (of_val vs)
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
                na_heap_mapsto_st (RSt (Pos.to_nat n)) ls q vs ∗
                l ↦{q} v ∗ vTy vs v)
            ∨
            (fc_auth γ (Some ((1/2)%Qp, 1%positive)) ∗
             na_heap_mapsto_st WSt ls (1/2)%Qp vs))%I.

Definition locN := nroot.@"loc".

Definition rlN := nroot.@"reln".@"eq".

Definition loc_paired ls l :=
  (meta (hG := refinement_na_heapG) ls rlN l ∗
   meta (hG := heapG_na_heapG) l rlN ls)%I.

Lemma loc_paired_eq_iff ls l ls' l':
  loc_paired ls l -∗
  loc_paired ls' l' -∗
  ⌜ l = l' ↔ ls = ls' ⌝.
Proof.
  iIntros "(#Hmls&#Hml) (#Hmls'&#Hml')".
  destruct (decide (ls = ls')).
  { subst. iDestruct (meta_agree with "Hmls Hmls'") as %Heq.
    eauto. }
  destruct (decide (l = l')).
  { subst. iDestruct (meta_agree with "Hml Hml'") as %Heq.
    eauto. }
  eauto.
Qed.

Lemma loc_paired_base_eq_iff ls l ls' l':
  addr_offset l = addr_offset ls →
  addr_offset l' = addr_offset ls' →
  loc_paired (addr_base ls) (addr_base l) -∗
  loc_paired (addr_base ls') (addr_base l') -∗
  ⌜ l = l' ↔ ls = ls' ⌝.
Proof.
  iIntros (??) "(#Hmls&#Hml) (#Hmls'&#Hml')".
  destruct (decide (ls = ls')).
  { subst. iDestruct (meta_agree with "Hmls Hmls'") as %Heq.
    iPureIntro.
    apply addr_base_and_offset_eq_iff; eauto; split; eauto.
  }
  destruct (decide (l = l')).
  { subst. iDestruct (meta_agree with "Hml Hml'") as %Heq.
    iPureIntro.
    apply addr_base_and_offset_eq_iff; eauto; split; eauto.
  }
  eauto.
Qed.

Definition is_loc ls l vTy :=
  ((∃ γ, inv locN (loc_inv γ ls l vTy)) ∗ loc_paired ls l)%I.

Lemma is_loc_loc_paired ls l vTy:
  is_loc ls l vTy -∗ loc_paired ls l.
Proof. iIntros "(?&$)". Qed.

Lemma is_loc_eq_iff ls l ls' l' vTy vTy':
  is_loc ls l vTy -∗
  is_loc ls' l' vTy' -∗
  ⌜ l = l' ↔ ls = ls' ⌝.
Proof.
  iIntros "(?&H1) (?&H2)".
  iApply (loc_paired_eq_iff with "H1 H2").
Qed.

Lemma litv_loc_eq_iff (ls l ls' l': loc):
  (l = l' ↔ ls = ls') →
  ((#l : ival) = #l' ↔ (#ls: sval) = #ls').
Proof.
  intros Heq.
  split; inversion 1; subst; do 2 f_equal; eapply Heq; auto.
Qed.

Definition prodT_interp (t1 t2: sty) val_interp : sval → ival → iProp Σ :=
  λ vs v, (∃ v1 v2 vs1 vs2, ⌜ v = (v1, v2)%V ∧ vs = (vs1, vs2)%V⌝
                   ∗ val_interp t1 vs1 v1
                   ∗ val_interp t2 vs2 v2)%I.

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
                      ⌜addr_offset l < 0 ∨ n ≤ addr_offset l⌝))
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

Section reln_adeq.

Context `{hsT_model: !specTy_model} (spec_trans: sval → ival → Prop).

Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field spec_ffi_interp_field spec_ffi_interp_adequacy_field.

Context (upd: specTy_update hsT_model).

Definition sty_init_obligation1 (sty_initP: istate → sstate → Prop) :=
      forall Σ `(hG: !heapG Σ) `(hRG: !refinement_heapG Σ) `(hC: crashG Σ) (hPre: sty_preG Σ) σs σ
      (HINIT: sty_initP σ σs),
        ⊢ ffi_start (heapG_ffiG) σ.(world) -∗
         ffi_start (refinement_spec_ffiG) σs.(world) -∗
         |={styN}=> ∃ (names: sty_names), let H0 := sty_update_pre _ hPre names in sty_init H0.

Definition sty_init_obligation2 (sty_initP: istate → sstate → Prop) :=
  ∀ σ σs, sty_initP σ σs → null_non_alloc σs.(heap) ∧ ffi_initP σ.(world) ∧ ffi_initP σs.(world).

Definition sty_crash_obligation :=
  forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ),
      ⊢ sty_inv hS -∗ sty_crash_cond hS ={styN, ∅}=∗ ▷ ∀ (hG': heapG Σ), |={⊤}=>
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
      |={styN}=> ∃ (new: sty_names), sty_init (sty_update Σ hS new).

Definition sty_rules_obligation :=
  ∀ (es: sval) (vs: sval) e v t1 t2,
    get_ext_tys es (t1, t2) →
    spec_trans es e →
    forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ),
    sty_inv hS -∗
    spec_ctx -∗
    val_interp (hS := hS) t1 vs v -∗
    has_semTy (es vs) (e v) (val_interp (hS := hS) t2).

Definition sty_crash_inv_obligation :=
  (forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ)
     e (Φ: ival → iProp Σ),
    ⊢ sty_init hS -∗
    spec_ctx -∗
    (sty_inv hS -∗ (WPC e @ NotStuck; LVL_OPS; ⊤; (⊤ ∖ ↑sN ∖ styN) {{ Φ }} {{ True%I }})) -∗
    |={⊤}=> sty_inv hS ∗
    WPC e @ NotStuck; LVL_INIT; ⊤; (⊤ ∖ ↑sN ∖ styN) {{ Φ }} {{ sty_crash_cond hS }}).

Record subst_tuple :=
  { subst_ty : sty ; subst_sval : sval; subst_ival: ival }.
Definition subst_ctx := gmap string subst_tuple.

Definition ctx_has_semTy `{hG: !heapG Σ} `{hC: !crashG Σ} `{hRG: !refinement_heapG Σ} {hS: styG Σ}
           (Γ: Ctx) es e τ : iProp Σ :=
  ∀ Γsubst (HPROJ: subst_ty <$> Γsubst = Γ),
  sty_inv hS -∗
  spec_ctx -∗
  trace_ctx -∗
  ([∗ map] x ↦ t ∈ Γsubst, (val_interp (hS := hS) (subst_ty t) (subst_sval t) (subst_ival t))) -∗
  has_semTy (subst_map (subst_sval <$> Γsubst) es)
            (subst_map (subst_ival <$> Γsubst) e)
            (val_interp (hS := hS) τ).

Instance base_interp_pers Σ es e t:
      Persistent (base_ty_interp (Σ := Σ) t es e).
Proof. destruct t; apply _. Qed.

Instance val_interp_pers `{hG: !heapG Σ} `{hC: !crashG Σ} `{hRG: !refinement_heapG Σ} {hS: styG Σ} es e t:
      Persistent (val_interp (hS := hS) t es e).
Proof.
 revert es e. induction t => ?? //=; try apply _.
 by apply sty_val_persistent.
Qed.

Instance sty_ctx_prop_pers `{hG: !heapG Σ} `{hC: !crashG Σ} `{hRG: !refinement_heapG Σ} {hS: styG Σ}
      (Γsubst: gmap string subst_tuple) :
      Persistent ([∗ map] t ∈ Γsubst, val_interp (hS := hS) (subst_ty t) (subst_sval t) (subst_ival t))%I.
Proof.
  apply big_sepM_persistent => ??. by apply val_interp_pers.
Qed.

Existing Instances sty_inv_persistent.

Lemma arrayT_structRefT_promote vs v t:
  forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ),
    val_interp (hS := hS) (arrayT t) vs v -∗
    val_interp (hS := hS) (structRefT (flatten_ty t)) vs v.
Proof.
  intros. iIntros "Hv".
  intros. rewrite val_interp_array_unfold.
  iDestruct "Hv" as "[Hv|Hnull]".
  - iDestruct "Hv" as (l ls n idx H0lt Hnonempty (->&->&?&?&Heq1&Heq2)) "(Hsz1&Hsz1'&H1)".
    iAssert (loc_paired (addr_base ls) (addr_base l)) with "[H1]" as "#Hpaired".
    {
      destruct n; try lia; [].
      rewrite ?big_sepL_cons.
      iDestruct "H1" as "(H&_)".
      destruct (flatten_ty t); first by congruence.
      rewrite ?big_sepL_cons.
      iDestruct "H" as "(H&_)".
      iApply is_loc_loc_paired; eauto.
    }
    iLeft.
    assert (0 < length (flatten_ty t))%nat.
    { destruct (flatten_ty t); simpl in *; try congruence. lia. }
    unshelve (iExists l, ls, (n * length (flatten_ty t))%nat, _, _).
    { lia. }
    { destruct (flatten_ty t); simpl in *; try congruence. }
    iSplitL "".
    { iPureIntro; split_and!; eauto. lia. }
    rewrite Nat2Z.inj_mul. iFrame.
    iFrame "Hpaired".
    destruct (decide (0 ≤ idx  ∧ idx < n)%Z) as [(Hr1&Hr2)|Hout]; last first.
    { iRight. iPureIntro. rewrite Heq1.
      assert (idx < 0 ∨ n <= idx) as [?|?] by lia.
      - left.
        apply Z.mul_neg_pos; lia.
      - right.
        apply Z.mul_le_mono_nonneg_r; lia.
    }
    iLeft.
    iDestruct (big_sepL_elem_of _ (seq 0 n) (Z.to_nat idx) with "H1") as "H".
    { apply elem_of_list_In, in_seq. lia. }
    assert (addr_base ls +ₗ length (flatten_ty t) * Z.to_nat idx = ls) as ->.
    { symmetry. rewrite (addr_plus_off_decode ls); f_equal; word. }
    assert (addr_base l +ₗ length (flatten_ty t) * Z.to_nat idx = l) as ->.
    { symmetry. rewrite (addr_plus_off_decode l); f_equal; word. }
    eauto.
  - iRight. eauto.
Qed.

Lemma ctx_has_semTy_subst `{hG: !heapG Σ} `{hC: !crashG Σ} `{hRG: !refinement_heapG Σ} {hS: styG Σ}
      e es t x v vs tx Γ:
      ctx_has_semTy (hS := hS) (<[x:=tx]> Γ) es e t -∗
      val_interp (hS := hS) tx vs v -∗
      ctx_has_semTy (hS := hS) Γ (subst' x vs es) (subst' x v e) t.
Proof.
  rewrite /ctx_has_semTy.
  iIntros "Hhasty Hval".
  iIntros (Γsubst Hproj) "Hsty Hspec Htrace Hctx".
  destruct x as [|x] => //=.
  { iApply ("Hhasty" with "[] [$] [$] [$]").
    * rewrite insert_anon //=.
    * eauto.
  }
  rewrite -?subst_map_insert'.
  iSpecialize ("Hhasty" $! (<[x := {| subst_ty := tx; subst_sval := vs; subst_ival := v |}]> Γsubst)
                 with "[] [$] [$] [$] [Hctx Hval]").
  { iPureIntro. rewrite -Hproj. apply: fmap_insert. }
  { iPoseProof (big_sepM_insert_2 with "[Hval] [Hctx]") as "$".
    * iFrame.
    * eauto.
  }
  rewrite ?fmap_insert //=.
Qed.

Lemma structRefT_comparableTy_val_eq ts vs1 v1 vs2 v2:
  forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ),
  val_interp (hS := hS) (structRefT ts) vs1 v1 -∗
  val_interp (hS := hS) (structRefT ts) vs2 v2 -∗
  ⌜ v1 = v2 ↔ vs1 = vs2 ⌝.
Proof.
  intros.
  iDestruct 1 as "[H1|Hnull1]";
  iDestruct 1 as "[H2|Hnull2]".
  * iDestruct "H1" as (?? n1 ?? (?&?&?&?&Hoffset1)) "(Hpaired1&_)".
    iDestruct "H2" as (?? n2 ?? (?&?&?&?&Hoffset2)) "(Hpaired2&_)".
    subst.
    iDestruct (loc_paired_base_eq_iff with "Hpaired1 Hpaired2") as %Heq; eauto.
    iPureIntro. apply litv_loc_eq_iff. eauto.
  * iDestruct "Hnull2" as %(?&(Hnull2s&Hnull2)). subst.
    iDestruct "H1" as (????? (?&?&?&?&?)) "H".
    iPureIntro.
    split; subst; inversion 1; exfalso; (eapply plus_off_preserves_non_null; [| eassumption]; eauto).
  * iDestruct "Hnull1" as %(?&(Hnull1s&Hnull1)). subst.
    iDestruct "H2" as (????? (?&?&Hnnull1&Hnnull2&?)) "H".
    iPureIntro.
    split; subst; intros Hnulleq; symmetry in Hnulleq; inversion Hnulleq; subst; symmetry.
    ** exfalso. rewrite addr_base_of_plus //= in Hnnull2.
    ** exfalso. rewrite addr_base_of_plus //= in Hnnull1.
  * iDestruct "Hnull1" as %(?&(Hnull1s&Hnull1)). subst.
    iDestruct "Hnull2" as %(?&(Hnull2s&Hnull2)). subst. iPureIntro. split; intros; eauto.
    ** (* this is kind of round about since inversion is behaving oddly on the null offset hypothesis *)
      f_equal. cut (∀ (l l': loc), #l = #l' → LitLoc l = LitLoc l'); eauto.
       inversion 1; eauto.
    ** (* this is kind of round about since inversion is behaving oddly on the null offset hypothesis *)
      f_equal. cut (∀ (l l': loc), (#l = (#l': @val (@spec_ext_op_field spec_ext))) →
                                     LitLoc l = LitLoc l'); eauto. inversion 1; eauto.
Qed.

Lemma comparableTy_val_eq t vs1 v1 vs2 v2:
  is_comparableTy t = true →
  forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ),
  val_interp (hS := hS) t vs1 v1 -∗
  val_interp (hS := hS) t vs2 v2 -∗
  ⌜ v1 = v2 ↔ vs1 = vs2 ⌝.
Proof.
  clear spec_trans.
  revert vs1 v1 vs2 v2.
  induction t => vs1 v1 vs2 v2; try (inversion 1; fail).
  - intros. destruct t; iPureIntro; naive_solver.
  - intros (?&?)%andb_prop.
    intros.
    iDestruct 1 as (?? ?? (->&->)) "(H1&H2)".
    iDestruct 1 as (?? ?? (->&->)) "(H1'&H2')".
    rewrite -/val_interp.
    iPoseProof (IHt1 with "H1 H1'") as "%"; eauto.
    iPoseProof (IHt2 with "H2 H2'") as "%"; eauto.
    iPureIntro. naive_solver.
  - intros.
    iIntros "H1 H2".
    iDestruct (arrayT_structRefT_promote with "H1") as "H1".
    iDestruct (arrayT_structRefT_promote with "H2") as "H2".
    iApply (structRefT_comparableTy_val_eq with "H1 H2").
  - intros. apply structRefT_comparableTy_val_eq.
Qed.

Lemma sty_val_size:
      forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ) τ vs v,
        sty_val_interp hS τ vs v -∗
        ⌜ length (flatten_struct vs) = 1%nat ∧
          length (flatten_struct v) = 1%nat ⌝.
Proof. iIntros. by iDestruct (sty_val_flatten with "[$]") as %[-> ->]. Qed.

Lemma length_flatten_well_typed vs v t:
  forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ),
  val_interp (hS := hS) t vs v -∗
  ⌜ length (flatten_ty t) = length (flatten_struct vs) ∧
    length (flatten_ty t) = length (flatten_struct v) ⌝.
Proof.
  iIntros (Σ hG hC hRG hG' HS) "Hval".
  iInduction t as [] "IH" forall (vs v).
  - destruct t; iDestruct "Hval" as %Hval;
    repeat destruct Hval as (?&Hval); subst; eauto.
  - iDestruct "Hval" as (???? (?&?)) "(H1&H2)". subst.
    rewrite /= ?app_length.
    iDestruct ("IH" with "[$]") as %[Heq1 Heq2].
    iDestruct ("IH1" with "[$]") as %[Heq1' Heq2'].
    subst. iPureIntro. lia.
  - iDestruct "Hval" as "[Hval|Hval]"; iDestruct "Hval" as (?? (?&?)) "Hval";
      subst; eauto.
  - iDestruct "Hval" as (?????? (?&?)) "H1". subst; eauto.
  - iDestruct "Hval" as "[Hval|Hnull]"; last first.
    { iDestruct "Hnull" as (?) "(%&%)"; subst. eauto. }
    iDestruct "Hval" as (?????? (?&?&?&?)) "H1". subst; eauto.
  - iDestruct "Hval" as "[Hval|Hnull]"; last first.
    { iDestruct "Hnull" as (?) "(%&%)"; subst. eauto. }
    iDestruct "Hval" as (????? (?&?&?&?)) "H1". subst; eauto.
  - iDestruct "Hval" as %[].
  - rewrite /val_interp/=. iDestruct (sty_val_size with "Hval") as "(%&%)"; eauto.
Qed.


Lemma flatten_well_typed vs v t i vsi vi ti:
  forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ),
    flatten_ty t !! i = Some ti →
    flatten_struct vs !! i = Some vsi →
    flatten_struct v !! i = Some vi →
    val_interp (hS := hS) t vs v -∗
    val_interp (hS := hS) ti vsi vi.
Proof.
  iIntros (Σ hG hC hRG HS Hlookup1 Hlookup2 Hlookup3) "Hval".
  iInduction t as [] "IH" forall (vs v i Hlookup1 Hlookup2 Hlookup3).
  - simpl in *.
    destruct t; destruct i; simpl in *; inversion Hlookup1; subst; eauto;
    iDestruct "Hval" as %Hval; repeat destruct Hval as (?&Hval); subst; eauto;
    simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
  - iDestruct "Hval" as (???? (?&?)) "(H1&H2)". subst.
    simpl in Hlookup1, Hlookup2, Hlookup3.
    iDestruct (length_flatten_well_typed with "H1") as %[Hlen1 Hlens1].
    iDestruct (length_flatten_well_typed with "H2") as %[Hlen2 Hlens2].
    apply lookup_app_Some in Hlookup1 as [Hleft|Hright].
    { specialize (lookup_lt_Some _ _ _ Hleft) => Hlen.
      rewrite lookup_app_l in Hlookup2; last by lia.
      rewrite lookup_app_l in Hlookup3; last by lia.
      iApply "IH"; eauto.
    }
    { destruct Hright as (?&Hright).
      specialize (lookup_lt_Some _ _ _ Hright) => Hlen.
      rewrite lookup_app_r in Hlookup2; last by lia.
      rewrite lookup_app_r in Hlookup3; last by lia.
      iApply "IH1"; eauto.
      { rewrite Hlen1; eauto. }
      { rewrite Hlens1; eauto. }
    }
  - iDestruct "Hval" as "[Hval|Hval]"; iDestruct "Hval" as (?? (?&?)) "Hval";
      subst; eauto.
    { simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iLeft. iExists _, _. iSplitL ""; first done. eauto. }
    { simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iRight. iExists _, _. iSplitL ""; first done. eauto. }
  - iDestruct "Hval" as (?????? (->&->)) "H". subst.
    { simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iExists _,_,_,_,_,_. iFrame. eauto. }
  - iDestruct "Hval" as "[Hval|Hnull]".
    { iDestruct "Hval" as (?????? (?&?&?&?)) "H1". subst; eauto.
      simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iLeft. unshelve (iExists _, _, _, _, _, _; iSplitL ""; first done; eauto); eauto. }
    { iDestruct "Hnull" as (?) "(%&%)"; subst.
      simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iRight. eauto. }
  - iDestruct "Hval" as "[Hval|Hnull]".
    { iDestruct "Hval" as (????? (?&?&?&?)) "H1". subst; eauto.
      simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iLeft. unshelve (iExists _, _, _, _, _; iSplitL ""; first done; eauto); eauto. }
    { iDestruct "Hnull" as (?) "(%&%)"; subst.
      simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iRight. eauto. }
  - iDestruct "Hval" as %[].
  - rewrite /val_interp/=. iDestruct (sty_val_flatten with "Hval") as %[Heq1 Heq2].
    { simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      rewrite Heq1 in Hlookup2.
      rewrite Heq2 in Hlookup3.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
    }
Qed.

Scheme expr_typing_ind := Induction for expr_transTy Sort Prop with
    val_typing_ind := Induction for val_transTy Sort Prop.

Lemma loc_paired_init l ls:
  forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ),
  meta_token l ⊤ -∗
  meta_token (hG := refinement_na_heapG) ls ⊤ ==∗
  loc_paired ls l.
Proof.
  intros. iIntros "Htok1 Htok2".
  iMod (meta_set ⊤ l ls rlN with "[$]").
  { solve_ndisj. }
  iMod (meta_set (hG := refinement_na_heapG) ⊤ ls l rlN with "[$]").
  { solve_ndisj. }
  by iFrame.
Qed.

Lemma is_loc_init l ls v vs:
  forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) P,
  l ↦ v -∗
  meta_token l ⊤ -∗
  ls s↦ vs -∗
  meta_token (hG := refinement_na_heapG) ls ⊤ -∗
  P vs v -∗
  |={⊤}=> is_loc ls l P.
Proof.
  intros. iIntros "Hl Hltok Hls Hlstok HP".
  iMod (fc_auth_init) as (γ) "Hfc".
  iMod (loc_paired_init with "[$] [$]") as "$".
  iExists γ.
  iMod (inv_alloc locN ⊤ (loc_inv γ ls l P) with "[-]") as "$"; last done.
  { iNext. iExists _, _. iLeft. iFrame. }
Qed.

Lemma logical_reln_prepare_write t ts vs v j K (Hctx: LanguageCtx K):
  forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ),
  {{{ spec_ctx ∗ val_interp (hS := hS) (structRefT (t :: ts)) vs v ∗ j ⤇ K (PrepareWrite vs) }}}
    PrepareWrite v
    {{{ RET #();
        ∃ (ls l: loc) mem_vs mem_v γ,
                       ⌜ vs = #ls ∧ v = #l ⌝ ∗
                       inv locN (loc_inv γ ls l (val_interp (hS := hS) t)) ∗
                       fc_tok γ (1/2)%Qp ∗
                       j ⤇ K #() ∗
                       na_heap_mapsto_st (hG := refinement_na_heapG) WSt ls (1/2)%Qp mem_vs ∗
                       (∀ v' : sval, na_heap_mapsto ls 1 v' -∗ heap_mapsto ls 1 v') ∗
                       na_heap_mapsto_st (hG := heapG_na_heapG) WSt l 1 mem_v ∗
                       (∀ v' : ival, na_heap_mapsto l 1 v' -∗ heap_mapsto l 1 v')}}}.
Proof.
  intros. iIntros "(#Hctx&Hvl&Hj) HΦ".
  rewrite val_interp_struct_unfold.
  iDestruct "Hvl" as "[Hv|Hnull]".
  * iDestruct "Hv" as (lv lvs n H0lt Hnonemtpy (->&->&?&?&?)) "(Hpaired&Hblock1&Hblocked2&Hloc)".
    iDestruct "Hloc" as "[Hinbound|Hoob]".
    {
      iDestruct "Hinbound" as "(H&_)".
      rewrite /is_loc. iDestruct "H" as "(Hlocinv&Hpaired')".
      iDestruct "Hlocinv" as (γ) "#Hlocinv".
      iInv "Hlocinv" as "Hlocinv_body" "Hclo".
      rewrite /loc_inv. iDestruct "Hlocinv_body" as (mem_vs mem_v) "H".
      iDestruct "H" as "[H0readers|[Hreaders|Hwriter]]".
      {
        iDestruct "H0readers" as "(>Hfc&>Hspts&>Hpts&#Hval)".
        rewrite ?loc_add_0.
        iApply (wp_prepare_write with "[$]"). iIntros "!> Hpts".
        iMod (@ghost_prepare_write _ _ _ _ _ _ _ _ _ Hctx with "[$] Hspts Hj") as "(Hspts&Hptsclo&Hj)".
        { solve_ndisj. }
        iDestruct "Hspts" as "(Hspts1&Hspts2)".
        iMod (fc_auth_first_tok with "Hfc") as "(Hfc&Htok)".
        iMod ("Hclo" with "[Hspts1 Hfc Hval]").
        { iNext. iExists mem_vs, mem_v. iRight. iRight. iFrame. }
        iApply "HΦ". iModIntro. iExists _, _, _, _, _. iFrame "Hlocinv". iFrame.
        eauto.
      }
      {
        iDestruct "Hreaders" as (q q' n') "(>%&>Hfc&>Hspts&>Hpts&#Hval)".
        rewrite ?loc_add_0.
        iMod (ghost_prepare_write_read_stuck with "Hctx Hspts Hj") as %[].
        { lia. }
        { solve_ndisj. }
      }
      {
        (* UB: writer during write *)
        iDestruct "Hwriter" as "(>Hfc&>Hspts)".
        rewrite ?loc_add_0.
        iMod (ghost_prepare_write_write_stuck with "Hctx Hspts Hj") as %[].
        { solve_ndisj. }
      }
    }
    {
      (* UB: oob *)
      iDestruct "Hoob" as %Hoob.
      iMod (ghost_prepare_write_block_oob_stuck with "[$] [$] [$]") as %[].
      { lia. }
      { solve_ndisj. }
    }
  * iDestruct "Hnull" as %(?&->&->).
    (* UB: null *)
    iMod (ghost_prepare_write_null_stuck with "[$] [$]") as %[].
    { rewrite addr_base_of_plus //=. }
    { solve_ndisj. }
Qed.

Lemma sty_fundamental_lemma:
  sty_rules_obligation →
  ∀ Γ es e τ, expr_transTy _ _ _ spec_trans Γ es e τ →
  forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ),
    ⊢ ctx_has_semTy (hS := hS) Γ es e τ.
Proof using spec_trans.
  iIntros (Hrules ???? Htyping).
  induction Htyping using @expr_typing_ind with
      (spec_trans := spec_trans)
      (P := (λ Γ es e τ
             (HTYPE: expr_transTy _ _ _ spec_trans Γ es e τ),
             forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ),
               ⊢ ctx_has_semTy (hS := hS) Γ es e τ))
      (P0 := (λ Γ vs v τ
             (HTYPE: val_transTy _ _ _ spec_trans Γ vs v τ),
             forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ),
               ⊢ ctx_has_semTy (hS := hS) Γ vs v τ));
    intros ??????; iIntros (Γsubst HPROJ) "#Hinv #Hspec #Htrace #Hctx".
  (* Variables *)
  - subst.
    rewrite lookup_fmap in e.
    apply fmap_Some_1 in e as (t'&?&?). subst.
    iDestruct (big_sepM_lookup with "Hctx") as "H"; first eauto.
    rewrite /= ?lookup_fmap H //=.
    iIntros (j K Hctx) "Hj". iApply wpc_value; iSplit.
    * iModIntro. iExists _; iFrame "H"; iFrame.
    * iModIntro. iApply fupd_mask_weaken; first by set_solver+. eauto.
  (* Function app. *)
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) x2).
    spec_bind (subst_map ((subst_sval <$> Γsubst)) x1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    wpc_bind (subst_map _ f2).
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [AppLCtx (vs2)] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[Hv2] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    simpl. iDestruct "Hv1" as (?????? (Heq1&Heq2)) "#Hinterp".
    iApply ("Hinterp" with "[$]").
    { iFrame. }
  - iApply (IHHtyping with "[//] [$] [$] [$] [$]").
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. econstructor; eauto.
      { simpl. econstructor; eauto. }
      { econstructor; eauto. }
    }
    wpc_pures; eauto.
    iExists _; iFrame.
    iExists _, _, _, _, _, _; iSplit; first eauto.
    iLöb as "IH".
    iAlways. iIntros (v vs) "Hval".
    clear j K Hctx.
    iIntros (j K Hctx) "Hj".
    wpc_pures; first auto.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)".
      (* TODO: make spec_ctx auto frame source_ctx *)
    }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. econstructor; eauto.
    }
    iPoseProof (ctx_has_semTy_subst with "[] []") as "H1".
    { iApply IHHtyping. }
    { simpl. iExists _, _, _, _, _, _. iFrame "IH"; eauto. }
    iPoseProof (ctx_has_semTy_subst with "[] Hval") as "H2".
    { iApply "H1". }
    iSpecialize ("H2" with "[//] [$] [$] [$] [$] [//] [Hj]").
    { do 2 (rewrite -subst_map_binder_insert' subst_map_binder_insert).
      iEval (rewrite (binder_delete_commute f x)). iFrame. }
    { do 2 (rewrite -subst_map_binder_insert' subst_map_binder_insert).
      iEval (rewrite {2}binder_delete_commute). iFrame. }
  (* Fork *)
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)".
    }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. econstructor; eauto.
    }
    iEval (simpl; rewrite right_id) in "Hchild".
    iDestruct "Hchild" as (j') "Hj'".
    iApply (wpc_fork with "[Hj']").
    { iNext. iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H"; eauto.
      iSpecialize ("H" $! j' (λ x, x) with "[] [$]"); first by (iPureIntro; apply language_ctx_id).
      iApply (wpc_mono with "H"); eauto.
    }
    iSplit; first eauto. iNext. iExists _; iFrame; eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) cond').
    spec_bind (_ _ cond) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last done.

    iIntros (vcond) "H". iDestruct "H" as (vscond) "(Hj&Hvcond)".
    (* split on the value of the bool *)
    iDestruct "Hvcond" as %(b&->&->).
    destruct b.
    * wpc_pures; first done. simpl.
      iMod (ghost_step_lifting_puredet _ _ K with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply head_prim_step. econstructor; eauto.
      }
      iApply (IHHtyping2 with "[//] [$] [$] [$] [$]"). eauto.
    * wpc_pures; first done. simpl.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply head_prim_step. econstructor; eauto.
      }
      iApply (IHHtyping3 with "[//] [$] [$] [$] [$]"). eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iMod (ghost_step_stuck_det with "Hj []") as %[]; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros; eapply stuck_Panic. }
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iApply wp_wpc.
    iApply wp_fupd.
    iApply wp_ArbitraryInt; auto.
    iNext.
    iIntros. iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. repeat econstructor; eauto.
    }
    iModIntro. iExists _. iFrame. iExists _. iPureIntro; eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [UnOpCtx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u64), ⌜ un_op_eval ToUInt64Op v1 = Some #vres ∧
                            un_op_eval ToUInt64Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply head_prim_step. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wpc_pures; eauto.
      iExists _. iFrame. eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u32), ⌜ un_op_eval ToUInt32Op v1 = Some #vres ∧
                            un_op_eval ToUInt32Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply head_prim_step. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wpc_pures; eauto.
      iExists _. iFrame. eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u8), ⌜ un_op_eval ToUInt8Op v1 = Some #vres ∧
                            un_op_eval ToUInt8Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply head_prim_step. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wpc_pures; eauto.
      iExists _. iFrame. eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: string), ⌜ un_op_eval ToStringOp v1 = Some #(LitString vres) ∧
                            un_op_eval ToStringOp vs1 = Some #(LitString vres) ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply head_prim_step. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wpc_pures; eauto.
      iExists _. iFrame. eauto.
  - destruct op; try inversion e; subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iDestruct "Hv1" as (?) "(%&%)"; subst.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. repeat econstructor; eauto.
    }
    wpc_pures; eauto.
    iExists _. iFrame. eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    wpc_bind (subst_map _ e2').
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    simpl. spec_bind (_ _ e2) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[Hv1] [] H"); last done.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. repeat econstructor; eauto.
    }

    wpc_pures; auto.
    iExists _. iFrame. iExists (bool_decide (vs1 = vs2)); eauto.
    iDestruct (comparableTy_val_eq with "Hv1 Hv2") as %Heq; auto.
    iPureIntro. split; first auto. do 2 f_equal.
    by apply bool_decide_iff.
  (* bin op *)
  - admit.
  - admit.
  - admit.
  (* data *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  (* pointers *)
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) n').
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [Primitive2LCtx _ _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (vn1) "H". iDestruct "H" as (vsn1) "(Hj&Hv1)".

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) v').
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [Primitive2RCtx _ _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[Hv1] [] H"); last done.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    iApply wp_wpc.
    iApply wp_fupd.
    iDestruct "Hv1" as (nint) "(->&->)".
    destruct (decide (0 < int.val nint)) as [Hnonneg|]; last first.
    { (* this is UB *) admit. }
    iDestruct (length_flatten_well_typed with "Hv2") as %(Hspecsize&Hsize).
    iApply wp_allocN_seq_sized_meta.
    { rewrite -Hsize. destruct (flatten_ty t) as [|]; try congruence; simpl; try lia. }
    { auto. }
    { auto. }
    iNext. iIntros (l) "(%&Hsize&Hpts)".
    iMod (ghost_allocN_seq_sized_meta with "[] Hj") as (ls) "(Hj&%&Hssize&Hspts)".
    { rewrite -Hspecsize. destruct (flatten_ty t) as [|]; try congruence; simpl; try lia. }
    { eassumption. }
    { solve_ndisj. }
    { iApply "Hspec". }
    iExists _. iFrame "Hj".
    rewrite val_interp_array_unfold /arrayT_interp.
    iLeft. unshelve (iExists l, ls, (int.nat nint), 0, _, _); eauto.
    { lia. }
    rewrite -Hsize -Hspecsize.
    iFrame. replace ((int.nat nint * length (flatten_ty t)))%Z with
                   (Z.of_nat (int.nat nint * length (flatten_ty t)))%nat by lia.
    iFrame.
    iSplitL "".
    { iPureIntro. split_and!; eauto.
      * apply addr_base_non_null_offset; eauto; naive_solver.
      * apply addr_base_non_null_offset; eauto; naive_solver.
      * naive_solver congruence.
      * lia.
    }
    rewrite (addr_offset_0_is_base l); last naive_solver.
    rewrite (addr_offset_0_is_base ls); last naive_solver.
    iCombine "Hpts Hspts" as "Hpts".
    rewrite -big_sepL_sep.
    iDestruct "Hv2" as "#Hv".
    iFrame.
    iApply big_sepL_fupd.
    iApply (big_sepL_mono_with_pers with "Hv Hpts").
    { iIntros (k x Hlookup) "#Hval (Hmtoks&Hsmtoks)".
      iDestruct (big_sepL_merge_big_sepL2 with "Hmtoks Hsmtoks") as "Hmtoks"; first lia.
      iApply big_sepL_fupd.
      iApply (big_sepL2_elim_big_sepL with "[] Hmtoks").
      { rewrite map_length //=. }
      { iAlways. iIntros (i vi vsi vty Hlookup1 Hlookup2 Hlookup3) "((Hpts&Hm)&(Hspts&Hsm))".
        rewrite list_lookup_fmap in Hlookup3.
        apply fmap_Some_1 in Hlookup3 as (sty&Hlookup3&Heq). subst.
        iDestruct (flatten_well_typed with "Hval") as "Hvali"; eauto.
        iMod (is_loc_init with "Hpts Hm Hspts Hsm Hvali") as "$".
        eauto.
      }
    }
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [BinOpLCtx _ _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (vn1) "H". iDestruct "H" as (vsn1) "(Hj&Hv1)".

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e2').
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [BinOpRCtx _ _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[Hv1] [] H"); last done.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    iApply wp_wpc.
    iApply wp_fupd.
    iDestruct "Hv2" as (off) "H". iDestruct "H" as %[Heq1 Heq2]. subst.
    iDestruct "Hv1" as "[Hv1|Hnull]"; last first.
    { iDestruct "Hnull" as %(off'&Heq1'&Heq2'). subst.
      wp_pures.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { solve_ndisj. }
      { intros ?. eexists. simpl.
        apply head_prim_step. repeat econstructor; eauto.
      }
      iModIntro. iExists _. iFrame. iRight.
      iExists _. rewrite /loc_add. rewrite addr_plus_plus. eauto.
    }
    iDestruct "Hv1" as (l ls n idx Hgtzero Hnonempty Hpeq) "(Hblock1&Hblock2&Hlist)".
    destruct Hpeq as (->&->&?&?&Hoff&Hoffs).
    wp_pures.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { solve_ndisj. }
    { intros ?. eexists. simpl.
      apply head_prim_step. repeat econstructor; eauto.
    }
    iModIntro.
    iExists _. iFrame. iLeft.
    unshelve (iExists (addr_plus_off l (ty_size t * int.val off)),
                                      (addr_plus_off ls (ty_size t * int.val off)), _, (idx + int.val off), _, _; iFrame); eauto.
    rewrite ?addr_base_of_plus ?addr_offset_of_plus. iPureIntro; split_and!; eauto.
    * rewrite Hoff. rewrite -ty_size_length.
      specialize (ty_size_ge_0 t). intros.
      rewrite Z2Nat.id //=. lia.
    * rewrite Hoffs. rewrite -ty_size_length.
      specialize (ty_size_ge_0 t). intros.
      rewrite Z2Nat.id //=. lia.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j K with "[] Hj"); first auto.
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (vn1) "H". iDestruct "H" as (vsn1) "(Hj&Hv1)".
    iExists _. iFrame "Hj". iApply arrayT_structRefT_promote. eauto.
  - admit.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) l').
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [Primitive1Ctx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (vn1) "H". iDestruct "H" as (vsn1) "(Hj&Hv1)".

    iApply wp_wpc.
    iApply wp_fupd.

    rewrite val_interp_struct_unfold.
    iDestruct "Hv1" as "[Hv|Hnull]".
    * iDestruct "Hv" as (lv lvs n H0lt Hnonemtpy (->&->&?&?&?)) "(Hpaired&Hblock1&Hblocked2&Hloc)".
      iDestruct "Hloc" as "[Hinbound|Hoob]".
      {
        iDestruct "Hinbound" as "(H&_)".
        rewrite /is_loc. iDestruct "H" as "(Hlocinv&Hpaired')".
        iDestruct "Hlocinv" as (γ) "Hlocinv".
        iInv "Hlocinv" as "Hlocinv_body" "Hclo".
        rewrite /loc_inv. iDestruct "Hlocinv_body" as (??) "H".
        iDestruct "H" as "[H0readers|[Hreaders|Hwriter]]".
        {
          iDestruct "H0readers" as "(>Hfc&>Hspts&>Hpts&#Hval)".
          rewrite ?loc_add_0.
          wp_step.
          iApply (wp_load with "[$]"). iIntros "!> Hpts".
          iMod (ghost_load with "[$] Hspts Hj") as "(Hspts&Hj)".
          { solve_ndisj. }
          iMod ("Hclo" with "[Hpts Hspts Hfc Hval]").
          { iNext. iExists _, _. iLeft. iFrame. iFrame "Hval". }
          iIntros "!> !>". iExists _. iFrame. iFrame "Hval".
        }
        {
          iDestruct "Hreaders" as (q q' n') "(>%&>Hfc&>Hspts&>Hpts&#Hval)".
          rewrite ?loc_add_0.
          wp_step.
          iApply (wp_load with "[$]"). iIntros "!> Hpts".
          iMod (ghost_load_rd with "[$] Hspts Hj") as "(Hspts&Hj)".
          { solve_ndisj. }
          iMod ("Hclo" with "[Hpts Hspts Hfc Hval]").
          { iNext. iExists _, _. iRight. iLeft. iExists _, _, _. iFrame. iFrame "Hval". eauto. }
          iIntros "!> !>". iExists _. iFrame. iFrame "Hval".
        }
        {
          iDestruct "Hwriter" as "(>Hfc&>Hspts)".
          rewrite ?loc_add_0.
          iMod (ghost_load_write_stuck with "[$] [$] [$]") as %[].
          { solve_ndisj. }
        }
      }
      {
        iDestruct "Hoob" as %Hoob.
        iMod (ghost_load_block_oob_stuck with "[$] [$] [$]") as %[].
        { lia. }
        { solve_ndisj. }
      }
    * iDestruct "Hnull" as %(?&->&->).
      iMod (ghost_load_null_stuck with "[$] [$]") as %[].
      { rewrite addr_base_of_plus //=. }
      { solve_ndisj. }
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) v').
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (subst_map _ v) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (varg) "H". iDestruct "H" as (vsarg) "(Hj&Hvarg)".

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) l').
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H".
    simpl. spec_bind (subst_map _ l) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (vl) "H". iDestruct "H" as (vsl) "(Hj&Hvl)".

    iApply wp_wpc.
    iApply wp_fupd.
    rewrite /Store. wp_pures.
    wp_bind (PrepareWrite _).

    (* XXX need tactic to do these pure det reductions ... *)
    simpl.
    spec_bind (App _ vsl) as Hctx'.
    iMod (ghost_step_lifting_puredet _ _ _ (App _ vsl) with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. simpl. econstructor. eauto.
    }
    simpl.
    clear Hctx'.


    spec_bind (Rec _ _ _) as Hctx'.
    iMod (ghost_step_lifting_puredet _ _ _ (Rec _ _ _)
            with "[Hj]") as "(Hj&_)"; swap 1 3.
    { simpl. iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. simpl. econstructor; eauto.
      * simpl. econstructor. econstructor.
      * econstructor. eauto.
    }
    clear Hctx'.

    spec_bind (App _ _) as Hctx'.
    iMod (ghost_step_lifting_puredet _ _ _ _
            with "[Hj]") as "(Hj&_)"; swap 1 3.
    { simpl. iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. simpl. econstructor; eauto.
    }
    clear Hctx'.

    simpl.
    spec_bind (PrepareWrite vsl) as Hctx'.
    wp_apply (logical_reln_prepare_write _ _ _ _ _ _ (Hctx') with "[Hvl Hj]").
    { iFrame "Hspec Hvl". iFrame "Hj". }
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) _).
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [AppRCtx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    iPoseProof (Hrules with "[$] [$] [$] [] Hj") as "H"; eauto.
  (* Values *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field spec_ffi_interp_field
         spec_ffi_interp_adequacy_field.

Section pre_assumptions.

Context `{Hhpre: @heapPreG ext ffi ffi_semantics interp _ Σ}.
Context `{Hcpre: @cfgPreG spec_lang Σ}.
Context `{Hrpre: @refinement_heapPreG spec_ext spec_ffi spec_interp _ spec_adeq Σ}.
Context `{Hcrashpre: crashPreG Σ}.
Context `{Hstypre: !sty_preG Σ}.

Definition sty_derived_crash_condition :=
    (λ (hG: heapG Σ) (hC: crashG Σ) (hRG: refinement_heapG Σ), ∃ hS,
      ▷ ∀ (hG': heapG Σ), |={⊤}=>
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
      |={styN}=> ∃ (new: sty_names), sty_init (sty_update Σ hS new))%I.

Lemma sty_inv_to_wpc hG hC hRG hS es e τ j:
  expr_transTy _ _ _ spec_trans ∅ es e τ →
  sty_crash_inv_obligation →
  sty_crash_obligation →
  sty_rules_obligation →
  spec_ctx -∗
  trace_ctx -∗
  sty_init hS -∗
  j ⤇ es -∗
  WPC e @ LVL_INIT; ⊤;⊤ ∖ ↑sN {{ _, True }}{{sty_derived_crash_condition hG hC hRG}}.
Proof.
  iIntros (Htype Hsty_crash_inv Hsty_crash Hsty_rules) "#Hspec #Htrace Hinit Hj".
    rewrite /sty_crash_obligation in Hsty_crash.
  iAssert (|={⊤}=> sty_inv hS ∗ WPC e @ LVL_INIT; ⊤;⊤ ∖ ↑sN ∖ styN {{ _, True }}{{sty_crash_cond hS}})%I with "[-]" as ">(#Hinv&H)".
  {
    rewrite /sty_crash_inv_obligation in Hsty_crash_inv.
    iApply (Hsty_crash_inv with "[$] [$] [Hj]").
    { iIntros "#Hinv'".
      iPoseProof (sty_fundamental_lemma Hsty_rules ∅ _ _ _ Htype) as "H"; eauto.
      iSpecialize ("H" $! ∅ with "[] [$] [$] [$] []").
      { iPureIntro. apply: fmap_empty. }
      { by rewrite big_sepM_empty. }
      rewrite /has_semTy.
      iSpecialize ("H" $! j id with "[] [Hj]").
      { iPureIntro. apply _. }
      { simpl. by rewrite fmap_empty subst_map_empty. }
      rewrite fmap_empty subst_map_empty.
      iApply (wpc_strong_mono _ _ _ _ _ _ _ _ _ _ (λ _, True%I) with "[$]"); eauto.
      iSplit.
      - eauto.
      - eauto. rewrite difference_diag_L.
        simpl. replace (LVL_OPS - LVL_OPS)%nat with O by lia. eauto.
    }
  }
  iApply (wpc_strong_mono with "[$]"); eauto.
  { solve_ndisj. }
  iSplit.
  - eauto.
  - iIntros.
    simpl. replace (LVL_INIT - LVL_INIT)%nat with O by lia. simpl.
    replace (⊤ ∖ ↑sN ∖ (⊤ ∖ ↑sN ∖ styN)) with (styN); last first.
    {
      rewrite difference_difference_remainder_L; auto.
      clear. generalize (styN_disjoint). solve_ndisj.
    }
    iMod (Hsty_crash with "[$] [$]").
    iModIntro. iModIntro. iExists _. iFrame.
Qed.
End pre_assumptions.

Existing Instances subG_cfgG subG_refinement_heapPreG subG_crashG.
Definition logical_relnΣ := #[styΣ; heapΣ; @cfgΣ spec_lang; refinement_heapΣ; crashΣ].

Lemma sty_adequacy es σs e σ τ initP:
  sty_init_obligation1 initP →
  sty_init_obligation2 initP →
  sty_crash_inv_obligation →
  sty_crash_obligation →
  sty_rules_obligation →
  expr_transTy _ _ _ spec_trans ∅ es e τ →
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  initP σ σs →
  trace_refines e e σ es es σs.
Proof.
  intros Hsty_init1 Hsty_init2 Hsty_crash_inv Hsty_crash Hsty_rules Htype Htrace Horacle Hinit.
  eapply @heap_wpc_refinement_adequacy with (spec_ext := spec_ext) (Σ := logical_relnΣ)
           (Φ := λ _ _ _ _, True%I) (Φc := sty_derived_crash_condition)
           (k := LVL_INIT) (initP := initP); eauto.
  { apply _. }
  { apply _. }
  { apply _. }
  { apply _. }
  { clear dependent σ σs. rewrite /wpc_init. iIntros (hG hC hRG σ σs Hinit) "Hffi Hffi_spec".
    rewrite /sty_init_obligation1 in Hsty_init1.
    rewrite /wpc_obligation.
    iIntros "Hj #Hspec #Htrace".
    iApply fupd_wpc.
    iPoseProof (Hsty_init1 _ _ _ _  with "[$] [$]") as "H"; first auto.
    iApply (fupd_mask_mono styN); first by set_solver+.
    iMod "H" as (names) "Hinit".
    iModIntro.
    iApply (sty_inv_to_wpc with "[$] [$] [$]"); eauto.
  }
  { clear dependent σ σs.
    rewrite /wpc_post_crash.
    iIntros (???) "H". iDestruct "H" as (hS') "H". iNext.
    iIntros (hG'). iMod ("H" $! hG') as "H". iModIntro.
    iIntros. iSpecialize ("H" with "[$] [$]").
    iDestruct "H" as (σs' Hcrash) "(Hctx&Hrest)".
    iExists σs', Hcrash. iFrame. iIntros (hRG') "Hcrash_rel Hrestart".
    iSpecialize ("Hrest" $! hRG' with "[$] [$]").
    rewrite /wpc_obligation.
    iIntros "Hj #Hspec #Htrace".
    iApply fupd_wpc.
    iApply (fupd_mask_mono styN); first by set_solver+.
    iMod "Hrest" as (names) "Hinv".
    iModIntro.
    iApply (sty_inv_to_wpc _ _ _ (sty_update logical_relnΣ hS' names) with "[$] [$] [$]"); eauto.
  }
  Grab Existential Variables.
  apply subG_styPreG, _.
Qed.


End reln_adeq.

End reln.
