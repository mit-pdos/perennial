From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
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

Context {spec_ext: spec_ext_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{spec_interp: @spec_ffi_interp spec_ffi}.
Context `{spec_adeq: !spec_ffi_interp_adequacy}.
Context (spec_ty: ext_types (@spec_ext_op_field spec_ext)).

Context `{Hhpre: @heapPreG ext ffi ffi_semantics interp _ Σ}.
Context `{Hcpre: @cfgPreG spec_lang Σ}.
Context `{Hrpre: @refinement_heapPreG spec_ext spec_ffi spec_interp _ spec_adeq Σ}.

Context {MAX: nat}.

Notation sexpr := (@expr (@spec_ext_op_field spec_ext)).
Notation sval := (@val (@spec_ext_op_field spec_ext)).
Notation iexpr := (@expr ext).
Notation ival := (@val ext).
Notation sty := (@ty (@val_tys _ spec_ty)).

Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field spec_ffi_interp_field
         spec_ffi_interp_adequacy_field.

Definition val_semTy := ∀ `(hG: !heapG Σ) (hRG: refinement_heapG Σ),
  sval → ival → iProp Σ.

Record spec_valTy_model :=
  { spec_val_interp : @ext_tys (@val_tys _ spec_ty) → val_semTy }.

Definition has_semTy `{hG: !heapG Σ} {hRG: refinement_heapG Σ} {hC: crashG Σ}
           (es: sexpr) (e: iexpr) (vty: val_semTy) : iProp Σ :=
  (∀ (j: nat) (K: sexpr → sexpr) (CTX: LanguageCtx K),
      j ⤇ K es -∗ WPC e @ NotStuck; MAX; ⊤; (⊤ ∖ ↑sN) {{ v, ∃ vs, j ⤇ K (of_val vs)
                                                                    ∗ vty hG hRG vs v }}
                                                      {{ True }})%I.

Definition base_ty_interp `{hG: !heapG Σ} {hRG : refinement_heapG Σ} (t: base_ty) :=
  λ (v1: sval) (v2: ival),
  match t with
    | uint64BT => (∃ x, ⌜ v1 = LitV $ LitInt x ∧ v2 = LitV $ LitInt x ⌝ : iProp Σ)%I
    | uint32BT => (∃ x, ⌜ v1 = LitV $ LitInt32 x ∧ v2 = LitV $ LitInt32 x ⌝ : iProp Σ)%I
    | byteBT => (∃ x, ⌜ v1 = LitV $ LitByte x ∧ v2 = LitV $ LitByte x ⌝ : iProp Σ)%I
    | boolBT => (∃ x, ⌜ v1 = LitV $ LitBool x ∧ v2 = LitV $ LitBool x ⌝ : iProp Σ)%I
    | unitBT => (⌜ v1 = LitV $ LitUnit ∧ v2 = LitV $ LitUnit ⌝ : iProp Σ)%I
    | stringBT => (∃ x, ⌜ v1 = LitV $ LitString x ∧ v2 = LitV $ LitString x ⌝ : iProp Σ)%I
  end.

Fixpoint val_interp_aux `{hG: !heapG Σ} {hRG : refinement_heapG Σ}
         (smodel: spec_valTy_model) (t: sty) (vs: sval) (v: ival) :=
  match t with
  | baseT bt => base_ty_interp bt vs v
  | prodT t1 t2 => (∃ v1 v2 vs1 vs2, ⌜ v = (v1, v2)%V ∧
                                       vs = (vs1, vs2)%V⌝
                   ∗ val_interp_aux smodel t1 vs1 v1
                   ∗ val_interp_aux smodel t2 vs2 v2)%I
  | sumT t1 t2 => ((∃ v' vs', ⌜ v = InjLV v' ∧
                                vs = InjLV vs'⌝
                              ∗ val_interp_aux smodel t1 vs' v')
                     ∨
                   (∃ v' vs', ⌜ v = InjRV v' ∧
                                vs = InjRV vs'⌝
                              ∗ val_interp_aux smodel t2 vs' v'))%I
  | _ => False%I
  end.

Definition val_interp (smodel: spec_valTy_model) (t: sty) : val_semTy :=
  λ `(hG: !heapG Σ) (hRG: refinement_heapG Σ), val_interp_aux smodel t%I.

End reln.
