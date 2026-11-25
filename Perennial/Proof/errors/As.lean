/-
The proof of `errors.As` (the real `wrap.go`: `As`'s checks of its target, over the Go model of
`internal/reflectlite`, and its tree walk `as`).
-/
module

public import Perennial.Spec.errors.As
public import Perennial.Spec.errors.as_
public import Perennial.Spec.internal.reflectlite.ValueOf
public import Perennial.Spec.internal.reflectlite.Value__Type
public import Perennial.Spec.internal.reflectlite.Value__IsNil
public import Perennial.Spec.internal.reflectlite.rtype__Kind
public import Perennial.Spec.internal.reflectlite.rtype__Elem
public import Perennial.Spec.internal.reflectlite.rtype__Implements

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- `As(err, any(l))` for a non-`nil` error and a target `*T` that passes `As`'s checks
(`AsTarget`, `T` of a kind): `as(err, target, asTargetVal T l, asTargetType T)`. -/
theorem errors.wp_As_ok
    (wp_ValueOf : internal.reflectlite.ValueOf.spec (GF := GF) (hG := hG))
    (wp_Value_Type : internal.reflectlite.Value.Type.spec (GF := GF) (hG := hG))
    (wp_Value_IsNil : internal.reflectlite.Value.IsNil.spec (GF := GF) (hG := hG))
    (wp_rtype_Kind : internal.reflectlite.rtype.Kind.spec (GF := GF) (hG := hG))
    (wp_rtype_Elem : internal.reflectlite.rtype.Elem.spec (GF := GF) (hG := hG))
    (wp_rtype_Implements : internal.reflectlite.rtype.Implements.spec (GF := GF) (hG := hG))
    (ii : GoInterfaceOk) (l : Loc) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {T : go.GoType} [IntoValTyped (GF := GF) T' T] (kT : Nat)
    (hkT : go.kindOf (underlying T) = some kT) (hNT : go.isUntypedNil (underlying T) = false)
    (hT : AsTarget T) (hl : l ≠ null) (R : IProp GF) (Q : Bool → IProp GF)
    (has : {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ R }}
      (App (App (App (App (Val (@! errors.as')) (Val #(interface.ok ii)))
        (Val #(interface.mkOk (go.PointerType T) #l))) (Val #(errors.asTargetVal T l)))
        (Val #(errors.asTargetType T)))
      {{ (b : Bool), RET #b; Q b }}) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ R }}
      (App (App (Val (@! errors.As)) (Val #(interface.ok ii)))
        (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ (b : Bool), RET #b; Q b }} := by
  haveI : T ↓u underlying T := ⟨rfl⟩
  iintro %Φ ⟨#Hinit, HR⟩ HΦ
  wp_func_call; wp_call
  try wp_auto
  have hpk : go.kindOf (go.PointerType T) = some 22 := by simp [go.kindOf]
  have hd1 : reflect.directIfaceN 1 (go.PointerType T) = some true := by
    simpa [reflect.directKind] using
      reflect.directIfaceN_of_kind (t := go.PointerType T) (u := go.PointerType T) 0 hpk
        (by omega) (by omega)
  wp_apply wp_ValueOf.1 (V := Loc) (t := go.PointerType T) (u := go.PointerType T) 22 1 true l hpk
    (by simp [go.isInterfaceType]) (by simp [internal.reflectlite.rtypeLayoutU]) hd1 as %xv Hxv
  unfold internal.reflectlite.valueOfRepr
  icases Hxv with (⟨%hd, %hxv⟩ | ⟨%q, ⟨%hd, %hxv⟩, -⟩)
  rotate_left
  · exfalso
    obtain ⟨n, hd⟩ := hd
    cases n with
    | zero => simp [reflect.directIfaceN] at hd
    | succ n =>
      rw [reflect.directIfaceN_of_kind (t := go.PointerType T) (u := go.PointerType T) n hpk
        (by omega) (by omega)] at hd
      simp [reflect.directKind] at hd
  subst hxv
  rw [MethodUnfold.method_unfold (t := go.PointerType internal.reflectlite.Value.ty) (m := go!"Type")]
  wp_call
  try wp_auto
  wp_apply wp_Value_Type (errors.asTargetVal T l) (by show W64 22 ≠ W64 0; decide)
  unfold go.tok
  wp_apply wp_rtype_Kind (T := go.PointerType T) 22 null hpk
  try wp_auto
  try (rw [MethodUnfold.method_unfold (t := go.PointerType internal.reflectlite.Value.ty) (m := go!"IsNil")]; wp_call; try wp_auto)
  wp_apply wp_Value_IsNil (internal.reflectlite.Value.mk (interface.mkOk (go.PointerType (go.PointerType T)) #null)
      (interface.mkOk (go.PointerType T) #l) (W64 ((22 : Nat) : Int))) (t := go.PointerType T) (e := T) l
    (by show W64 ((22 : Nat) : Int) &&& W64 31 = W64 22; decide)
    (by show W64 ((22 : Nat) : Int) &&& W64 128 = W64 0; decide) rfl
  try simp only [hl, decide_false]
  try wp_auto
  wp_apply wp_rtype_Elem (T := go.PointerType T) T null (by simp [go.typeQuery, go.is_underlying])
  unfold go.tok
  wp_apply wp_rtype_Kind (T := T) kT null hkT
  ihave #HET := errors.errorType_of_init $$ Hinit
  cases hI : go.isInterfaceType (underlying T)
  · have h20 := internal.reflectlite.kindOf_ne_20 hkT hI
    have hk20 := internal.reflectlite.kne_20 kT (internal.reflectlite.kindOf_lt hkT) h20
    simp only [hk20, decide_false, Bool.not_false]
    try wp_auto
    have hts : go.typeSetContains T go.error = true := by
      rcases hT with ⟨elems, he⟩ | h
      · rw [he] at hI; simp [go.isInterfaceType] at hI
      · exact h
    rw [show interface.mkOk (go.PointerType T) #null = go.tok T from rfl]
    wp_apply wp_rtype_Implements (U := go.error) (W := T') (t := T) kT hkT hI hNT
    rw [hts]
    try wp_auto
    simp only [errors.asTargetVal, errors.asTargetType, go.tok] at has
    rw [show (W64 ((22 : Nat) : Int) : w64) = W64 22 from rfl]
    try unfold go.tok
    wp_apply has $$ [$HR] as %b HQ
    try wp_auto
    iapply HΦ
    iexact HQ
  · obtain ⟨elems, hUT⟩ : ∃ elems, underlying T = go.InterfaceType elems := by
      revert hI; cases underlying T <;> simp [go.isInterfaceType]
    rw [hUT] at hkT
    simp only [internal.reflectlite.kindOf_interface, Option.some.injEq] at hkT
    subst hkT
    try wp_auto
    simp only [errors.asTargetVal, errors.asTargetType, go.tok] at has
    rw [show (W64 ((22 : Nat) : Int) : w64) = W64 22 from rfl]
    try unfold go.tok
    wp_apply has $$ [$HR] as %b HQ
    try wp_auto
    iapply HΦ
    iexact HQ

/-- The kind of `T`, from the head of an `asNoMatch` of a non-`nil` error. -/
theorem errors.asNoMatch_kind (T : go.GoType) (n : Nat) (ii : GoInterfaceOk) :
    errors.asNoMatch (GF := GF) T n (interface.ok ii) ⊢
      ⌜(∃ k, go.kindOf (underlying T) = some k) ∧ go.isUntypedNil (underlying T) = false⌝ ∗
      errors.asNoMatch (GF := GF) T n (interface.ok ii) := by
  iintro H
  cases n with
  | zero =>
    iunfold errors.asNoMatch at H
    icases H with %H
    rcases H.1 with h | ⟨ii3, h, -, -, hd⟩
    · cases h
    isplitr
    · ipureintro; exact ⟨hd.2.1, hd.2.2.1⟩
    iunfold errors.asNoMatch
    ipureintro; exact H
  | succ n =>
    iunfold errors.asNoMatch at H
    icases H with (%H | ⟨%ii2, %H, HW⟩)
    · rcases H.1 with h | ⟨ii3, h, -, -, hd⟩
      · cases h
      isplitr
      · ipureintro; exact ⟨hd.2.1, hd.2.2.1⟩
      iunfold errors.asNoMatch
      ileft; ipureintro; exact H
    · isplitr
      · ipureintro; exact ⟨H.2.2.1.2.1, H.2.2.1.2.2.1⟩
      iunfold errors.asNoMatch
      iright; iexists ii2; iframe; ipureintro; exact H

theorem errors.As.wp_proof
    (wp_ValueOf : internal.reflectlite.ValueOf.spec (GF := GF) (hG := hG))
    (wp_Value_Type : internal.reflectlite.Value.Type.spec (GF := GF) (hG := hG))
    (wp_Value_IsNil : internal.reflectlite.Value.IsNil.spec (GF := GF) (hG := hG))
    (wp_rtype_Kind : internal.reflectlite.rtype.Kind.spec (GF := GF) (hG := hG))
    (wp_rtype_Elem : internal.reflectlite.rtype.Elem.spec (GF := GF) (hG := hG))
    (wp_rtype_Implements : internal.reflectlite.rtype.Implements.spec (GF := GF) (hG := hG))
    (wp_as : errors.«as».spec (GF := GF) (hG := hG)) :
    errors.As.spec (GF := GF) (hG := hG) := by
  have ok := errors.wp_As_ok wp_ValueOf wp_Value_Type wp_Value_IsNil wp_rtype_Kind wp_rtype_Elem
    wp_rtype_Implements
  refine ⟨?_, ?_, ?_⟩
  · intro S err l T' _ _ T _ v hT hdec
    iintro %Φ ⟨#Hinit, #Htree, %HS, Hl⟩ HΦ
    icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %hl⟩
    cases err with
    | nil =>
      wp_func_call; wp_call
      try wp_auto
      iapply HΦ
      iframe
    | ok ii =>
      obtain ⟨hd, -⟩ := hdec ii HS
      obtain ⟨-, ⟨kT, hkT⟩, hNT, -⟩ := hd
      wp_apply ok ii l kT hkT hNT hT hl _ _ (wp_as.1 S ii l v hT hdec) $$ [Hl] as %b ⟨%v', Hl⟩
      · iframe; iframe #; ipureintro; exact HS
      iapply HΦ
      iframe
  · intro ii l T' _ _ T _ v hT hdec hrep hA htyped
    iintro %Φ ⟨#Hinit, Hl⟩ HΦ
    icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %hl⟩
    obtain ⟨-, ⟨kT, hkT⟩, hNT, -⟩ := id hdec
    wp_apply ok ii l kT hkT hNT hT hl _ _ (wp_as.2.1 ii l v hT hdec hrep hA htyped) $$ [$Hl]
      as %b ⟨%hb, %x, Hl, %hx⟩
    subst hb
    iapply HΦ
    iframe
    ipureintro; exact hx
  · intro n err l T' _ _ T _ v hT
    iintro %Φ ⟨#Hinit, Hl, Hm⟩ HΦ
    icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %hl⟩
    cases err with
    | nil =>
      wp_func_call; wp_call
      try wp_auto
      iapply HΦ
      iframe
    | ok ii =>
      ihave ⟨%hk, Hm⟩ := errors.asNoMatch_kind T n ii $$ Hm
      obtain ⟨⟨kT, hkT⟩, hNT⟩ := hk
      wp_apply ok ii l kT hkT hNT hT hl _ _ (wp_as.2.2 n ii l v hT) $$ [$Hl $Hm] as %b ⟨%hb, Hl⟩
      subst hb
      iapply HΦ
      iframe

end proof

end Perennial
