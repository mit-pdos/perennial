/-
The interface tests (`interfaces.go`, `interfaces_complex.go`) under the byte
memory's interface semantics (`go.SemanticsB`, `Golang/Defn/StaticImage.lean`),
on goose's unchanged translation: interface values are `(itab, data)` and
`(type, data)` headers over boxed bytes, method calls go through the static
itab's code pointers, and the package's static data is assumed
(`StaticAssumptions`, which goose would generate next to `Assumptions`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics_proof.semantics_init
public import Perennial.Golang.Theory.StaticIface

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE go

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics

/-! ## Byte layouts (goose would generate them) -/

instance SquareStruct.byteRepr : ByteRepr SquareStruct where
  size := 8
  align := 8
  encode x := ByteRepr.encode x.Side'
  decode bs := (ByteRepr.decode bs).map SquareStruct.mk
  align_pos := by decide
  length_encode x := ByteRepr.length_encode (V := w64) _
  decode_encode x := by simp [ByteRepr.decode_encode]
  length_of_decode bs v h := by
    obtain ⟨w, hw, -⟩ := Option.map_eq_some_iff.1 h
    exact ByteRepr.length_of_decode (V := w64) _ _ hw

instance NumStruct.byteRepr : ByteRepr NumStruct where
  size := 8
  align := 8
  encode x := ByteRepr.encode x.Value'
  decode bs := (ByteRepr.decode bs).map NumStruct.mk
  align_pos := by decide
  length_encode x := ByteRepr.length_encode (V := w64) _
  decode_encode x := by simp [ByteRepr.decode_encode]
  length_of_decode bs v h := by
    obtain ⟨w, hw, -⟩ := Option.map_eq_some_iff.1 h
    exact ByteRepr.length_of_decode (V := w64) _ _ hw

/-- The methods of an interface type, from its (syntactic) underlying type. -/
@[reducible] def ifaceElems : go.GoType → List go.InterfaceElem
  | .InterfaceType elems => elems
  | _ => []

/-! ## Typed points-to of the test's structs

`GeneratedProof`'s instances are stated under `go.Semantics`, though they do not
use the interface semantics; proofgen should state them under a class without
it. Restated here under `go.SemanticsB` (the same generated proof scripts). -/

namespace SquareStruct
section def_

-- the FFI instances are global (from the disk prelude)
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [semB : go.SemanticsB]
variable [package_sem' : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

instance SquareStruct_B_typed_pointsto :
    TypedPointsto (GF := GF) github_com.mit_pdos.perennial.goose.testdata.examples.semantics.SquareStruct where
  typedPointstoDef l v dq := iprop(
    "Side" ∷ typedPointsto (structFieldRef github_com.mit_pdos.perennial.goose.testdata.examples.semantics.SquareStruct go!"Side" l) v.Side' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance SquareStruct_B_into_val_typed :
    IntoValTypedUnderlying (GF := GF) github_com.mit_pdos.perennial.goose.testdata.examples.semantics.SquareStruct github_com.mit_pdos.perennial.goose.testdata.examples.semantics.SquareStruct.underlying := by
  solve_into_val_typed_struct

instance SquareStruct_B_access_load_Side (l : Loc) (v : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.SquareStruct) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.mit_pdos.perennial.goose.testdata.examples.semantics.SquareStruct go!"Side" l) v.Side' dq)
      (typedPointsto (structFieldRef github_com.mit_pdos.perennial.goose.testdata.examples.semantics.SquareStruct go!"Side" l) v.Side' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance SquareStruct_B_access_store_Side (l : Loc) (v : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.SquareStruct) (Side' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.mit_pdos.perennial.goose.testdata.examples.semantics.SquareStruct go!"Side" l) v.Side' (DFrac.own 1))
      (typedPointsto (structFieldRef github_com.mit_pdos.perennial.goose.testdata.examples.semantics.SquareStruct go!"Side" l) Side' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Side' := Side' } : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.SquareStruct) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

end def_
end SquareStruct

namespace NumStruct
section def_

-- the FFI instances are global (from the disk prelude)
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [semB : go.SemanticsB]
variable [package_sem' : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

instance NumStruct_B_typed_pointsto :
    TypedPointsto (GF := GF) github_com.mit_pdos.perennial.goose.testdata.examples.semantics.NumStruct where
  typedPointstoDef l v dq := iprop(
    "Value" ∷ typedPointsto (structFieldRef github_com.mit_pdos.perennial.goose.testdata.examples.semantics.NumStruct go!"Value" l) v.Value' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance NumStruct_B_into_val_typed :
    IntoValTypedUnderlying (GF := GF) github_com.mit_pdos.perennial.goose.testdata.examples.semantics.NumStruct github_com.mit_pdos.perennial.goose.testdata.examples.semantics.NumStruct.underlying := by
  solve_into_val_typed_struct

instance NumStruct_B_access_load_Value (l : Loc) (v : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.NumStruct) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.mit_pdos.perennial.goose.testdata.examples.semantics.NumStruct go!"Value" l) v.Value' dq)
      (typedPointsto (structFieldRef github_com.mit_pdos.perennial.goose.testdata.examples.semantics.NumStruct go!"Value" l) v.Value' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

instance NumStruct_B_access_store_Value (l : Loc) (v : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.NumStruct) (Value' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef github_com.mit_pdos.perennial.goose.testdata.examples.semantics.NumStruct go!"Value" l) v.Value' (DFrac.own 1))
      (typedPointsto (structFieldRef github_com.mit_pdos.perennial.goose.testdata.examples.semantics.NumStruct go!"Value" l) Value' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with Value' := Value' } : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.NumStruct) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

end def_
end NumStruct

/-! ## The package's static data (goose would generate this class) -/

class StaticAssumptions [GoGlobalContext] [GoSemanticsFunctions] [StaticSymbols] : Prop where
  SquareStruct_bytes : TypeBytes SquareStruct.ty SquareStruct
  NumStruct_bytes : TypeBytes NumStruct.ty NumStruct
  geometryInterface_methods : IfaceMethods geometryInterface.ty [go!"Square", go!"Volume"]
  geometryInterface_underlying_methods :
    IfaceMethods geometryInterface.underlying [go!"Square", go!"Volume"]
  SquareStruct_geometryInterface_itab : StaticItab SquareStruct.ty geometryInterface.ty
  SquareStruct_geometryInterface : Implements SquareStruct.ty geometryInterface.ty

attribute [instance] StaticAssumptions.SquareStruct_bytes StaticAssumptions.NumStruct_bytes
  StaticAssumptions.geometryInterface_methods
  StaticAssumptions.geometryInterface_underlying_methods
  StaticAssumptions.SquareStruct_geometryInterface_itab
  StaticAssumptions.SquareStruct_geometryInterface

section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [semB : go.SemanticsB] [package_sem : semantics.Assumptions]
variable [static : StaticAssumptions]
include package_sem static

/-- A semantics test function `name` returns `true`. -/
def TestFunOkB (name : GoString) : Prop :=
  ∀ Φ : val → IProp GF, ⊢ Φ #true -∗ WP (App (Val (@! name)) (Val #())) {{ Φ }}

open ProofMode

theorem geometry_Square : go!"Square" ∈ itabMethods geometryInterface.ty := by
  rw [IfaceMethods.itab_methods (t := geometryInterface.ty)]; simp

theorem geometry_Volume : go!"Volume" ∈ itabMethods geometryInterface.ty := by
  rw [IfaceMethods.itab_methods (t := geometryInterface.ty)]; simp

omit package_sem static in
include hG in
theorem iface_val (tab d : w64) : PairV #true (PairV #tab #d) = #(⟨tab, d⟩ : GoIface) := by
  rw [intoVal_unfold GoIface]

theorem wp_testBasicInterface : TestFunOkB (GF := GF) testBasicInterface := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  steps
  wp_apply wp_convert_iface (by rfl) (by rfl) as %i #Hi
  steps
  wp_apply wp_iface_method_resolve go!"Square" i _ geometry_Square (by decide) $$ [$Hi]
  steps
  iexact HΦ


theorem wp_testAssignInterface : TestFunOkB (GF := GF) testAssignInterface := by
  intro Φ; iintro HΦ
  wp_func_call; wp_call; steps
  wp_apply wp_convert_iface (by rfl) (by rfl) as %i1 #Hi1
  steps
  wp_apply wp_iface_method_resolve go!"Square" i1 _ geometry_Square (by decide) $$ [$Hi1]
  steps
  iexact HΦ

theorem wp_testMultipleInterface : TestFunOkB (GF := GF) testMultipleInterface := by
  intro Φ; iintro HΦ
  wp_func_call; wp_call; steps
  wp_apply wp_convert_iface (by rfl) (by rfl) as %i2 #Hi2
  steps
  wp_apply wp_iface_method_resolve go!"Square" i2 _ geometry_Square (by decide) $$ [$Hi2]
  steps
  wp_apply wp_convert_iface (by rfl) (by rfl) as %i3 #Hi3
  steps
  wp_apply wp_iface_method_resolve go!"Square" i3 _ geometry_Square (by decide) $$ [$Hi3]
  steps
  iexact HΦ

theorem wp_testBinaryExprInterface : TestFunOkB (GF := GF) testBinaryExprInterface := by
  intro Φ; iintro HΦ
  wp_func_call; wp_call; steps
  wp_apply wp_convert_iface (by rfl) (by rfl) as %i4 #Hi4
  steps
  wp_apply wp_iface_method_resolve go!"Square" i4 _ geometry_Square (by decide) $$ [$Hi4]
  steps
  wp_apply wp_convert_iface (by rfl) (by rfl) as %i5 #Hi5
  steps
  wp_apply wp_iface_method_resolve go!"Volume" i5 _ geometry_Volume (by decide) $$ [$Hi5]
  steps
  wp_apply wp_convert_iface (by rfl) (by rfl) as %i6 #Hi6
  steps
  wp_apply wp_iface_method_resolve go!"Square" i6 _ geometry_Square (by decide) $$ [$Hi6]
  steps
  wp_apply wp_convert_iface (by rfl) (by rfl) as %i7 #Hi7
  steps
  wp_apply wp_iface_method_resolve go!"Volume" i7 _ geometry_Volume (by decide) $$ [$Hi7]
  steps
  iexact HΦ

theorem wp_testIfStmtInterface : TestFunOkB (GF := GF) testIfStmtInterface := by
  intro Φ; iintro HΦ
  wp_func_call; wp_call; steps
  wp_apply wp_convert_iface (by rfl) (by rfl) as %i8 #Hi8
  steps
  wp_apply wp_iface_method_resolve go!"Square" i8 _ geometry_Square (by decide) $$ [$Hi8]
  steps
  iexact HΦ

theorem wp_testParamsInterface : TestFunOkB (GF := GF) testParamsInterface := by
  intro Φ; iintro HΦ
  wp_func_call; wp_call; steps
  wp_apply wp_convert_iface (by rfl) (by rfl) as %i9 #Hi9
  steps
  wp_apply wp_iface_method_resolve go!"Volume" i9 _ geometry_Volume (by decide) $$ [$Hi9]
  steps
  iexact HΦ

theorem wp_testEmptyInterface : TestFunOkB (GF := GF) testEmptyInterface := by
  intro Φ; iintro HΦ
  wp_func_call; wp_call; steps
  wp_apply wp_eq_eface_nil
  steps
  iexact HΦ

theorem wp_testTypeAssertionInterface : TestFunOkB (GF := GF) testTypeAssertionInterface := by
  intro Φ; iintro HΦ
  wp_func_call; wp_call; steps
  wp_apply wp_convert_eface (by rfl) (by rfl) as %i #Hi
  steps
  wp_apply wp_type_assert_eface (by rfl) i _ (by decide) $$ [$Hi]
  steps
  iexact HΦ

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
