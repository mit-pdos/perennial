/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/unittest/generics.v`:
specs for the goose generics unit tests.
-/
import Perennial.Proof.ProofPrelude
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.helpers
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : generics.Assumptions]

instance is_pkg_init_helpers :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.helpers :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_helpers :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.helpers :=
  build_get_is_pkg_init_wf

instance is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics :=
  build_get_is_pkg_init_wf

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics

section generic_proofs
variable {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {T : go.type}
  [IntoValTyped (GF := GF) T' T]

theorem wp_BoxGet (b : Box.t T') :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val #(functions BoxGet [T])) (Val #b))
    {{ RET #(b.Value'); True }} := by
  wp_start as _
  wp_auto
  wp_end

theorem wp_Box__Get' (b : Box.t T') :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (b @!! Box T @!! go!"Get")) (Val #()))
    {{ RET #(b.Value'); True }} := by
  wp_start as _
  wp_auto
  wp_end

theorem wp_Box__Get (l : loc) (b : Box.t T') :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ l ↦ b }}
      (App (Val (l @!! go.type.PointerType (Box T) @!! go!"Get")) (Val #()))
    {{ RET #(b.Value'); True }} := by
  wp_start
  wp_auto
  wp_apply wp_Box__Get'
  wp_end

theorem wp_makeGenericBox (value : T') :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val #(functions makeGenericBox [T])) (Val #value))
    {{ RET #(Box.t.mk value); True }} := by
  wp_start
  wp_auto
  wp_end

end generic_proofs

theorem wp_BoxGet2 (b : Box.t w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! BoxGet2)) (Val #b))
    {{ RET #(b.Value'); True }} := by
  wp_start
  wp_auto
  wp_end

theorem wp_makeBox :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! makeBox)) (Val #()))
    {{ RET #(Box.t.mk (W64 42)); True }} := by
  wp_start
  wp_end

theorem wp_useBoxGet :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! useBoxGet)) (Val #()))
    {{ RET #(W64 42); True }} := by
  wp_start
  wp_auto
  wp_apply wp_makeGenericBox
  wp_apply wp_Box__Get $$ [$]
  wp_end

theorem wp_useContainer :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! useContainer)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_apply wp_map_make1 with %m Hm
  wp_apply wp_map_insert $$ Hm with Hm
  wp_apply wp_map_insert $$ Hm with Hm
  wp_end

theorem wp_useMultiParam :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! useMultiParam)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_end

theorem wp_multiParamFunc {A' : Type} [ZeroVal A'] [TypedPointsto (GF := GF) A'] {A : go.type}
    [IntoValTyped (GF := GF) A' A]
    {B' : Type} [ZeroVal B'] [TypedPointsto (GF := GF) B'] {B : go.type}
    [IntoValTyped (GF := GF) B' B] (x : A') (y : B') :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (App (Val #(functions multiParamFunc [A, B])) (Val #x)) (Val #y))
    {{ (s : slice.t), RET #s; s ↦* [y] }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, _⟩
  wp_auto
  iapply HΦ
  iExactEq Hsl
  rfl

theorem wp_useMultiParamFunc :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! useMultiParamFunc)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_apply wp_multiParamFunc with %s H
  wp_end

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics

end Perennial
