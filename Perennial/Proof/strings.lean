/-
Port of `new/proof/strings.v`: specs for the Go `strings` package.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.strings
import Perennial.GeneratedProof.strings

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace strings

/-- Model for Go's `unicode.IsSpace` for ASCII-range bytes. Based on
https://cs.opensource.google/go/go/+/refs/tags/go1.26.1:src/strings/strings.go;l=377 -/
def is_ascii_space (b : w8) : Bool :=
  [9#8,    -- \t  (0x09)
   10#8,   -- \n  (0x0A)
   11#8,   -- \v  (0x0B)
   12#8,   -- \f  (0x0C)
   13#8,   -- \r  (0x0D)
   32#8    -- space (0x20)
  ].contains b

def split_fields_aux : go_string → Option go_string → List go_string
  | [], w => match w with | none => [] | some w => [w]
  | x :: s, w =>
    if is_ascii_space x then
      match w with
      | none => split_fields_aux s none
      | some w => w :: split_fields_aux s none
    else split_fields_aux s (some (w.getD [] ++ [x]))

def split_fields (s : go_string) : List go_string := split_fields_aux s none

/-! Tests of `split_fields`, which is part of the `wp_Fields` axiom. -/

example : split_fields go!"hello" = [go!"hello"] := by decide

example : split_fields go!"   hello world" = [go!"hello", go!"world"] := by decide

example : split_fields go!"hello world" = [go!"hello", go!"world"] := by decide

example : split_fields go!"" = [] := by decide

def bs_tab : w8 := 9#8
def bs_nl : w8 := 10#8
def bs_cr : w8 := 13#8
def bs_sp : w8 := 32#8

def hello_world_ws : go_string :=
  [bs_sp, bs_tab] ++ go!"hello" ++ [bs_nl] ++ go!"world" ++ [bs_cr, bs_sp]

example : split_fields hello_world_ws = [go!"hello", go!"world"] := by decide

example : split_fields go!"  hello\tthere\ngeneral\rkenobi " =
    [go!"hello", go!"there", go!"general", go!"kenobi"] := by decide

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.strings :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.strings :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.strings get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.strings }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := array.t w8 256) asciiSpace (go.ArrayType 256 go.uint8) with H
  iframe Hown
  is_pkg_init_finish

/-- FIXME (from Rocq): this is wrong (unsound) for strings with non-ASCII
runes. Simplest solution might be to add a precondition for the string to be
all ASCII. (`own_slice_cap w8` is also as in Rocq.) -/
axiom wp_Fields [package_sem : strings.Assumptions] (s : go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.strings }}
      (App (Val (@! Fields)) (Val #s))
    {{ (sl : slice.t), RET #sl;
        sl ↦* (split_fields s) ∗ own_slice_cap w8 sl (DFrac.own 1) }}

/-! Unit tests for `wp_Fields`. -/

example :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.strings }}
      (App (Val (@! Fields)) (Val #(go!"  hello\tthere\ngeneral\rkenobi ")))
    {{ (sl : slice.t), RET #sl;
        sl ↦* [go!"hello", go!"there", go!"general", go!"kenobi"] ∗
        own_slice_cap w8 sl (DFrac.own 1) }} := by
  iintro %Φ #Hinit HΦ
  wp_apply +noauto wp_Fields with %sl ⟨Hsl, Hcap⟩
  have h : split_fields go!"  hello\tthere\ngeneral\rkenobi " =
      [go!"hello", go!"there", go!"general", go!"kenobi"] := by decide
  rw [h]
  iapply HΦ
  iframe

example :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.strings }}
      (App (Val (@! Fields)) (Val #(go!"hello world")))
    {{ (sl : slice.t), RET #sl;
        sl ↦* [go!"hello", go!"world"] ∗
        own_slice_cap w8 sl (DFrac.own 1) }} := by
  iintro %Φ #Hinit HΦ
  wp_apply +noauto wp_Fields go!"hello world" with %sl ⟨Hsl, Hcap⟩
  have h : split_fields go!"hello world" = [go!"hello", go!"world"] := by decide
  rw [h]
  iapply HΦ
  iframe

end wps

end strings

end Perennial
end
