/-
The Go theory without channels and strings
(which are built on top of it).
-/
module

public import Perennial.GooseLang.Lang
public import Perennial.Golang.Defn.Pre
public import Perennial.Golang.Theory.ProofMode
public import Perennial.Golang.Theory.PostLifting
public import Perennial.Golang.Theory.Predeclared
public import Perennial.Golang.Theory.Mem
public import Perennial.Golang.Theory.Exception
public import Perennial.Golang.Theory.Loop
public import Perennial.Golang.Theory.Assume
public import Perennial.Golang.Theory.Pkg
public import Perennial.Golang.Theory.TacticsSimp
public import Perennial.Golang.Theory.Auto
public import Perennial.Golang.Theory.Defer
public import Perennial.Golang.Theory.Array
public import Perennial.Golang.Theory.Slice
public import Perennial.Golang.Theory.Map

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section shift_count
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- The count of a shift by an `int` (`go.shiftCount`, which goose applies to a signed count):
the count itself when it is not negative (Go panics on a negative one). -/
theorem wp_shiftCount_int (y : w64) :
    {{ (⌜0 ≤ sint.Z y⌝ : IProp GF) }}
      (App (Val (go.shiftCount go.int)) (Val #y))
    {{ RET #y; True }} := by
  wp_start as %Hy
  wp_if_destruct
  · exfalso; have : sint.Z (W64 0) = 0 := rfl; omega
  · iapply HΦ; itrivial

/-- `go.shiftCount` at `int64`: see `wp_shiftCount_int`. -/
theorem wp_shiftCount_int64 (y : w64) :
    {{ (⌜0 ≤ sint.Z y⌝ : IProp GF) }}
      (App (Val (go.shiftCount go.int64)) (Val #y))
    {{ RET #y; True }} := by
  wp_start as %Hy
  wp_if_destruct
  · exfalso; have : sint.Z (W64 0) = 0 := rfl; omega
  · iapply HΦ; itrivial

end shift_count

end Perennial
