/-
Byte strings.

Go strings are arbitrary byte sequences, so `GoString` is `List w8`. A literal
`go!"abc"` elaborates to the explicit list of its UTF-8 bytes, so that equality
of literals is decidable by `decide`/`simp` without unfolding `String.toUTF8`.
-/
module

public import Lean
public import Perennial.Std.Word

@[expose] public section

namespace Perennial

abbrev byte_string := List w8
abbrev GoString := byte_string

def stringToGoString (s : String) : GoString :=
  s.toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat)

instance : Coe String GoString := ⟨stringToGoString⟩

open Lean Elab Term Meta in
/-- `go!"abc"` is the `GoString` with the UTF-8 bytes of `"abc"`. -/
elab:max "go!" s:str : term => do
  let bytes := s.getString.toUTF8.toList
  let mut e : Lean.Expr := mkApp (mkConst ``List.nil [0]) (mkConst ``w8)
  for b in bytes.reverse do
    let lit ← mkAppM ``BitVec.ofNat #[mkNatLit 8, mkNatLit b.toNat]
    e := mkApp3 (mkConst ``List.cons [0]) (mkConst ``w8) lit e
  return e

theorem goString_lit_test : go!"ab" = [97#8, 98#8] := rfl

end Perennial
