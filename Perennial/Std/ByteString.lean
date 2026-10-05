/-
Byte strings. Port of `src/Helpers/ByteString.v`.

Go strings are arbitrary byte sequences, so `go_string` is `List w8`. A literal
`go!"abc"` elaborates to the explicit list of its UTF-8 bytes, so that equality
of literals is decidable by `decide`/`simp` without unfolding `String.toUTF8`.
-/
import Lean
import Perennial.Std.Word

namespace Perennial

abbrev byte_string := List w8
abbrev go_string := byte_string

def stringToGoString (s : String) : go_string :=
  s.toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat)

instance : Coe String go_string := ⟨stringToGoString⟩

open Lean Elab Term Meta in
/-- `go!"abc"` is the `go_string` with the UTF-8 bytes of `"abc"`. -/
elab:max "go!" s:str : term => do
  let bytes := s.getString.toUTF8.toList
  let mut e : Expr := mkApp (mkConst ``List.nil [0]) (mkConst ``w8)
  for b in bytes.reverse do
    let lit ← mkAppM ``BitVec.ofNat #[mkNatLit 8, mkNatLit b.toNat]
    e := mkApp3 (mkConst ``List.cons [0]) (mkConst ``w8) lit e
  return e

theorem go_string_lit_test : go!"ab" = [97#8, 98#8] := rfl

end Perennial
