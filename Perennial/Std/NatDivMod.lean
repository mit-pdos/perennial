/-
Port of `src/Helpers/NatDivMod.v`. In Rocq this file only enables `lia`
support for `/` and `mod`; Lean's `omega` handles division and modulus by
numerals natively, so there is nothing to port beyond the sanity check.
-/
import Perennial.Std.Word

namespace Perennial

example (n : Nat) : 2 * n % 2 = 0 := by omega

end Perennial
