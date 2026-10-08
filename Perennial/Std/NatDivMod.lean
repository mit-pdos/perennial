/-
Natural-number division and modulus. Lean's `omega` handles division and
modulus by numerals natively, so this file only contains a sanity check.
-/
import Perennial.Std.Word

namespace Perennial

example (n : Nat) : 2 * n % 2 = 0 := by omega

end Perennial
