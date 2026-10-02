/-
`encodeO` (encoding into the Leibniz OFE stored in ghost state). The basic
`Pos.Countable` instances live in `Perennial/Std/Countable.lean`.

The ghost libraries (`ghost_var`, `ghost_map`, `mono_list`, `saved_pred`, ...)
store `Pos.Countable.encode a`; see `Perennial/Ghost/All.lean`. User types can get
an instance from an injection with `Pos.Countable.ofInjective`.
-/
import Iris
import Perennial.Std.Countable

noncomputable section

namespace Perennial
open Iris

/-- Encode into `DiscreteO Pos` (the Leibniz OFE stored in ghost state). -/
def encodeO {A : Type} [Pos.Countable A] (a : A) : DiscreteO Pos := ⟨Pos.Countable.encode a⟩

theorem encodeO_inj {A : Type} [Pos.Countable A] {a b : A} (h : encodeO a = encodeO b) : a = b :=
  Pos.encode_inj (congrArg DiscreteO.car h)

@[simp] theorem encodeO_eq_iff {A : Type} [Pos.Countable A] {a b : A} :
    encodeO a = encodeO b ↔ a = b :=
  ⟨encodeO_inj, fun h => h ▸ rfl⟩

end Perennial
