/-
Port of `new/proof/proof_prelude.v`: the common imports of new goose proofs.

Rocq exports `Perennial.algebra.big_op`, the `Perennial.Helpers` libraries
(`Tactics List ListLen Transitions ModArith iris ipm Integers`),
`Perennial.base`, `Perennial.program_logic.ncinv` and `New.ghost`.

In Lean:
* `Perennial.Std.All` covers the `Helpers` list/word/arith libraries;
* `Perennial.Algebra.BigOp` is `big_op`;
* `Perennial.Helpers.NamedProps` is `ipm` (named propositions, `iNamed`);
* `Perennial.IrisLib.*` and `Perennial.GooseLang.IPersist` are the
  dfrac/ipersist helpers that Rocq gets through `iris` and `base`;
* `Perennial.Ghost` is `New.ghost`.
* `ncinv` (non-cancelable invariants) is crash-only and not ported.

Rocq also sets `Default Proof Using "Type"` and `Printing Projections`; neither
has a Lean counterpart.
-/
import Perennial.Std.All
import Perennial.Algebra.BigOp
import Perennial.Helpers.NamedProps
import Perennial.IrisLib.DFrac
import Perennial.IrisLib.DFractional
import Perennial.GooseLang.IPersist
import Perennial.Ghost
