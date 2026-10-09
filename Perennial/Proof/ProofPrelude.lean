/-
The common imports of goose proofs:
* `Perennial.Std.All`: list/word/arith libraries;
* `Perennial.Algebra.BigOp`: big separating conjunctions;
* `Perennial.Helpers.NamedProps`: named propositions (`iNamed`);
* `Perennial.IrisLib.*` and `Perennial.GooseLang.IPersist`: dfrac/ipersist
  helpers;
* `Perennial.Ghost`: ghost-state libraries.
-/
module

public import Perennial.Std.All
public import Perennial.Algebra.BigOp
public import Perennial.Helpers.NamedProps
public import Perennial.IrisLib.DFrac
public import Perennial.IrisLib.DFractional
public import Perennial.GooseLang.IPersist
public import Perennial.Ghost

@[expose] public section
