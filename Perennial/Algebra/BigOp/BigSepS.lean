/-
Port of `src/algebra/big_op/big_sepS.v`.

The Rocq file has no lemmas: it only re-exports `iris.algebra.big_op` and imports `ncfupd`
(crash logic, dropped) and `big_sepL`. This module re-exports the corresponding Lean
modules so that imports of `big_sepS` have a counterpart.
-/
import Iris.BI.BigOp
import Perennial.Algebra.BigOp.BigSepL
