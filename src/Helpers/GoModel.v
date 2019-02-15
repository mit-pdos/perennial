From RecoveryRefinement Require Import Helpers.MachinePrimitives.

Import UIntNotations.

Class HasGoZero (T:Type) := zeroValue : T.

Arguments zeroValue T {_}.

Instance uint64_zero : HasGoZero uint64 := 0%u64.
Instance bool_zero : HasGoZero bool := false.

Axiom byte0 : byte.
Instance byte_zero : HasGoZero byte := byte0.
