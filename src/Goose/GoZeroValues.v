From RecoveryRefinement.Goose Require Import Machine.

Class HasGoZero (T:Type) := zeroValue : T.

Arguments zeroValue T {_}.

Instance uint64_zero : HasGoZero uint64 := 0.
Instance bool_zero : HasGoZero bool := false.

Axiom byte0 : byte.
Instance byte_zero : HasGoZero byte := byte0.

Instance ptr_zero ty : HasGoZero (Ptr.t ty) := nullptr _.
Instance file_zero : HasGoZero File := nilFile.
Instance slice_zero T : HasGoZero (slice.t T) := slice.nil _.

Instance string_zero : HasGoZero string := ""%string.
