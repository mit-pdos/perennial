From RecoveryRefinement.Goose Require Import Machine.

Class HasGoZero (T:Type) := zeroValue : T.

Arguments zeroValue T {_}.

Instance uint64_zero : HasGoZero uint64 := 0.
Instance bool_zero : HasGoZero bool := false.
Instance string_zero : HasGoZero string := ""%string.

Section GoModel.
  Context `{GoModel}.
  Global Instance byte_zero : HasGoZero byte := byte0.

  Global Instance ptr_zero ty : HasGoZero (Ptr ty) := nullptr _.
  Global Instance file_zero : HasGoZero File := nilFile.
  Global Instance slice_zero T : HasGoZero (slice.t T) := slice.nil _.
End GoModel.
