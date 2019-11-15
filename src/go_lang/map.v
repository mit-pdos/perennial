From Perennial.go_lang Require Export lang notation.
From Perennial.go_lang Require Import typing.

Definition NewMap {ext:ext_op} (t:ty) : expr := AllocMap (zero_val t).
