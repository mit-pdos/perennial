From Perennial.goose_lang Require Import notation.

Module interface.
Section goose_lang.
Context `{ffi_syntax}.

Definition call : val.
Admitted.

Definition val (x : gmap string val) : val.
Admitted.

End goose_lang.
End interface.
