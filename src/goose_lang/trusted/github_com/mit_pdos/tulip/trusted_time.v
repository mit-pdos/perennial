From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang.ffi Require Import grove_prelude.

Section goose_lang.

Definition GetTime : val :=
  λ: <>, grove_ffi.GetTSC #().

End goose_lang.
