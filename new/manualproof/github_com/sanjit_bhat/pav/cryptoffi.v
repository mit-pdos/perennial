From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.trusted_code.github_com.sanjit_bhat.pav Require Import cryptoffi.

Module cryptoffi.

Module SigPublicKey.
#[global] Transparent cryptoffi.SigPublicKey.
#[global] Typeclasses Transparent cryptoffi.SigPublicKey.
Section def.
Context `{ffi_syntax}.
Definition t := slice.t.
End def.
End SigPublicKey.

End cryptoffi.
