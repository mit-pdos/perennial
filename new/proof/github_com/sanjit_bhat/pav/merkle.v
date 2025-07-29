(* NOTE: "merkle_proof" files themselves don't explicitly define Modules.
this allows merkle files to not have to write "merkle".
however, when they're exposed to the outside, they're within this merkle module. *)
From New.proof.github_com.sanjit_bhat.pav.merkle_proof Require Import base serde theory.

Module merkle.
  Export base serde theory.
End merkle.
