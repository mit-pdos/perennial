/-
The proof of `crypto/sha256.Sum256`: its trusted model converts the slice to a string and hashes
it with the SHA-256 extension's primitive.
-/
module

public import Perennial.Spec.crypto.sha256.Sum256

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] {ok : Sha256Filter} [HasSha256 ok]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha256.Assumptions]

theorem crypto.sha256.Sum256.wp_proof :
    crypto.sha256.Sum256.spec (GF := GF) (hG := hG) := by
  intro s data dq
  wp_start as Hs
  wp_bind (App (Val (GoInstruction (Convert _ _))) _)
  wp_apply wp_bytes_to_string $$ Hs with Hs
  iapply wp_Sha256Sum
  iintro %h Hh
  iapply HΦ
  iframe
  unfold crypto.sha256.is_hash
  iexact Hh

end proof

end Perennial
