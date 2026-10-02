/-
Port of `new/proof/crypto/ed25519.v`: package initialization of
`crypto/ed25519`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.crypto.ed25519
import Perennial.GeneratedProof.crypto.ed25519

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace crypto.ed25519

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.ed25519.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.crypto.ed25519 :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.crypto.ed25519 :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.crypto.ed25519 get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.crypto.ed25519 }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  -- `cryptocustomrand'init` is opaque (an axiom in the generated code)
  sorry -- Rocq: Admitted

end proof

end crypto.ed25519

end Perennial
end
