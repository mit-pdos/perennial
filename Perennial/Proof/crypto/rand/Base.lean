/-
Shared definitions of the proofs of the Go `crypto/rand` package: its `isPkgInit`
(`isInitialized`, the package's `Reader`).
-/
module

public import Perennial.Proof.math.big.Base
public import Perennial.Code.crypto.rand
public import Perennial.GeneratedProof.crypto.rand

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace crypto.rand

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]

/-- What `crypto/rand`'s initialization gives: its package-level `Reader` (an
`io.Reader`). Its value is opaque: nothing is known about it beyond being the reader the
package installed, and `wp_Int` is stated for exactly that reader. -/
def isInitialized : IProp GF :=
  iprop(∃ rdr : GoInterface, "#Reader" ∷ (globalAddr Reader ↦□ rdr : IProp GF))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.crypto.rand :=
  define_is_pkg_init isInitialized
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.crypto.rand :=
  build_get_is_pkg_init_wf

theorem isInitialized_access :
    isPkgInit (PROP := IProp GF) pkg_id.crypto.rand ⊢ isInitialized :=
  isPkgInit_access (PROP := IProp GF) pkg_id.crypto.rand

end wps

end crypto.rand

end Perennial
