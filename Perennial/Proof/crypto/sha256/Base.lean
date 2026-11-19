/-
Shared definitions of the proofs of the Go `crypto/sha256` package: its `isPkgInit`, and
`is_hash data h` (`h` is the SHA-256 hash of `data`, computed in this run) with its laws.
`is_hash_inj` (collision resistance) holds under the run's no-collision assumption
`Sha256NoCollision ok` (`Perennial/GooseLang/Ext/Sha256/Impl.lean`); the others hold for every run.
-/
module

public import Perennial.Proof.Sha256Prelude
public import Perennial.Code.crypto.sha256
public import Perennial.GeneratedProof.crypto.sha256

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace crypto.sha256

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] {ok : Sha256Filter} [HasSha256 ok]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha256.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.crypto.sha256 :=
  define_is_pkg_init iprop(True)

instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.crypto.sha256 :=
  build_get_is_pkg_init_wf

/-- `is_hash data h`: `h` is SHA-256's hash of `data` (`sha256IsHash`). Persistent. -/
def is_hash (data : List w8) (h : GoArray w8 32) : IProp GF :=
  sha256IsHash ok (gooseSha256GS (ok := ok)) data h

instance is_hash_persistent (data : List w8) (h : GoArray w8 32) :
    Persistent (is_hash (GF := GF) data h) := by
  unfold is_hash; infer_instance

/-- SHA-256 is a function: one hash per input. -/
theorem is_hash_det (data : List w8) (h1 h2 : GoArray w8 32) :
    is_hash (GF := GF) data h1 ∗ is_hash (GF := GF) data h2 ⊢ ⌜h1 = h2⌝ :=
  sha256IsHash_det ok _ data h1 h2

/-- Collision resistance, under the run's no-collision assumption: of the hashes computed, no two
inputs share one. -/
theorem is_hash_inj (H : Sha256NoCollision ok) (data1 data2 : List w8) (h : GoArray w8 32) :
    is_hash (GF := GF) data1 h ∗ is_hash (GF := GF) data2 h ⊢ ⌜data1 = data2⌝ :=
  sha256IsHash_inj ok H _ data1 data2 h

/-- A hash has 32 bytes (`Size`). -/
theorem is_hash_len (data : List w8) (h : GoArray w8 32) :
    is_hash (GF := GF) data h ⊢ ⌜h.arr.length = 32⌝ :=
  sha256IsHash_len ok _ data h

end defs

end crypto.sha256

end Perennial
