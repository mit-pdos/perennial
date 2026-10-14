/-
Shared definitions of the proofs of `internal/stringslite`, the string functions shared by
`strings` and the runtime: its `isPkgInit`, `trimPrefix` and a lemma about byte occurrences.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.stringslite
public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace internal.stringslite

/-- What `TrimPrefix(s, pfx)` returns: `s` without the prefix `pfx` if it has it, else `s`. -/
def trimPrefix (s pfx : GoString) : GoString :=
  if pfx <+: s then s.drop pfx.length else s

/-- A byte `c` occurs at `k` in `s[a:b]` iff `s` has `c` at `a + k < b`. -/
theorem occ_slice_singleton (s : GoString) (c : w8) (a b k : Nat) :
    [c] <+: ((s.drop a).take (b - a)).drop k ↔ a + k < b ∧ s[a + k]? = some c := by
  rw [internal.bytealg.occ_singleton_iff, List.getElem?_take, List.getElem?_drop]
  by_cases h : k < b - a
  · rw [ite_eq_left h]; exact ⟨fun h' => ⟨by omega, h'⟩, fun h' => h'.2⟩
  · rw [ite_eq_right h]
    constructor
    · intro h'; cases h'
    · intro h'; omega

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : internal.stringslite.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.stringslite :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.stringslite :=
  build_get_is_pkg_init_wf


end wps

end internal.stringslite

end Perennial
end
