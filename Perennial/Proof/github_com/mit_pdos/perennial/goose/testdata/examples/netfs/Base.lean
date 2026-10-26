/-
Shared definitions of the proofs of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs`:
its `isPkgInit`, and the protocol of the nodes over the network.

The nodes have addresses `"a"`, `"b"` and `"c"`. The protocol (`netInv`) is an
invariant that owns the messages sent to `"a"` and to `"b"` and says that each
of them carries the data `c0`, the contents of `"a"`'s file `"in"`, unless it
is from `"c"`. `"a"` and `"b"` send only `c0`; `"c"` sends anything, but the
network attaches its address to its messages, so that `"a"` and `"b"`, which
accept messages from each other only, receive only `c0`.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Base
public import Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.netfs
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std net_ext

namespace github_com.mit_pdos.perennial.goose.testdata.examples.netfs

/-- The messages `ms` follow the protocol: every message not from `"c"` carries
`c0`. -/
def goodMsgs (c0 : GoString) (ms : GSet NetMsg) : Prop :=
  ∀ m, m ∈ ms → m.sender ≠ go!"c" → m.data = c0

theorem goodMsgs_empty (c0 : GoString) : goodMsgs c0 ∅ := by
  intro m hm
  simp [GMap.mem_iff] at hm

theorem goodMsgs_add {c0 : GoString} {ms : GSet NetMsg} {m : NetMsg} (h : goodMsgs c0 ms)
    (hm : m.sender ≠ go!"c" → m.data = c0) : goodMsgs c0 (ms ∪ {[m]}) := by
  intro m' hm'
  have : m' ∈ ms ∨ m' = m := by
    simp only [GMap.mem_iff, GMap.lookup_union] at hm'
    by_cases h' : m' ∈ ms
    · exact .inl h'
    · right
      rw [GMap.mem_iff] at h'
      simp only [Option.not_isSome_iff_eq_none] at h'
      rw [h'] at hm'
      exact (by simpa [Singleton.singleton, GMap.lookup_singleton_iff] using hm' : m = m').symm
  rcases this with h' | rfl
  · exact h m' h'
  · exact hm

/-- The namespace of the protocol's invariant. -/
def netN : Namespace := nroot.@"netfs"

section defs
variable {GF : BundledGFunctors}

/-- The protocol, under the network's ghost state `hN`: the messages sent to
`"a"` and to `"b"` follow it. -/
abbrev netInv (hN : NetGS GF) (c0 : GoString) : IProp GF :=
  iprop(∃ msA msB : GSet NetMsg, netPointsto hN go!"a" (.own 1) msA ∗
    netPointsto hN go!"b" (.own 1) msB ∗ ⌜goodMsgs c0 msA⌝ ∗ ⌜goodMsgs c0 msB⌝)

end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs :=
  build_get_is_pkg_init_wf

open Iris.ProofMode

/-- A send to `"a"` or `"b"` that follows the protocol (from `"c"`, or of `c0`),
in the invariant: the atomic update of the send. -/
theorem netInv_send (c0 to data : GoString) (hto : to = go!"a" ∨ to = go!"b")
    (hok : netAddr (GF := GF) ≠ go!"c" → data = c0) :
    ⊢ inv netN (netInv (gooseNetGS (GF := GF)) c0) -∗ |={⊤,∅}=> ∃ ms : GSet NetMsg, to n↦ ms ∗
      (to n↦ (ms ∪ {[⟨netAddr (GF := GF), data⟩]}) ={∅,⊤}=∗ emp) := by
  iintro #Hinv
  iinv Hinv with ⟨%msA, %msB, >Ha, >Hb, >%HA, >%HB⟩ Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  rcases hto with rfl | rfl
  · iexists msA
    iframe Ha
    iintro Ha
    imod Hmask
    iapply Hclose
    inext
    iexists _, msB
    iframe
    ipureintro
    exact ⟨goodMsgs_add HA hok, HB⟩
  · iexists msB
    iframe Hb
    iintro Hb
    imod Hmask
    iapply Hclose
    inext
    iexists msA, _
    iframe
    ipureintro
    exact ⟨HA, goodMsgs_add HB hok⟩

/-- A receive at `"a"` or `"b"`, in the invariant: the atomic update of the
receive, which learns that the message follows the protocol. -/
theorem netInv_recv (c0 : GoString)
    (hme : netAddr (GF := GF) = go!"a" ∨ netAddr (GF := GF) = go!"b") :
    ⊢ inv netN (netInv (gooseNetGS (GF := GF)) c0) -∗ |={⊤,∅}=> ∃ (q : DFrac) (ms : GSet NetMsg),
      netAddr (GF := GF) n↦{q} ms ∗
      ∀ m, ⌜m ∈ ms⌝ -∗ netAddr (GF := GF) n↦{q} ms ={∅,⊤}=∗
        ⌜m.sender ≠ go!"c" → m.data = c0⌝ := by
  iintro #Hinv
  iinv Hinv with ⟨%msA, %msB, >Ha, >Hb, >%HA, >%HB⟩ Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  rcases hme with hme | hme <;> rw [hme]
  · iexists (DFrac.own 1), msA
    iframe Ha
    iintro %m %Hm Ha
    imod Hmask
    imod Hclose $$ [Ha Hb]
    · inext; iexists msA, msB; iframe; ipureintro; exact ⟨HA, HB⟩
    imodintro
    ipureintro
    exact HA m Hm
  · iexists (DFrac.own 1), msB
    iframe Hb
    iintro %m %Hm Hb
    imod Hmask
    imod Hclose $$ [Ha Hb]
    · inext; iexists msA, msB; iframe; ipureintro; exact ⟨HA, HB⟩
    imodintro
    ipureintro
    exact HB m Hm

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.netfs

end Perennial
