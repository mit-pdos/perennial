/-
Shared definitions of the proofs of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs`:
its `isPkgInit`, and the protocol of the nodes over the network.

The nodes have addresses `"a"`, `"b"` and `"c"`. The protocol (`netInv`) is an
invariant that owns the messages sent to `"a"` and to `"b"` and says that each
of them carries the data `c0`, the contents of `"a"`'s file `"in"`, unless it
is from `"c"`. `"a"` and `"b"` send only `c0`; `"c"` sends anything, but the
network attaches its address to its messages, so that `"a"` and `"b"`, which
accept messages from each other only, receive only `c0`.

`"b"`'s files follow their own invariant (`bInv`), which owns them, so that a
crash of `"b"` does not lose them: `"sent"` is `"yes"` only once `"out"` holds
`c0` for good, with a persistent witness `outDone γ` of that (`bState`, after
`crashfs`'s `fileState`). This is where durability comes in: after a crash, the
invariant still describes the files, so a boot that finds `"sent"` marked
knows that `"out"` is `c0`.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Base
public import Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.netfs
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std net_ext fs_ext

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

/-- The namespace of the invariant of `"b"`'s files. -/
def outN : Namespace := nroot.@"netfs_out"

end defs

section files
variable [GooseExts] [GooseInterp]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

open Iris.ProofMode

/-- The witness that `"b"`'s file `"out"` holds `c0` for good. -/
abbrev outDone (γ : GName) : IProp GF := dghostVar γ .discard ()

/-- The state of `"b"`'s files `"out"` (contents `so`) and `"sent"` (`ss`): not
done yet, with the ghost variable `γ`, and then `"sent"` is not marked; or done,
`γ` discarded, and then `"out"` is `c0`. -/
abbrev bState (c0 : GoString) (γ : GName) (so ss : GoString) : IProp GF :=
  iprop((dghostVar γ (.own 1) () ∗ ⌜ss ≠ go!"yes"⌝) ∨ (outDone γ ∗ ⌜so = c0⌝))

/-- The invariant of `"b"`'s files, under the files' ghost state `hF`. It owns
the files, so that a crash does not lose them. -/
abbrev bInv (hF : FsGS GF) (c0 : GoString) (γ : GName) : IProp GF :=
  iprop(∃ so ss : GoString, fsPointsto hF go!"out" (.own 1) so ∗
    fsPointsto hF go!"sent" (.own 1) ss ∗ bState c0 γ so ss)

/-- Writing `c0` to `"out"` makes the files done, with the witness. -/
theorem bState_write_out (c0 : GoString) (γ : GName) (so ss : GoString) :
    bState (GF := GF) c0 γ so ss ==∗ outDone γ ∗ bState c0 γ c0 ss := by
  unfold bState
  iintro (⟨Hown, -⟩ | ⟨#Hd, -⟩)
  · imod dghostVar_persist γ 1 () $$ Hown with #Hd
    imodintro
    isplitr
    · iexact Hd
    iright; iframe Hd; ipureintro; rfl
  · imodintro
    isplitr
    · iexact Hd
    iright; iframe Hd; ipureintro; rfl

/-- With the witness, `"out"` is `c0`, and `"sent"` may be marked. -/
theorem bState_done (c0 : GoString) (γ : GName) (so ss ss' : GoString) :
    ⊢@{IProp GF} outDone γ -∗ bState c0 γ so ss -∗ ⌜so = c0⌝ ∗ bState c0 γ so ss' := by
  unfold bState
  iintro #Hd (⟨Hown, -⟩ | ⟨-, %Hso⟩)
  · icases dghostVar_valid_2 γ () (.own 1) () .discard $$ Hown Hd with %H
    exact absurd (DFrac.valid_own_op_discard.mp H.1) (by simp)
  · isplitr
    · ipureintro; exact Hso
    iright; iframe Hd; ipureintro; exact Hso

/-- A reader of `"sent"` learns that, if it is marked, the files are done. -/
theorem bState_read_sent (c0 : GoString) (γ : GName) (so ss : GoString) :
    bState (GF := GF) c0 γ so ss ⊢
      □ (⌜ss = go!"yes"⌝ -∗ outDone γ) ∗ bState c0 γ so ss := by
  unfold bState
  iintro (⟨Hown, %Hss⟩ | ⟨#Hd, %Hso⟩)
  · isplitr
    · iintro !> %h
      exact absurd h Hss
    ileft; iframe Hown; ipureintro; exact Hss
  · isplitr
    · iintro !> _
      iexact Hd
    iright; iframe Hd; ipureintro; exact Hso

/-- If `"sent"` is marked, the files are done: the witness. -/
theorem bState_sent (c0 : GoString) (γ : GName) (so : GoString) :
    bState (GF := GF) c0 γ so go!"yes" ⊢ outDone γ ∗ bState c0 γ so go!"yes" := by
  unfold bState
  iintro (⟨-, %Hss⟩ | ⟨#Hd, %Hso⟩)
  · exact absurd rfl Hss
  · isplitr
    · iexact Hd
    iright; iframe Hd; ipureintro; exact Hso

end files

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

/-- A read of `"sent"` in the invariant of `"b"`'s files: the atomic update of
the read, which learns that the files are done if `"sent"` is marked. -/
theorem bInv_read_sent (c0 : GoString) (γ : GName) :
    ⊢ inv outN (bInv (gooseFsGS (GF := GF)) c0 γ) -∗ |={⊤,∅}=> ∃ (q : DFrac) (ss : GoString),
      go!"sent" fs↦{q} ss ∗ (go!"sent" fs↦{q} ss ={∅,⊤}=∗ □ (⌜ss = go!"yes"⌝ -∗ outDone γ)) := by
  iintro #Hinv
  iinv Hinv with ⟨%so, %ss, >Hout, >Hsent, >Hst⟩ Hclose
  icases bState_read_sent c0 γ so ss $$ Hst with ⟨#Hd, Hst⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (DFrac.own 1), ss
  iframe Hsent
  iintro Hsent
  imod Hmask
  imod Hclose $$ [Hout Hsent Hst]
  · inext; iexists so, ss; iframe
  imodintro
  iexact Hd

/-- A read of `"out"` once the files are done: `c0`. -/
theorem bInv_read_out (c0 : GoString) (γ : GName) :
    ⊢ outDone (GF := GF) γ -∗ inv outN (bInv (gooseFsGS (GF := GF)) c0 γ) -∗
      |={⊤,∅}=> ∃ q : DFrac, go!"out" fs↦{q} c0 ∗ (go!"out" fs↦{q} c0 ={∅,⊤}=∗ emp) := by
  iintro #Hd #Hinv
  iinv Hinv with ⟨%so, %ss, >Hout, >Hsent, >Hst⟩ Hclose
  icases bState_done c0 γ so ss ss $$ Hd Hst with ⟨%Hso, Hst⟩
  rw [Hso]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (DFrac.own 1)
  iframe Hout
  iintro Hout
  imod Hmask
  iapply Hclose
  inext; iexists c0, ss; iframe

/-- The write of `c0` to `"out"`: the files are done, with the witness. -/
theorem bInv_write_out (c0 : GoString) (γ : GName) :
    ⊢ inv outN (bInv (gooseFsGS (GF := GF)) c0 γ) -∗
      |={⊤,∅}=> ∃ old : GoString, go!"out" fs↦ old ∗ (go!"out" fs↦ c0 ={∅,⊤}=∗ outDone γ) := by
  iintro #Hinv
  iinv Hinv with ⟨%so, %ss, >Hout, >Hsent, >Hst⟩ Hclose
  imod bState_write_out c0 γ so ss $$ Hst with ⟨#Hd, Hst⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists so
  iframe Hout
  iintro Hout
  imod Hmask
  imod Hclose $$ [Hout Hsent Hst]
  · inext; iexists c0, ss; iframe
  imodintro
  iexact Hd

/-- The marking of `"sent"`, once the files are done. -/
theorem bInv_write_sent (c0 : GoString) (γ : GName) :
    ⊢ outDone (GF := GF) γ -∗ inv outN (bInv (gooseFsGS (GF := GF)) c0 γ) -∗
      |={⊤,∅}=> ∃ old : GoString, go!"sent" fs↦ old ∗ (go!"sent" fs↦ go!"yes" ={∅,⊤}=∗ emp) := by
  iintro #Hd #Hinv
  iinv Hinv with ⟨%so, %ss, >Hout, >Hsent, >Hst⟩ Hclose
  icases bState_done c0 γ so ss go!"yes" $$ Hd Hst with ⟨%Hso, Hst⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists ss
  iframe Hsent
  iintro Hsent
  imod Hmask
  iapply Hclose
  inext; iexists so, go!"yes"; iframe

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.netfs

end Perennial
