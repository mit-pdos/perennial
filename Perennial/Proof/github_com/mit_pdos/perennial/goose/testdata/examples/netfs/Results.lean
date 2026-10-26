/-
The end-to-end result of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs`:
the distributed adequacy of the three-node system, on the network and the
filesystem.

The nodes have addresses `"a"`, `"b"` and `"c"` (their local network states),
and run `boot NodeA`, `boot NodeB` and `boot NodeC`: initialize the package,
then call the node's function. The global setup of the proof allocates the
protocol's invariant (`netInv`, `Base.lean`) from the network's points-to of
`"a"` and `"b"`, initially without messages; each node then proves its boot
program with the standard WP from its start resources: `"a"` its file `"in"`
(contents `c0`), `"b"` its file `"out"`. The conclusion, `netfs_safety`, mentions
no ghost state and no bounds: in every execution of the system, no thread of
any node is stuck and none has an unrecovered panic, so the checks of `NodeA`
(the round trip returns `c0`) and `NodeB` (the write is kept) never fail.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.Link
public import Perennial.GooseLang.Ext.Net.Adequacy

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode fs_ext net_ext

namespace github_com.mit_pdos.perennial.goose.testdata.examples.netfs

attribute [local instance] fsNetExts fsNetExtsSemantics fsNetExtsInterp fsNetExts_hasFs
  fsNetExts_hasNet

/- The global setup of `goose_dist_adequacy` is under the global ghost state
alone, whose invariants are those of the fancy updates. -/
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The boot program of a node: initialize the package, then call the package's
function `f` (as goose calls a function: resolve it, then apply it). -/
def boot [GoGlobalContext] (f : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve f []))) (Val #())) (Val #()))

/-- The system: the nodes run `NodeA`, `NodeB` and `NodeC` from the local states
`σa`, `σb` and `σc`. -/
def system [GoGlobalContext] (σa σb σc : state) : List (Expr × state) :=
  [(boot NodeA, σa), (boot NodeB, σb), (boot NodeC, σc)]

/-- A node's initial local state: its Go context is `lctx`, no package is
initialized, it has its main thread only, and its address is `addr`. -/
structure NodeStart [GoGlobalContext] (lctx : GoLocalContext) (σ : state) (addr : GoString) : Prop where
  goLctx : σ.goState.goLctx = lctx
  packageState : σ.goState.packageState = ∅
  threads : σ.threads = 1
  addr : extLocal netExt σ.world = addr

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The `get_is_pkg_init` of a boot program: the package, `fsext` and `netext`. -/
def getIsPkgInit [HeapGS .hasLC GF] (p : GoString) : IProp GF :=
  if p = pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs then
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs
  else if p = pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext then
    isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext
  else if p = pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext then
    isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext
  else iprop(True)

/-- A boot program, from a spec of its function `f` with precondition `P` (and
the package initialized). -/
theorem wp_boot [hG : HeapGS .hasLC GF] [sem : go.Semantics] [package_sem : Assumptions] (f : GoString) (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF)
          pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs ∗ P }}
        (App (Val (@! f)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP (boot f) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  have Hne₁ : pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext ≠
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs := by
    unfold pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs
    decide
  have Hne₂ : pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext ≠
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs := by
    unfold pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs
    decide
  have Hne₃ : pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext ≠
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext := by
    unfold pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext
    decide
  have Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs
      (getIsPkgInit (GF := GF)) := by
    refine ⟨by simp [getIsPkgInit], ⟨by simp [getIsPkgInit, Hne₁], trivial⟩,
      ⟨by simp [getIsPkgInit, Hne₂, Hne₃], trivial⟩, trivial⟩
  iintro HP Hgs
  unfold boot
  wp_apply wp_initialize' getIsPkgInit Hinit $$ [Hgs] as ⟨_, #Hpkg⟩
  · -- no package is initialized
    rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  wp_pures
  wp_apply Hf $$ [HP]
  · iframe
  ipureintro; rfl

/-- `netfs_safety` for executions of fewer than `N` steps along which every node
has fewer than `T` live threads, under any ghost state `GF` with `GooseGpreS GF`:
`goose_dist_adequacy` for the system. -/
theorem netfs_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [hPre : GooseGpreS GF] (N T : Nat) (σa σb σc : state) (g : GlobalState) (c0 old : GoString)
    (Ha : NodeStart lctx σa go!"a") (Hb : NodeStart lctx σb go!"b") (Hc : NodeStart lctx σc go!"c")
    (Hin : extLocal fsExt σa.world !! go!"in" = some c0)
    (Hout : extLocal fsExt σb.world !! go!"out" = some old)
    (Hneta : extGlobal netExt g.globalWorld !! go!"a" = some ∅)
    (Hnetb : extGlobal netExt g.globalWorld !! go!"b" = some ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistNsteps n (distInit (system σa σb σc) g) κs c)
    (Hbound : n < N) (Hlive : DistThreadsBelow T n (distInit (system σa σb σc) g)) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) := by
  refine goose_dist_adequacy (GF := GF) N T (system σa σb σc) g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨trivial, trivial, trivial⟩
    (fun _ _ => ⟨trivial, trivial, trivial⟩) ?_ n κs c Hsteps Hbound ?_ Hlive
  · intro G _
    iintro Hg
    -- the protocol, from the network's points-to of `"a"` and `"b"`
    icases fsNet_globalStart g.globalWorld $$ Hg with Hnet
    icases (BigSepM.bigSepM_delete Hneta).1 $$ Hnet with ⟨Hna, Hnet⟩
    have Hnetb' : PartialMap.get? (PartialMap.delete (extGlobal netExt g.globalWorld) go!"a")
        go!"b" = some ∅ := by
      rw [LawfulPartialMap.get?_delete_ne (by decide)]; exact Hnetb
    icases (BigSepM.bigSepM_delete Hnetb').1 $$ Hnet with ⟨Hnb, -⟩
    imod inv_alloc netN ⊤ (netInv (extGlobalGS netExt) c0) $$ [Hna Hnb] with #Hinv
    · inext
      iexists ∅, ∅
      iframe Hna Hnb
      ipureintro
      exact ⟨goodMsgs_empty c0, goodMsgs_empty c0⟩
    imodintro
    simp only [system]
    unfold nodeWp nodeWpBody
    isplitl [Hinv]
    · -- `"a"`
      iintro %L %_ %Hlctx Hstart Hgs _
      rw [Ha.goLctx] at Hlctx
      obtain ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩ := L
      subst Hlctx
      letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
      icases fsNet_localStart (L := hG.goose_localGS) σa.world $$ Hstart with ⟨Hfiles, %Haddr⟩
      icases (BigSepM.bigSepM_lookup (Φ := fun f c => (f fs↦ c : IProp GF)) Hin) $$ Hfiles with Hf
      rw [Ha.packageState]
      imodintro
      iapply wp_boot NodeA _ (wp_NodeA (GF := GF) c0 (Haddr.trans Ha.addr)) $$ [Hf] Hgs
      isplitl []
      · iexact Hinv
      · iexact Hf
    isplitl [Hinv]
    · -- `"b"`
      iintro %L %_ %Hlctx Hstart Hgs _
      rw [Hb.goLctx] at Hlctx
      obtain ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩ := L
      subst Hlctx
      letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
      icases fsNet_localStart (L := hG.goose_localGS) σb.world $$ Hstart with ⟨Hfiles, %Haddr⟩
      icases (BigSepM.bigSepM_lookup (Φ := fun f c => (f fs↦ c : IProp GF)) Hout) $$ Hfiles with Hf
      rw [Hb.packageState]
      imodintro
      iapply wp_boot NodeB _ (wp_NodeB (GF := GF) c0 old (Haddr.trans Hb.addr)) $$ [Hf] Hgs
      isplitl []
      · iexact Hinv
      · iexact Hf
    isplitl [Hinv]
    · -- `"c"`
      iintro %L %_ %Hlctx Hstart Hgs _
      rw [Hc.goLctx] at Hlctx
      obtain ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩ := L
      subst Hlctx
      letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
      icases fsNet_localStart (L := hG.goose_localGS) σc.world $$ Hstart with ⟨-, %Haddr⟩
      rw [Hc.packageState]
      imodintro
      iapply wp_boot NodeC _ (wp_NodeC (GF := GF) c0 (Haddr.trans Hc.addr)) $$ [] Hgs
      iexact Hinv
    iempintro
  · intro n hn
    simp only [system, List.mem_cons, List.not_mem_nil, _root_.or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact Ha.threads
    · exact Hb.threads
    · exact Hc.threads

/-- Safety of the system: in every execution of the three nodes (`DistNsteps`,
the real semantics), from local states whose Go contexts satisfy the Go
semantics and the package's assumptions, with no package initialized, their
main threads only and the addresses `"a"`, `"b"` and `"c"`, where `"a"`'s file
`"in"` holds `c0` and `"b"`'s file `"out"` exists, and where no message has
been sent to `"a"` or `"b"` yet, every node's boot program returns `#()` if it
returns, no thread of any node is stuck and none has an unrecovered panic: the
checks of `NodeA` and `NodeB` hold, however the network delays, duplicates,
reorders or loses messages and whatever `"c"` sends. (`netfs_safety_bounded`
with the ghost state `fsNetGF`, the step bound `n + 1` and the thread bound
`n + 2`, which an execution of `n` steps from single threads respects,
`DistThreadsBelow.of_single`.) -/
theorem netfs_safety [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    (σa σb σc : state) (g : GlobalState) (c0 old : GoString)
    (Ha : NodeStart lctx σa go!"a") (Hb : NodeStart lctx σb go!"b") (Hc : NodeStart lctx σc go!"c")
    (Hin : extLocal fsExt σa.world !! go!"in" = some c0)
    (Hout : extLocal fsExt σb.world !! go!"out" = some old)
    (Hneta : extGlobal netExt g.globalWorld !! go!"a" = some ∅)
    (Hnetb : extGlobal netExt g.globalWorld !! go!"b" = some ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistNsteps n (distInit (system σa σb σc) g) κs c) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) :=
  netfs_safety_bounded (GF := fsNetGF) (n + 1) (n + 2) σa σb σc g c0 old Ha Hb Hc Hin Hout
    Hneta Hnetb n κs c Hsteps (by omega)
    (DistThreadsBelow.of_single (fun (i : Nat) (tp : List Expr) (σ : state) hi => by
      simp only [distInit, system, List.map_cons, List.map_nil] at hi
      match i, hi with
      | 0, hi => cases hi; exact Ha.threads
      | 1, hi => cases hi; exact Hb.threads
      | 2, hi => cases hi; exact Hc.threads))

end adequacy

end github_com.mit_pdos.perennial.goose.testdata.examples.netfs

end Perennial
