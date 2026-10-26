/-
The end-to-end result of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs`:
the distributed crash safety of the three-node system, on the network and the
filesystem.

The nodes have addresses `"a"`, `"b"` and `"c"` (their local network states)
and the boot programs `boot NodeA`, `boot NodeB` and `boot NodeC` (initialize
the package, then call the node's function), which run at the start and after
every crash of the node. The precondition of a node's boot program, over the
local ghost state `L` of a generation of the node (`nodePre`), is the protocol's
invariant (`netInv`, `Base.lean`), the node's package state, its address, and
what it knows of its files under `L`'s files' ghost state: `"a"`'s file `"in"`
holds `c0` for good (a persistent points-to); `"b"`'s files follow their
invariant (`bInv`). The global setup allocates the protocol's invariant from
the network's points-to of `"a"` and `"b"`; each node's first generation
establishes its precondition from its start resources (`"b"` allocates the
invariant of its files). Every generation's proof guarantees the precondition
of the next one after a crash: the files' and the address's ghost state are
the crashed generation's (`fsNet_crashStart`), so the same invariants and
persistent points-to hold.

The conclusion, `netfs_crash_safety`, mentions no ghost state and no bounds: in
every execution of the system with crashes, no thread of any node is stuck and
none has an unrecovered panic, so `NodeA`'s check (the round trip returns
`c0`) never fails, however often any node crashes.
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
  fsNetExts_hasNet fsNetExtsCrashInterp

/- The global setup of `goose_dist_adequacy` is under the global ghost state
alone, whose invariants are those of the fancy updates. -/
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The boot program of a node: initialize the package, then call the package's
function `f` (as goose calls a function: resolve it, then apply it). -/
def boot [GoGlobalContext] (f : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve f []))) (Val #())) (Val #()))

/-- The system: the nodes have the boot programs `boot NodeA`, `boot NodeB` and
`boot NodeC`, and start from the local states `σa`, `σb` and `σc`. -/
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

/-- The address of node `i` of the system. -/
def nodeAddr : Nat → GoString
  | 0 => go!"a"
  | 1 => go!"b"
  | _ => go!"c"

/-- What node `i` knows of its files, under the files' ghost state `hF`. -/
def nodeFiles [G : GooseGlobalGS .hasLC GF] (hF : FsGS GF) (c0 : GoString) (i : Nat) : IProp GF :=
  if i = 0 then fsPointsto hF go!"in" .discard c0
  else if i = 1 then iprop(∃ γ, inv outN (bInv hF c0 γ))
  else iprop(True)

instance nodeFiles_persistent [G : GooseGlobalGS .hasLC GF] (hF : FsGS GF) (c0 : GoString)
    (i : Nat) : Persistent (nodeFiles hF c0 i) := by
  unfold nodeFiles
  split
  · infer_instance
  · split <;> infer_instance

/-- The precondition of node `i`'s boot program in the generation with local
ghost state `L`: the protocol, a fresh package state, the node's address and
what it knows of its files. -/
def nodePre [G : GooseGlobalGS .hasLC GF] (c0 : GoString) (i : Nat) (L : GooseLocalGS GF) :
    IProp GF :=
  iprop(inv netN (netInv (extGlobalGS netExt) c0) ∗ ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ⌜(extLocalGS netExt (L := L) : NetNodeGS GF).addr = nodeAddr i⌝ ∗
    nodeFiles (extLocalGS fsExt (L := L)) c0 i)

/-- `netfs_crash_safety` for executions of fewer than `N` steps along which every
node has fewer than `T` live threads, under any ghost state `GF` with
`GooseGpreS GF`: `goose_dist_crash_adequacy` for the system. -/
theorem netfs_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions]
    [hPre : GooseGpreS GF] (N T : Nat) (σa σb σc : state) (g : GlobalState) (c0 old : GoString)
    (Ha : NodeStart lctx σa go!"a") (Hb : NodeStart lctx σb go!"b") (Hc : NodeStart lctx σc go!"c")
    (Hin : extLocal fsExt σa.world !! go!"in" = some c0)
    (Hout : extLocal fsExt σb.world !! go!"out" = some old)
    (Hsent : extLocal fsExt σb.world !! go!"sent" = some go!"")
    (Hneta : extGlobal netExt g.globalWorld !! go!"a" = some ∅)
    (Hnetb : extGlobal netExt g.globalWorld !! go!"b" = some ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps ((system σa σb σc).map Prod.fst) n
      (distInit (system σa σb σc) g) κs c)
    (Hbound : n < N)
    (Hlive : DistCrashThreadsBelow ((system σa σb σc).map Prod.fst) T n
      (distInit (system σa σb σc) g)) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) := by
  refine goose_dist_crash_adequacy (GF := GF) N T (system σa σb σc) g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨trivial, trivial, trivial⟩
    (fun _ _ => ⟨trivial, trivial, trivial⟩) (fun i L => nodePre c0 i L) ?_ ?_
    n κs c Hsteps Hbound ?_ Hlive
  · -- the global setup and the first generation of every node
    intro G _
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
    unfold nodeStart
    isplitl []
    · -- `"a"`: the file `"in"` holds `c0` for good
      iintro %L %_ %_ Hstart Hgs
      icases fsNet_localStart (L := L) σa.world $$ Hstart with ⟨Hfiles, %Haddr⟩
      icases (BigSepM.bigSepM_lookup (Φ := fun f c => fsPointsto (extLocalGS fsExt (L := L)) f
        (DFrac.own 1) c) Hin) $$ Hfiles with Hf
      imod fsPointsto_persist (L := L) go!"in" (DFrac.own 1) c0 $$ Hf with #Hf
      rw [Ha.packageState]
      imodintro
      unfold nodePre
      isplitl []
      · iexact Hinv
      isplitl [Hgs]
      · iexact Hgs
      isplitr
      · ipureintro; exact Haddr.trans Ha.addr
      simp only [nodeFiles, ↓reduceIte]
      iexact Hf
    isplitl []
    · -- `"b"`: the invariant of its files, not done yet
      iintro %L %_ %_ Hstart Hgs
      icases fsNet_localStart (L := L) σb.world $$ Hstart with ⟨Hfiles, %Haddr⟩
      icases (BigSepM.bigSepM_delete Hout).1 $$ Hfiles with ⟨Ho, Hfiles⟩
      have Hsent' : PartialMap.get? (PartialMap.delete (extLocal fsExt σb.world) go!"out")
          go!"sent" = some go!"" := by
        rw [LawfulPartialMap.get?_delete_ne (by decide)]; exact Hsent
      icases (BigSepM.bigSepM_delete Hsent').1 $$ Hfiles with ⟨Hs, -⟩
      letI hG : HeapGS .hasLC GF := ⟨G, L⟩
      imod dghostVar_alloc (GF := GF) () with ⟨%γ, Hown⟩
      imod inv_alloc outN ⊤ (bInv (extLocalGS fsExt (L := L)) c0 γ) $$ [Ho Hs Hown] with #Hb
      · inext
        iexists old, go!""
        iframe Ho Hs
        ileft
        iframe Hown
        ipureintro; decide
      rw [Hb.packageState]
      imodintro
      unfold nodePre
      isplitl []
      · iexact Hinv
      isplitl [Hgs]
      · iexact Hgs
      isplitr
      · ipureintro; exact Haddr.trans Hb.addr
      simp only [nodeFiles, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iexists γ
      iexact Hb
    isplitl []
    · -- `"c"`
      iintro %L %_ %_ Hstart Hgs
      icases fsNet_localStart (L := L) σc.world $$ Hstart with ⟨-, %Haddr⟩
      rw [Hc.packageState]
      imodintro
      unfold nodePre
      isplitl []
      · iexact Hinv
      isplitl [Hgs]
      · iexact Hgs
      isplitr
      · ipureintro; exact Haddr.trans Hc.addr
      simp only [nodeFiles, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      itrivial
    iempintro
  · -- every generation of every node: its boot program, and its next precondition
    intro hG _ _ i e σ Hes Hlctx
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    have Hnode : (i = 0 ∧ e = boot NodeA ∧ σ = σa) ∨ (i = 1 ∧ e = boot NodeB ∧ σ = σb) ∨
        (i = 2 ∧ e = boot NodeC ∧ σ = σc) := by
      match i, Hes with
      | 0, Hes => cases Hes; exact .inl ⟨rfl, rfl, rfl⟩
      | 1, Hes => cases Hes; exact .inr (.inl ⟨rfl, rfl, rfl⟩)
      | 2, Hes => cases Hes; exact .inr (.inr ⟨rfl, rfl, rfl⟩)
    have Hl : σ.goState.goLctx = lctx := by
      rcases Hnode with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · exact Ha.goLctx
      · exact Hb.goLctx
      · exact Hc.goLctx
    rw [Hl] at Hlctx
    subst Hlctx
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold nodePre
    iintro ⟨#Hinv, Hgs, %Haddr, #Hf⟩ _
    imodintro
    isplitl [Hgs]
    · rcases Hnode with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · iapply wp_boot NodeA _ (wp_NodeA (GF := GF) c0 Haddr) $$ [] Hgs
        isplitl []
        · iexact Hinv
        · simp only [nodeFiles, ↓reduceIte]; iexact Hf
      · simp only [nodeFiles, Nat.reduceEqDiff, ↓reduceIte]
        icases Hf with ⟨%γ, #Hb⟩
        iapply wp_boot NodeB _ (wp_NodeB (GF := GF) c0 γ Haddr) $$ [] Hgs
        isplitl []
        · iexact Hinv
        · iexact Hb
      · iapply wp_boot NodeC _ (wp_NodeC (GF := GF) c0 Haddr) $$ [] Hgs
        iexact Hinv
    · -- after a crash: the files' and the address's ghost state are kept
      iintro %L' _ Hcs Hgs'
      icases fsNet_crashStart _ L' $$ Hcs with ⟨%Hfs, %Hnet⟩
      imodintro
      iframe Hinv Hgs'
      rw [Hfs, Hnet]
      isplitr
      · ipureintro; exact Haddr
      iexact Hf
  · intro n hn
    simp only [system, List.mem_cons, List.not_mem_nil, _root_.or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact Ha.threads
    · exact Hb.threads
    · exact Hc.threads

/-- Crash safety of the system: in every execution with crashes of the three
nodes (`DistCrashNsteps`, the real semantics: a crash of a node restarts it
with its boot program, from a crashed local state), from local states whose Go
contexts satisfy the Go semantics and the package's assumptions, with no
package initialized, their main threads only and the addresses `"a"`, `"b"`
and `"c"`, where `"a"`'s file `"in"` holds `c0`, `"b"`'s file `"out"` exists
and its file `"sent"` is empty, and where the network has entries for `"a"`
and `"b"` without messages (an entry, not just no messages: the network's
start resources are the points-to of its entries), every boot program returns
`#()` if it returns, no thread of any node is stuck and none has an
unrecovered panic: `NodeA`'s check holds, however the network delays,
duplicates, reorders or loses messages, whatever `"c"` sends, and however
often any node crashes. (`netfs_crash_safety_bounded` with the ghost state
`fsNetGF`, the step bound `n + 1` and the thread bound `n + 2`, which an
execution of `n` steps from single threads respects,
`DistCrashThreadsBelow.of_single`.) -/
theorem netfs_crash_safety [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions]
    (σa σb σc : state) (g : GlobalState) (c0 old : GoString)
    (Ha : NodeStart lctx σa go!"a") (Hb : NodeStart lctx σb go!"b") (Hc : NodeStart lctx σc go!"c")
    (Hin : extLocal fsExt σa.world !! go!"in" = some c0)
    (Hout : extLocal fsExt σb.world !! go!"out" = some old)
    (Hsent : extLocal fsExt σb.world !! go!"sent" = some go!"")
    (Hneta : extGlobal netExt g.globalWorld !! go!"a" = some ∅)
    (Hnetb : extGlobal netExt g.globalWorld !! go!"b" = some ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps ((system σa σb σc).map Prod.fst) n
      (distInit (system σa σb σc) g) κs c) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) :=
  netfs_crash_safety_bounded (GF := fsNetGF) (n + 1) (n + 2) σa σb σc g c0 old Ha Hb Hc Hin Hout
    Hsent Hneta Hnetb n κs c Hsteps (by omega)
    (DistCrashThreadsBelow.of_single (fun (i : Nat) (tp : List Expr) (σ : state) hi => by
      simp only [distInit, system, List.map_cons, List.map_nil] at hi
      match i, hi with
      | 0, hi => cases hi; exact Ha.threads
      | 1, hi => cases hi; exact Hb.threads
      | 2, hi => cases hi; exact Hc.threads))

end adequacy

end github_com.mit_pdos.perennial.goose.testdata.examples.netfs

end Perennial
