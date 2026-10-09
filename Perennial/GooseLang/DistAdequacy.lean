/-
Adequacy for distributed GooseLang (fail-stop): a system of nodes sharing a
global state, with the semantics of `DistLang.lean`.

Notes:
* Each node runs under its own local ghost state (`GooseLocalGS`); all nodes
  share one `GooseGlobalGS`. The state interpretation of the program logic
  (`gooseBstateInterp`) splits into a node-local part (`gooseLocalInterp`) and
  a global part (`gooseGlobalInterp`: the FFI global state, the prophecy map
  and the fuel); `gooseBstateInterp_split`. A distributed configuration is
  interpreted as the global part together with, for every node, *some* local
  ghost state, the node-local part and WPs for the node's threads
  (`distNodesRes`). A distributed step of node `i` is a thread-pool step of
  that node, so it is justified by iris-lean's `wptp_step` under the node's
  `HeapGS` (`distNodes_step`).
* The WP hypothesis (`distWpInit`) is the fail-stop one: for every node, under
  any local ghost state, from the FFI's local start resources and the initial
  package state, a WP (with any postcondition) for the node's initial thread.
  The global part of the ghost state is allocated first, so the nodes' WPs can
  share resources (invariants, network channels) allocated by the WP
  hypothesis from `ffiGlobalStart`.
* The conclusion (`DistAdequate`) is about real executions of fewer than `N`
  steps, for the time-receipt bound `N` (as for `goose_adequacy`): the fuel of
  the bounded semantics is shared by all nodes.
* The conclusion is only that no thread of any node is stuck: the WP
  hypothesis is `NotStuck`, and the postconditions are arbitrary (and not
  part of the conclusion).
-/
module

public import Perennial.GooseLang.Adequacy
public import Perennial.GooseLang.DistLang

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Language.Notation LawfulSet

attribute [local instance] GSet.lawfulSet

namespace DistGlobal

/-- Fancy updates under a `GooseGlobalGS` alone, without a node's
`GooseLocalGS`: the global part of the distributed adequacy proof (and its WP
hypothesis) has no single `HeapGS`. Scoped (`open scoped Perennial.DistGlobal`)
rather than global, since with a `HeapGS` in scope it is a second path to the
`InvGS` of `goose_irisGS`. -/
scoped instance distGlobalInvGS [FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] : InvGS_gen .hasLC GF :=
  G.gooseInvGS

end DistGlobal

open scoped DistGlobal

section dist_interp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiInterpAdequacy ffi]
variable [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- The node-local part of the GooseLang state interpretation. -/
def gooseLocalInterp [L : GooseLocalGS GF] (σ : state) : IProp GF :=
  iprop(naHeapCtx tls σ.heap ∗
    ffiLocalCtx L.gooseFfiLocalGS σ.world ∗
    ownGoStateCtx σ.goState.packageState ∗
    ⌜σ.goState.goLctx = L.goose_go_local_context⌝)

/-- The global part of the (bounded) GooseLang state interpretation, shared by
all nodes: the FFI global state, the prophecy map and the fuel. -/
def gooseGlobalInterp [G : GooseGlobalGS .hasLC GF] (gf : GlobalState × Nat)
    (κs : List Observation) : IProp GF :=
  iprop(ffiGlobalCtx G.gooseFfiGlobalGS gf.1.globalWorld ∗
    prophMapInterp κs gf.1.usedProphId ∗
    receiptFuel gf.2)

theorem gooseBstateInterp_split [G : GooseGlobalGS .hasLC GF] [L : GooseLocalGS GF]
    (σ : state) (gf : GlobalState × Nat) (κs : List Observation) :
    gooseBstateInterp (GF := GF) (bdistComb σ gf) κs ⊣⊢
      iprop(gooseLocalInterp σ ∗ gooseGlobalInterp gf κs) := by
  unfold gooseBstateInterp gooseStateInterp gooseLocalInterp gooseGlobalInterp
  constructor
  · iintro ⟨⟨Hh, Hl, Hgs, %Hc, Hg, Hp⟩, Hf⟩
    iframe
    ipureintro; exact Hc
  · iintro ⟨⟨Hh, Hl, Hgs, %Hc⟩, Hg, Hp, Hf⟩
    iframe
    ipureintro; exact Hc

/-- The program-logic instance of a node with local ghost state `L`. -/
abbrev distNodeIrisGS (G : GooseGlobalGS .hasLC GF) (L : GooseLocalGS GF) :
    IrisGS_gen .hasLC Expr GF :=
  letI := G; letI := L; inferInstance

/-- A node's resources under local ghost state `L`: the node-local state
interpretation and WPs for its threads. -/
def distNodeRes [G : GooseGlobalGS .hasLC GF] (L : GooseLocalGS GF) (dn : DistNode) :
    IProp GF :=
  iprop(gooseLocalInterp (L := L) dn.localState ∗
    ∃ Φs : List (val → IProp GF),
      wptp (iG := distNodeIrisGS G L) Stuckness.NotStuck dn.tpool Φs)

/-- The resources of all nodes, each under some local ghost state. -/
def distNodesRes [G : GooseGlobalGS .hasLC GF] (dns : List DistNode) : IProp GF :=
  iprop([∗list] dn ∈ dns, ∃ L : GooseLocalGS GF, distNodeRes L dn)

/-- One distributed step preserves the global interpretation and the nodes'
resources. -/
theorem distNodes_step [G : GooseGlobalGS .hasLC GF] {dns₁ dns₂ : List DistNode}
    {gf₁ gf₂ : GlobalState × Nat} {κ κs : List Observation}
    (H : BDistStep (dns₁, gf₁) κ (dns₂, gf₂)) :
    ⊢ gooseGlobalInterp gf₁ (κ ++ κs) -∗ distNodesRes dns₁ -∗ (£ 1 : IProp GF) ={⊤,∅}=∗
      |={∅}▷=>^[1] |={∅,⊤}=> gooseGlobalInterp gf₂ κs ∗ distNodesRes dns₂ := by
  cases H with
  | step hi h =>
  iintro Hg Hnodes Hcred
  unfold distNodesRes distNodeRes
  icases BigSepL.bigSepL_insert_acc hi $$ Hnodes with ⟨⟨%L, Hloc, %Φs, Hwptp⟩, Hclose⟩
  ihave Hσ := (gooseBstateInterp_split (L := L) _ _ (κ ++ κs)).2 $$ [Hloc Hg]
  · iframe
  icases wptp_step (iG := distNodeIrisGS G L) Stuckness.NotStuck _ _ κ κs _ _ 0 Φs 0 h
    $$ Hσ Hcred Hwptp with ⟨%nt', Hstep⟩
  imod Hstep
  imodintro
  iapply step_fupdN_wand $$ Hstep
  iintro >⟨Hσ, Hwptp⟩
  icases (gooseBstateInterp_split (L := L) _ _ κs).1 $$ Hσ with ⟨Hloc, Hg⟩
  imodintro
  iframe Hg
  iapply Hclose
  iexists L
  iframe Hloc
  iexists _
  iexact Hwptp

/-- `n` distributed steps preserve the global interpretation and the nodes'
resources, at the cost of `n` laters and `n` later credits. -/
theorem distNodes_steps [G : GooseGlobalGS .hasLC GF] {n : Nat} {dns₁ dns₂ : List DistNode}
    {gf₁ gf₂ : GlobalState × Nat} {κs κs' : List Observation}
    (H : BDistNsteps n (dns₁, gf₁) κs (dns₂, gf₂)) :
    ⊢ gooseGlobalInterp gf₁ (κs ++ κs') -∗ distNodesRes dns₁ -∗ (£ n : IProp GF) ={⊤,∅}=∗
      |={∅}▷=>^[n] |={∅,⊤}=> gooseGlobalInterp gf₂ κs' ∗ distNodesRes dns₂ := by
  generalize hρ1 : (dns₁, gf₁) = ρ1 at H
  generalize hρ2 : (dns₂, gf₂) = ρ2 at H
  induction H generalizing κs' dns₁ gf₁ dns₂ gf₂ with
  | refl ρ =>
    cases hρ1; cases hρ2
    simp only [List.nil_append, step_fupdN]
    iintro Hg Hnodes _
    iapply fupd_mask_intro empty_subset
    iintro Hcl; imod Hcl; imodintro
    iframe
  | @cons n_inner ρ1' ρ_mid ρ2' obs obs' hstep hrest ih =>
    cases hρ1; cases hρ2
    obtain ⟨dns_mid, gf_mid⟩ := ρ_mid
    rw [List.append_assoc obs obs' κs', show n_inner + 1 = 1 + n_inner by omega, step_fupdN_add.to_eq]
    iintro Hg Hnodes ⟨Hcred1, Hcred2⟩
    imod distNodes_step (κs := obs' ++ κs') hstep $$ Hg Hnodes Hcred1 with Hstep
    imodintro
    iapply step_fupdN_S_fupd.2
    iapply step_fupdN_wand $$ Hstep
    iintro >⟨Hg, Hnodes⟩
    imod ih rfl rfl $$ Hg Hnodes Hcred2 with Hih
    imodintro
    iexact Hih

/-- The fail-stop WP hypothesis for one node running `e` in initial local state
`σ`, under local ghost state `L`: from the FFI's local start resources and the
initial package state, a WP for `e`. -/
def distNodeWp [G : GooseGlobalGS .hasLC GF] (L : GooseLocalGS GF) (e : Expr) (σ : state) :
    IProp GF :=
  letI : HeapGS .hasLC GF := ⟨G, L⟩
  iprop(ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
    ownGoState σ.goState.packageState ={⊤}=∗
    ∃ Φ : val → IProp GF, WP e @ Stuckness.NotStuck; ⊤ {{ Φ }})

/-- The fail-stop WP hypothesis for a distributed system: for every node, under
any local ghost state (whose Go local context is the node's), `distNodeWp`. -/
def distWpInit [G : GooseGlobalGS .hasLC GF] (ebσs : List (Expr × state)) : IProp GF :=
  iprop([∗list] ebσ ∈ ebσs, ∀ L : GooseLocalGS GF,
    ⌜L.goose_go_local_context = ebσ.2.goState.goLctx⌝ -∗ distNodeWp (GF := GF) L ebσ.1 ebσ.2)

/-- Allocate every node's local ghost state and obtain the initial nodes'
resources from the WP hypothesis. -/
theorem distNodes_init [hPre : GooseGpreS ffi GF] [G : GooseGlobalGS .hasLC GF]
    (ebσs : List (Expr × state)) (gw : ffi_global_state)
    (Hinit : ∀ ebσ, ebσ ∈ ebσs → ffi_initP ebσ.2.world gw) :
    distWpInit (GF := GF) ebσs ⊢
      |={⊤}=> distNodesRes (ebσs.map fun ebσ => DistNode.init ebσ.1 ebσ.2) := by
  unfold distWpInit distNodesRes
  induction ebσs with
  | nil =>
    iintro -
    imodintro
    simp only [List.map_nil]
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | cons ebσ ebσs ih =>
    obtain ⟨e, σ⟩ := ebσ
    simp only [List.map_cons]
    iintro ⟨Hhd, Htl⟩
    imod ih (fun x hx => Hinit x (List.mem_cons_of_mem _ hx)) $$ Htl with Htl
    imod na_heap_init (L := Loc) (V := val)
      (hG := ⟨hPre.goose_preG_heap.na_heap_preG_inG, default⟩) tls σ.heap with ⟨%hHeap, Hh⟩
    imod goState_init hPre.goose_preG_go_state σ.goState.packageState with ⟨%γ, Hgs, Hgs'⟩
    imod ffi_local_init GF hPre.goosePreGFfi σ.world gw (Hinit _ List.mem_cons_self)
      with ⟨%hFL, Hlctx, Hlstart⟩
    let L : GooseLocalGS GF :=
      ⟨hFL, σ.goState.goLctx, hHeap, goStateGSUpdatePre GF hPre.goose_preG_go_state γ⟩
    unfold distNodeWp
    imod Hhd $$ %L [] Hlstart Hgs' with ⟨%Φ, Hwp⟩
    · ipureintro; rfl
    imodintro
    iframe Htl
    iexists L
    unfold distNodeRes gooseLocalInterp
    iframe
    isplitr
    · ipureintro; rfl
    iexists [Φ]
    iapply BigSepL2.bigSepL2_singleton
    iexact Hwp

end dist_interp

section adequacy
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiInterpAdequacy ffi]
variable [FfiSemantics ext ffi] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- The soundness argument for distributed GooseLang (bounded semantics): given
the WP hypothesis, for any `n`-step execution of the bounded distributed
semantics started with fuel `N - 1`, a pure `φ` follows if it follows (in the
logic, opening all invariants) from the final global interpretation and nodes'
resources, together with the resources `Q` that the WP hypothesis set aside. -/
theorem goose_dist_soundness [hPre : GooseGpreS ffi GF] (N : Nat) (hN : 0 < N)
    (ebσs : List (Expr × state)) (g : GlobalState)
    (Hinitg : ffi_initgP g.globalWorld)
    (Hinit : ∀ ebσ, ebσ ∈ ebσs → ffi_initP ebσ.2.world g.globalWorld)
    (Q : GooseGlobalGS .hasLC GF → IProp GF)
    (Hwp : ∀ [G : GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld ={⊤}=∗
        distWpInit ebσs ∗ Q G)
    {n : Nat} {κs : List Observation} {dns : List DistNode} {gf : GlobalState × Nat}
    (Hsteps : BDistNsteps n ((startingDistCfg ebσs g).1, (g, N - 1)) κs (dns, gf))
    (φ : Prop)
    (Hfin : ∀ [G : GooseGlobalGS .hasLC GF],
      ⊢ Q G -∗ gooseGlobalInterp gf [] -∗ distNodesRes dns ={⊤,∅}=∗ ⌜φ⌝) :
    φ := by
  unfold startingDistCfg at Hsteps
  apply pure_soundness (PROP := IProp GF)
  apply laterN_soundness (n := n + 1)
  rw [(laterN_succ_right _).to_eq]
  refine Entails.trans ?_ (laterN_mono _ except0_into_later)
  apply fupd_finally_soundness .hasLC n ⊤
  iintro %Hinv Hf
  imod ProphMap.init (H := GMap proph_id) (V := val) κs g.usedProphId with ⟨%hProph, Hp⟩
  imod ffi_global_init GF hPre.goosePreGFfi g.globalWorld Hinitg with ⟨%hFG, Hgctx, Hgstart⟩
  imod receipt_init (hPre := hPre.goose_preG_receipt) N hN with ⟨%γR, %γL, HR⟩
  let G : GooseGlobalGS .hasLC GF :=
    ⟨Hinv, hProph, hFG, ⟨hPre.goose_preG_receipt.receiptPreGAllG, γR, γL, N, hN⟩⟩
  imod (@Hwp G rfl) $$ Hgstart with ⟨Hnodes, HQ⟩
  imod distNodes_init (G := G) ebσs g.globalWorld Hinit $$ Hnodes with Hnodes
  imod distNodes_steps (G := G) (κs' := []) Hsteps $$ [Hgctx Hp HR] Hnodes Hf with H
  · rw [List.append_nil]
    unfold gooseGlobalInterp
    iframe
  iapply step_fupdN_fupd_finally
  iapply step_fupdN_wand $$ H
  iintro >⟨Hg, Hnodes⟩
  imod (@Hfin G) $$ HQ Hg Hnodes with %Hφ
  ipureintro; exact Hφ

/-- Adequacy of distributed GooseLang (fail-stop), for the real semantics,
under the time-receipt assumption: for any bound `N`, if, for any global ghost
state with receipt bound `N`, the FFI's global start resources yield the WP
hypothesis `distWpInit` for every node, then in every real distributed
execution of fewer than `N` steps no thread of any node is stuck. -/
theorem goose_dist_adequacy [hPre : GooseGpreS ffi GF] (N : Nat)
    (ebσs : List (Expr × state)) (g : GlobalState)
    (Hinitg : ffi_initgP g.globalWorld)
    (Hinit : ∀ ebσ, ebσ ∈ ebσs → ffi_initP ebσ.2.world g.globalWorld)
    (Hwp : ∀ [GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld ={⊤}=∗
        distWpInit ebσs) :
    DistAdequate N ebσs g := by
  constructor
  · intro n κs dns g' dn Hsteps hn hdn e he
    obtain ⟨f', Hb⟩ := bounded_distNsteps_of_real Hsteps (N - 1) (by omega)
    apply realNotStuck_of_bounded (f := f')
    refine goose_dist_soundness (GF := GF) N (by omega) ebσs g Hinitg Hinit (fun _ => iprop(True)) ?_ Hb
      _ ?_
    · intro G hN
      iintro H
      imod Hwp hN $$ H with H
      imodintro
      iframe
    · intro G
      iintro - Hg Hnodes
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hdn
      obtain ⟨j, hj⟩ := List.getElem?_of_mem he
      unfold distNodesRes distNodeRes
      icases BigSepL.bigSepL_lookup hi $$ Hnodes with ⟨%L, Hloc, %Φs, Hwptp⟩
      icases BigSepL2.bigSepL2_lookup_left hj $$ Hwptp with ⟨%Φ, %_, Hwp⟩
      ihave Hσ := (gooseBstateInterp_split (L := L) dn.localState (g', f') []).2 $$ [Hloc Hg]
      · iframe
      iapply wp_not_stuck (iG := distNodeIrisGS G L) [] 0 e _ 0 Φ $$ Hσ Hwp

end adequacy

end Perennial
