/-
Adequacy for distributed GooseLang programs: the adequacy of the standard
(iris-lean) WP for executions of a distributed system, without crashes
(`DistNsteps`, `goose_dist_adequacy`) and with crashes of the nodes
(`DistCrashNsteps`, `goose_dist_crash_adequacy`), `DistLang.lean`.

Notes:
* A distributed system is a list of nodes, each running its own program on its
  own local state, sharing the global state. Each node's program is proved
  with the standard WP, as a single-node program is; there is no distributed
  program logic. All the nodes are one Iris proof: they share the global ghost
  state (`GooseGlobalGS`: invariants, the prophecy map, the extensions' global
  ghost state, time receipts), and each has its own local ghost state
  (`GooseLocalGS`: heap, package state, extensions' local ghost state, thread
  tokens), allocated by the adequacy theorem.
* The client proves `Hwp`: for any global ghost state `G` with receipt bound
  `N`, from the extensions' global start resources (e.g. the ownership of the
  network), a fancy update to the proof obligations of the nodes,
  `nodeWp T e σ φ` for the node running `e` from `σ`: for any local ghost state
  of the node (thread bound `T`, the node's Go context), from the node's start
  resources (the extensions' local start resources, e.g. its files, its package
  state and its main thread's token), the WP of `e` with postcondition `φ`. The
  fancy update lets the client allocate the invariants that the nodes share
  (e.g. a protocol over the network) before splitting the resources among the
  nodes.
* The state interpretation of a node's WP is that of a single-node program,
  `gooseBstateInterp` at the node's local state and the global state; it splits
  into the node's part (`nodeInterp`) and the global part (`globalInterp`). The
  invariant of the adequacy proof (`distInv`) owns the global part once and, for
  each node, its part and the WPs of its threads, under its local ghost state.
  A step of node `i` reassembles node `i`'s state interpretation and takes the
  step with iris-lean's `wptp_step` (`dist_step`); the other nodes are framed.
* Time receipts bound the steps of all nodes together (the step fuel is
  global); thread tokens are per node (each node has its own thread fuel and
  bound `T`). The theorem is about executions of fewer than `N` steps in all
  along which every node has fewer than `T` live threads (`DistThreadsBelow`).
* Crashes (`goose_dist_crash_adequacy`): a node has one program, its boot
  program, run at the start and after every crash of the node; there is no
  separate recovery procedure. As for `goose_crash_adequacy` (one node), the
  client picks the precondition `P i L` of node `i`'s boot program over the
  local ghost state `L` of a generation of the node. `Hstart` is the global
  setup and every node's first `P i`; `Hwp` proves, in every generation, the
  WP of the boot program from `P i` together with `P i L'` for the generation
  `L'` after a crash, from `crashed` and the extensions' `crashStart`. In the
  invariant, each node carries that guarantee as its frame (`crashFrame`); a
  crash of node `i` (`dist_crash_node`) runs `goose_crash_step` on node `i`'s
  part of the state interpretation, which allocates `L'` for that node alone,
  and starts the boot program again by `Hwp`. A crash keeps the step fuel and
  resets the node's thread fuel.
* Both theorems are instances of one soundness core (`dist_soundness`), which
  allocates the global ghost state and reads the result off the invariant.
-/
module

public import Perennial.GooseLang.CrashAdequacy
public import Perennial.GooseLang.DistLang

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Language.Notation

attribute [local instance] GSet.lawfulSet

section dist
variable [GooseExts] [GooseInterp] [GooseSemantics] [GoGlobalContext]
variable {GF : BundledGFunctors}

/- Under the global ghost state alone (no local ghost state, hence no
`goose_irisGS`), its invariants are those of the fancy updates. -/
attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## The state interpretation, split between a node and the global state -/

/-- A node's part of the state interpretation: its heap, the local states of the
extensions, its package state, its Go context, its thread fuel and its
`notCrashed`. -/
def nodeInterp [G : GooseGlobalGS .hasLC GF] [L : GooseLocalGS GF] (σ : state) (t : Nat) : IProp GF :=
  iprop(naHeapCtx tls σ.heap ∗ extsLocalCtx σ.world ∗ ownGoStateCtx σ.goState.packageState ∗
    ⌜σ.goState.goLctx = L.goose_go_local_context⌝ ∗ threadFuel t ∗ notCrashed)

/-- The global part of the state interpretation: the global states of the
extensions, the prophecy map and the step fuel. -/
def globalInterp [G : GooseGlobalGS .hasLC GF] (g : GlobalState) (s : Nat)
    (κs : List Observation) : IProp GF :=
  iprop(extsGlobalCtx g.globalWorld ∗ prophMapInterp κs g.usedProphId ∗ receiptFuel s)

theorem bstateInterp_split [G : GooseGlobalGS .hasLC GF] [L : GooseLocalGS GF] (σ : state)
    (g : GlobalState) (s t : Nat) (κs : List Observation) :
    gooseBstateInterp (GF := GF) (((σ, g), ⟨s, t⟩) : BcfgState) κs ⊣⊢
      nodeInterp σ t ∗ globalInterp g s κs := by
  unfold gooseBstateInterp gooseStateInterp nodeInterp globalInterp
  constructor
  · iintro ⟨⟨Hh, Hl, Hgs, Hlctx, Hg, Hp⟩, Hr, Ht, Hnc⟩
    iframe
  · iintro ⟨⟨Hh, Hl, Hgs, Hlctx, Ht, Hnc⟩, Hg, Hp, Hr⟩
    iframe

/-! ## The proof obligation of a node -/

/-- The proof obligation of a node, under its ghost state `hG`: with thread
bound `T` and the node's Go context, the WP of its program `e` from its start
resources (the extensions' local start resources, the package state and the
main thread's token), with postcondition `φ`. -/
def nodeWpBody [hG : HeapGS .hasLC GF] (T : Nat) (e : Expr) (σ : state) (φ : val → Prop) :
    IProp GF :=
  iprop(⌜threadBound GF = T⌝ -∗
    ⌜hG.goose_localGS.goose_go_local_context = σ.goState.goLctx⌝ -∗
    extsLocalStart (GF := GF) σ.world -∗ ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
    WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})

/-- The proof obligation of the node running `e` from `σ`, under the global
ghost state `G`: `nodeWpBody` for every local ghost state of the node. -/
def nodeWp [G : GooseGlobalGS .hasLC GF] (T : Nat) (e : Expr) (σ : state) (φ : val → Prop) :
    IProp GF :=
  iprop(∀ L : GooseLocalGS GF, nodeWpBody (hG := ⟨G, L⟩) T e σ φ)

/-! ## The invariant of a distributed execution -/

/-- A node in the ghost state: for some local ghost state `L`, its part of the
state interpretation, the WPs of its threads (the main thread's with
postcondition `φ`) and the frame `R L` (nothing for executions without
crashes; for executions with crashes, the obligation of the node's next boot,
`crashFrame`). -/
def nodeInv [G : GooseGlobalGS .hasLC GF] (R : GooseLocalGS GF → IProp GF) (φ : val → Prop)
    (n : List Expr × state × Nat) : IProp GF :=
  iprop(∃ L : GooseLocalGS GF, nodeInterp (L := L) n.2.1 n.2.2 ∗
    (∃ k : Nat, gooseWptp (L := L) n.1 ((fun v => iprop(⌜φ v⌝)) :: forkPosts k)) ∗ R L)

/-- A distributed configuration in the ghost state: the global part of the state
interpretation, and every node `i` (with frame `R i` and the main thread's
postcondition `φ i`). -/
def distInv [G : GooseGlobalGS .hasLC GF] (R : Nat → GooseLocalGS GF → IProp GF)
    (φ : Nat → val → Prop) (c : BDistCfg) (κs : List Observation) : IProp GF :=
  iprop(globalInterp c.global c.steps κs ∗ [∗list] i ↦ n ∈ c.nodes, nodeInv (R i) (φ i) n)

/-- One step of a distributed configuration, in the ghost state: the step of
node `i`, by `wptp_step` under node `i`'s ghost state; the frames are kept. -/
theorem dist_step [G : GooseGlobalGS .hasLC GF] (R : Nat → GooseLocalGS GF → IProp GF)
    (φ : Nat → val → Prop) {c c' : BDistCfg}
    {κ : List Observation} (H : BDistStep c κ c') (κs : List Observation) :
    ⊢ distInv (GF := GF) R φ c (κ ++ κs) -∗ £ 1 ={⊤,∅}=∗ |={∅}▷=>^[1] |={∅,⊤}=>
      distInv R φ c' κs := by
  obtain ⟨i, tp, σ, t, tp', ⟨⟨σ', g'⟩, ⟨s', t'⟩⟩, hi, hstep, rfl⟩ := H
  unfold distInv nodeInv
  iintro ⟨Hg, Hnodes⟩ Hcred
  icases BigSepL.bigSepL_insert_acc hi $$ Hnodes with ⟨⟨%L, Hl, ⟨%k, Hwp⟩, HR⟩, Hclose⟩
  ihave Hσ := (bstateInterp_split (L := L) σ c.global c.steps t (κ ++ κs)).2 $$ [Hl Hg]
  · iframe
  icases wptp_step (iG := gooseIrisGS G L) Stuckness.NotStuck tp tp' κ κs _ _ 0 _ 0 hstep
    $$ Hσ Hcred Hwp with ⟨%nt', H⟩
  imod H
  imodintro
  iapply step_fupdN_wand $$ H
  iintro >⟨Hσ, Hwp⟩
  imodintro
  icases (bstateInterp_split (L := L) σ' g' s' t' κs).1 $$ Hσ with ⟨Hl, Hg⟩
  simp only [BDistCfg.setNode]
  iframe Hg
  iapply Hclose
  iexists L
  iframe Hl HR
  iexists k + nt'
  simp only [gooseWptp, forkPosts, ← List.replicate_append_replicate, List.cons_append]
  iexact Hwp

/-- `n` steps of a distributed configuration, in the ghost state. -/
theorem dist_preservation [G : GooseGlobalGS .hasLC GF] (R : Nat → GooseLocalGS GF → IProp GF)
    (φ : Nat → val → Prop) {n : Nat}
    {c c' : BDistCfg} {κs : List Observation} (H : BDistNsteps n c κs c')
    (κs' : List Observation) :
    ⊢ distInv (GF := GF) R φ c (κs ++ κs') -∗ £ n ={⊤,∅}=∗ |={∅}▷=>^[n] |={∅,⊤}=>
      distInv R φ c' κs' := by
  induction H with
  | refl c =>
    simp only [Nat.repeat, List.nil_append]
    iintro Hσ _
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hcl
    imod Hcl
    imodintro
    iexact Hσ
  | @cons n c₁ c₂ c₃ κ κs₁ hstep _ ih =>
    iintro Hσ Hcred
    rw [List.append_assoc, Nat.add_comm n 1]
    icases lc_split.1 $$ Hcred with ⟨Hcred₁, Hcred₂⟩
    imod dist_step R φ hstep (κs₁ ++ κs') $$ Hσ Hcred₁ with H
    imodintro
    rw [(step_fupdN_add (n := 1) (m := n)).to_eq]
    iapply step_fupdN_wand $$ H
    iintro H
    iapply fupd_step_fupdN_absorb
    imod H with Hσ
    imod ih $$ Hσ Hcred₂ with H
    imodintro
    iexact H

/-! ## The initial configuration -/

/-- The initial configuration of the bounded semantics, for receipt bound `N` and
thread bound `T`: each node runs its program alone with thread fuel `T - 2`,
and the step fuel is `N - 1`. -/
def bdistInit (N T : Nat) (es : List (Expr × state)) (g : GlobalState) : BDistCfg :=
  ⟨es.map (fun n => ([n.1], n.2, T - 2)), g, N - 1⟩

theorem bdistInit_erase (N T : Nat) (es : List (Expr × state)) (g : GlobalState) :
    (bdistInit N T es g).erase = distInit es g := by
  simp [bdistInit, BDistCfg.erase, distInit]

theorem bdistInit_fuelOk {N T : Nat} {es : List (Expr × state)} {g : GlobalState}
    (Hthreads : ∀ n, n ∈ es → n.2.threads = 1) : (bdistInit N T es g).FuelOk T := by
  intro j tp σ t hj
  simp only [bdistInit, List.getElem?_map] at hj
  obtain ⟨⟨e', σ'⟩, hj', hx⟩ := Option.map_eq_some_iff.mp hj
  simp only [Prod.mk.injEq] at hx
  obtain ⟨-, rfl, rfl⟩ := hx
  rw [Hthreads _ (List.mem_of_getElem? hj')]
  omega

/-- Allocate a node's local ghost state. -/
theorem goose_local_init [hPre : GooseGpreS GF] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (hT : 1 < T) (σ : state) (g : GlobalState) (Hinit : extsInitP σ.world g.globalWorld) :
    ⊢@{IProp GF} |==> ∃ L : GooseLocalGS GF,
      ⌜@ThreadGS.threadBound GF L.goose_threadGS = T⌝ ∗
      ⌜L.goose_go_local_context = σ.goState.goLctx⌝ ∗
      nodeInterp (L := L) σ (T - 2) ∗ extsLocalStart (L := L) σ.world ∗
      ownGoState (hG := L.goose_go_stateGS) σ.goState.packageState ∗
      threadTok (hT := L.goose_threadGS) := by
  imod na_heap_init (L := Loc) (V := val)
    (hG := ⟨hPre.goose_preG_heap.na_heap_preG_inG, default⟩) tls σ.heap with ⟨%hHeap, Hh⟩
  imod goState_init hPre.goose_preG_go_state σ.goState.packageState with ⟨%γ, Hgs, Hgs'⟩
  imod Exts.local_init exts _ hPre.goosePreGExts σ.world g.globalWorld Hinit
    with ⟨%hFL, Hlctx, Hlstart⟩
  imod thread_init T hT with ⟨%γT, HT⟩
  imod crashToken_init with ⟨%γC, HC⟩
  have Hsplit := (threadToks_add (hT := ⟨γT, T, hT⟩) (T - 2) 1).1
  rw [show T - 2 + 1 = T - 1 by omega] at Hsplit
  icases Hsplit $$ HT with ⟨Hfuel, Htok⟩
  imodintro
  iexists (⟨hFL, σ.goState.goLctx, hHeap, goStateGSUpdatePre GF hPre.goose_preG_go_state γ,
    ⟨γT, T, hT⟩, ⟨γC⟩⟩ : GooseLocalGS GF)
  unfold nodeInterp threadFuel
  iframe
  ipureintro; exact ⟨rfl, rfl, rfl⟩

/-- Allocate every node's local ghost state and discharge its proof obligation:
the nodes of the initial configuration in the ghost state, under the frames `R`
that the nodes' obligations `O` give. -/
theorem goose_nodes_init_gen [hPre : GooseGpreS GF] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (hT : 1 < T) (g : GlobalState) (es : List (Expr × state)) (φ : Nat → val → Prop)
    (Hinit : ∀ n, n ∈ es → extsInitP n.2.world g.globalWorld)
    (O : Nat → Expr × state → IProp GF) (R : Nat → GooseLocalGS GF → IProp GF)
    (HO : ∀ (i : Nat) (e : Expr) (σ : state) (L : GooseLocalGS GF), es[i]? = some (e, σ) →
      @ThreadGS.threadBound GF L.goose_threadGS = T →
      L.goose_go_local_context = σ.goState.goLctx →
      ⊢ O i (e, σ) -∗ extsLocalStart (L := L) σ.world -∗
        ownGoState (hG := L.goose_go_stateGS) σ.goState.packageState -∗
        threadTok (hT := L.goose_threadGS) ={⊤}=∗
        gooseWptp (L := L) [e] [fun v => iprop(⌜φ i v⌝)] ∗ R i L) :
    ⊢ ([∗list] i ↦ n ∈ es, O i n) ={⊤}=∗
      [∗list] i ↦ n ∈ es.map (fun n => ([n.1], n.2, T - 2)), nodeInv (R i) (φ i) n := by
  rw [BigSepL.bigSepL_map]
  iintro H
  iapply BigSepL2.bigSepL_fupd
  iapply BigSepL.bigSepL_mono (Φ := fun i n => O i n) ?_ $$ H
  intro i ⟨e, σ⟩ hi
  iintro Ho
  imod goose_local_init T hT σ g (Hinit (e, σ) (List.mem_of_getElem? hi))
    with ⟨%L, %HT, %Hlctx, Hσ, Hstart, Hgs, Htok⟩
  imod HO i e σ L hi HT Hlctx $$ Ho Hstart Hgs Htok with ⟨Hwp, HR⟩
  imodintro
  unfold nodeInv
  iexists L
  iframe Hσ HR
  iexists 0
  simp only [forkPosts, List.replicate_zero]
  iexact Hwp

/-! ## Soundness -/

/-- The soundness core of the adequacy theorems: if, for every global ghost
state with receipt bound `N`, the extensions' global start resources, the
global part of the initial state interpretation (prophecies `κs`, step fuel
`N - 1`) and `£ n` give, after `n` steps, the invariant of the configuration `c`
(with some frames), then every thread `e` of every node `i` of `c` can take a
step or is a value; a value is not a panic, and if it is the main thread's, it
satisfies `φ i`. -/
theorem dist_soundness [hPre : GooseGpreS GF] (N : Nat) (hN : 0 < N) (g : GlobalState)
    (φ : Nat → val → Prop) (hφ : ∀ i p, ¬ φ i (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (n : Nat) (κs : List Observation) (c : BDistCfg)
    (Hrun : ∀ [GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗ globalInterp g (N - 1) κs -∗ £ n ={⊤,∅}=∗
        |={∅}▷=>^[n] |={∅,⊤}=> ∃ R : Nat → GooseLocalGS GF → IProp GF, distInv R φ c [])
    {i : Nat} {tp : List Expr} {σ : state} {t : Nat} (Hi : c.nodes[i]? = some (tp, σ, t))
    {j : Nat} {e : Expr} (Hj : tp[j]? = some e) :
    PrimStep.NotStuck (e, c.nodeState σ t) ∧
      ∀ v, e = Val v → v.isPanic = false ∧ (j = 0 → φ i v) := by
  apply pure_soundness (PROP := IProp GF)
  apply laterN_soundness (n := n + 1)
  rw [(laterN_succ_right _).to_eq]
  refine Entails.trans ?_ (laterN_mono _ except0_into_later)
  apply fupd_finally_soundness .hasLC n ⊤
  iintro %Hinv Hf
  -- the global ghost state
  imod ProphMap.init (H := GMap proph_id) (V := val) κs g.usedProphId with ⟨%hProph, Hp⟩
  imod Exts.global_init exts _ hPre.goosePreGExts g.globalWorld Hinitg with ⟨%hFG, Hgctx, Hgstart⟩
  letI := hPre.goosePreGAllG
  imod receipt_init N hN with ⟨%γR, %γL, HR⟩
  let G : GooseGlobalGS .hasLC GF :=
    ⟨Hinv, hPre.goosePreGAllG, hProph, hFG, ⟨γR, γL, N, hN⟩⟩
  -- the execution
  imod (@Hrun G rfl) $$ Hgstart [Hp Hgctx HR] Hf with H
  · unfold globalInterp
    iframe
  iapply step_fupdN_fupd_finally
  iapply step_fupdN_wand $$ H
  iintro >⟨%R, H⟩
  unfold distInv nodeInv
  icases H with ⟨Hg, Hnodes⟩
  -- node `i` and its thread `j`
  icases BigSepL.bigSepL_lookup Hi $$ Hnodes with ⟨%L, Hl, ⟨%k, Ht⟩, -⟩
  ihave Hσ := (bstateInterp_split (L := L) σ c.global c.steps t []).2 $$ [Hl Hg]
  · iframe
  icases BigSepL2.bigSepL2_lookup_left Hj $$ Ht with ⟨%Φ, %HΦ, He⟩
  cases e with
  | Val v =>
    imod (wp_value_fupd' (ι := gooseIrisGS G L)).1 $$ He with HΦv
    have Hpost : Φ = (fun v => iprop(⌜φ i v⌝)) ∧ j = 0 ∨
        Φ = (fun v => iprop(⌜v.isPanic = false⌝)) ∧ j ≠ 0 := by
      cases j with
      | zero => left; simpa using HΦ.symm
      | succ j =>
        right
        simp only [List.getElem?_cons_succ, forkPosts, List.getElem?_replicate] at HΦ
        split at HΦ
        · cases HΦ; exact ⟨rfl, by omega⟩
        · cases HΦ
    rcases Hpost with ⟨rfl, rfl⟩ | ⟨rfl, Hj0⟩
    · icases HΦv with %HΦv
      ipureintro
      refine ⟨.inl rfl, fun w hw => ?_⟩
      cases hw
      exact ⟨by cases v <;> first | rfl | exact absurd HΦv (hφ _ _), fun _ => HΦv⟩
    · icases HΦv with %HΦv
      ipureintro
      refine ⟨.inl rfl, fun w hw => ?_⟩
      cases hw
      exact ⟨HΦv, fun h => absurd h Hj0⟩
  | _ =>
    imod wp_not_stuck (iG := gooseIrisGS G L) (κs := []) (nt := 0) (ns := 0) $$ Hσ He with %Hns
    ipureintro
    exact ⟨Hns, fun _ h => by cases h⟩

/-- A thread with an unrecovered panic at node `i` of `c` unwinds, by steps of
node `i` that use no fuel, to a configuration where it is `PanicV p`. -/
theorem unrecoveredPanic_node {c : BDistCfg} {i : Nat} {tp : List Expr} {σ : state} {t : Nat}
    (Hi : c.nodes[i]? = some (tp, σ, t)) {e : Expr} (He : e ∈ tp) (Hu : UnrecoveredPanic e) :
    ∃ (m : Nat) (κs : List Observation) (c' : BDistCfg) (tp' : List Expr) (j : Nat) (p : val),
      BDistNsteps m c κs c' ∧ c'.nodes[i]? = some (tp', σ, t) ∧
      tp'[j]? = some (Val (PanicV p)) ∧ c'.nodeState σ t = c.nodeState σ t := by
  obtain ⟨p, Hp⟩ := unrecoveredPanic_steps Hu
  obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem He
  have hilen : i < c.nodes.length := (List.getElem?_eq_some_iff.mp Hi).1
  obtain ⟨m, κs', Hm⟩ := BDistNsteps.of_node hilen (Hp [] t₁ t₂ (c.nodeState σ t))
  change BDistNsteps m (c.setNode i (t₁ ++ e :: t₂) (c.nodeState σ t)) κs'
    (c.setNode i (t₁ ++ Val (PanicV p) :: t₂) (c.nodeState σ t)) at Hm
  rw [BDistCfg.setNode_self Hi] at Hm
  have Hi' := BDistCfg.setNode_nodes (c := c) (i := i) (tp := t₁ ++ Val (PanicV p) :: t₂)
    (s := c.nodeState σ t)
  rw [ite_eq_left_iff.mpr (fun h => absurd hilen h)] at Hi'
  exact ⟨m, κs', _, _, t₁.length, p, Hm, Hi', by simp, rfl⟩

/-! ## Adequacy without crashes -/

/-- Adequacy of the bounded semantics of a distributed system: under the
hypotheses of `goose_dist_adequacy`, in every execution of the bounded semantics
from `bdistInit N T es g`, every thread `e` of every node `i` can take a step
or is a value; a value is not a panic, and if it is the main thread's, it
satisfies `φ i`. -/
theorem goose_dist_adequacy_blang [hPre : GooseGpreS GF] (N T : Nat) (hN : 0 < N) (hT : 1 < T)
    (es : List (Expr × state)) (g : GlobalState) (φ : Nat → val → Prop)
    (hφ : ∀ i p, ¬ φ i (PanicV p))
    (Hinitg : extsInitgP g.globalWorld)
    (Hinit : ∀ n, n ∈ es → extsInitP n.2.world g.globalWorld)
    (Hwp : ∀ [GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld ={⊤}=∗
        [∗list] i ↦ n ∈ es, nodeWp T n.1 n.2 (φ i))
    {n : Nat} {κs : List Observation} {c : BDistCfg}
    (Hsteps : BDistNsteps n (bdistInit N T es g) κs c)
    {i : Nat} {tp : List Expr} {σ : state} {t : Nat} (Hi : c.nodes[i]? = some (tp, σ, t))
    {j : Nat} {e : Expr} (Hj : tp[j]? = some e) :
    PrimStep.NotStuck (e, c.nodeState σ t) ∧
      ∀ v, e = Val v → v.isPanic = false ∧ (j = 0 → φ i v) := by
  refine dist_soundness (GF := GF) N hN g φ hφ Hinitg n κs c ?_ Hi Hj
  intro G HN
  iintro Hgstart Hg Hf
  imod (@Hwp G HN) $$ Hgstart with Hnodes
  imod goose_nodes_init_gen (G := G) T hT g es φ Hinit (fun i n => nodeWp T n.1 n.2 (φ i))
    (fun _ _ => iprop(emp)) ?_ $$ Hnodes with Hnodes
  · intro i e σ L _ HT Hlctx
    iintro Hn Hstart Hgs Htok
    unfold nodeWp nodeWpBody
    imod Hn $$ %L %HT %Hlctx Hstart Hgs Htok with Hwp
    imodintro
    isplitl [Hwp]
    · try simp only [gooseWptp]
      iapply BigSepL2.bigSepL2_singleton.2
      iexact Hwp
    iempintro
  have Hpres := dist_preservation (G := G) (fun _ _ => iprop(emp)) φ Hsteps []
  rw [List.append_nil] at Hpres
  imod Hpres $$ [Hg Hnodes] Hf with H
  · unfold distInv bdistInit
    iframe
  imodintro
  iapply step_fupdN_wand $$ H
  iintro H
  imod H
  imodintro
  iexists _
  iexact H

/-- No thread of the bounded semantics has an unrecovered panic: it would unwind
to `PanicV p` without using fuel (`unrecoveredPanic_node`), contradicting
`goose_dist_adequacy_blang`. -/
theorem goose_dist_no_unrecovered_panic_blang [hPre : GooseGpreS GF] (N T : Nat) (hN : 0 < N)
    (hT : 1 < T) (es : List (Expr × state)) (g : GlobalState) (φ : Nat → val → Prop)
    (hφ : ∀ i p, ¬ φ i (PanicV p))
    (Hinitg : extsInitgP g.globalWorld)
    (Hinit : ∀ n, n ∈ es → extsInitP n.2.world g.globalWorld)
    (Hwp : ∀ [GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld ={⊤}=∗
        [∗list] i ↦ n ∈ es, nodeWp T n.1 n.2 (φ i))
    {n : Nat} {κs : List Observation} {c : BDistCfg}
    (Hsteps : BDistNsteps n (bdistInit N T es g) κs c)
    {i : Nat} {tp : List Expr} {σ : state} {t : Nat} (Hi : c.nodes[i]? = some (tp, σ, t))
    (e : Expr) (He : e ∈ tp) : ¬ UnrecoveredPanic e := by
  intro Hu
  obtain ⟨m, κs', c', tp', j, p, Hm, Hi', Hj, -⟩ := unrecoveredPanic_node Hi He Hu
  have := (goose_dist_adequacy_blang N T hN hT es g φ hφ Hinitg Hinit Hwp (Hsteps.append Hm) Hi'
    Hj).2 (PanicV p) rfl
  simp at this

/-- Adequacy of GooseLang for distributed systems, for the real semantics, under
the time-receipt and thread-bound assumptions: for any bounds `N` and `T`, for
the system whose node `i` runs the program `es[i].1` from the local state
`es[i].2`, all of them sharing the global state `g`, if `Hwp`: for every global
ghost state with receipt bound `N`, the extensions' global start resources
give, after a fancy update, the proof obligation of every node (`nodeWp`: the WP
of the node's program with postcondition `φ i`, for any local ghost state with
thread bound `T` and the node's Go context, from the node's start resources),
with postconditions that exclude panics (`hφ`), then in every real execution of
the system (`DistNsteps`) of fewer than `N` steps in all, from a configuration
in which each node has its main thread only, along which every node has fewer
than `T` live threads (`DistThreadsBelow`), for every node `i` with thread pool
`tp` and local state `σ`:
* if the node's main thread has terminated with `v` then `φ i v`;
* every thread of the node is a value or can take a step;
* no thread of the node has an unrecovered panic. -/
theorem goose_dist_adequacy [hPre : GooseGpreS GF] (N T : Nat)
    (es : List (Expr × state)) (g : GlobalState) (φ : Nat → val → Prop)
    (hφ : ∀ i p, ¬ φ i (PanicV p))
    (Hinitg : extsInitgP g.globalWorld)
    (Hinit : ∀ n, n ∈ es → extsInitP n.2.world g.globalWorld)
    (Hwp : ∀ [GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld ={⊤}=∗
        [∗list] i ↦ n ∈ es, nodeWp T n.1 n.2 (φ i))
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistNsteps n (distInit es g) κs c)
    (Hbound : n < N) (Hthreads : ∀ n, n ∈ es → n.2.threads = 1)
    (Hlive : DistThreadsBelow T n (distInit es g)) :
    ∀ i tp σ, c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → φ i v) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) := by
  intro i tp σ Hi
  -- the node exists initially, with a single thread, so `1 < T`
  have hlen : i < es.length := by
    have := (List.getElem?_eq_some_iff.mp Hi).1
    rw [Hsteps.length] at this
    simpa [distInit] using this
  have hT : 1 < T := by
    have := Hlive.start (i := i) (tp := [es[i].1]) (σ := es[i].2) (by simp [distInit, hlen])
    rw [Hthreads _ (List.getElem_mem hlen)] at this
    exact this
  obtain ⟨bc, Hb, He⟩ := bdist_nsteps_of_real Hsteps T Hlive (bdistInit N T es g)
    (bdistInit_erase N T es g) (by simp only [bdistInit]; omega) (bdistInit_fuelOk Hthreads)
  -- node `i` of the bounded configuration
  subst He
  simp only [BDistCfg.erase, List.getElem?_map] at Hi
  obtain ⟨⟨tp₀, σ₀, t⟩, Hbi, hx⟩ := Option.map_eq_some_iff.mp Hi
  obtain ⟨rfl, rfl⟩ : tp = tp₀ ∧ σ = σ₀ := by
    simp only [Prod.mk.injEq] at hx; exact ⟨hx.1.symm, hx.2.symm⟩
  have Hadeq := fun {j} {e} (Hj : tp[j]? = some e) =>
    goose_dist_adequacy_blang N T (by omega) hT es g φ hφ Hinitg Hinit Hwp Hb Hbi Hj
  refine ⟨?_, ?_, ?_⟩
  · rintro v tp' rfl
    exact ((Hadeq (j := 0) (e := Val v) rfl).2 v rfl).2 rfl
  · intro e he
    obtain ⟨j, Hj⟩ := List.getElem?_of_mem he
    exact realNotStuck_of_bounded (Hadeq Hj).1
  · exact goose_dist_no_unrecovered_panic_blang N T (by omega) hT es g φ hφ Hinitg Hinit Hwp Hb Hbi

end dist

/-! ## Adequacy with crashes -/

section dist_crash
variable [GooseExts] [GooseInterp] [GooseSemantics] [GoGlobalContext] [GooseCrashInterp]
variable {GF : BundledGFunctors}

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The proof obligation of a node's start under the global ghost state `G`, for
the precondition `P` of its boot program: for every local ghost state of the
node with thread bound `T` and the node's Go context, `P` from the node's
start resources (the extensions' local start resources and the package
state). -/
def nodeStart [G : GooseGlobalGS .hasLC GF] (T : Nat) (σ : state)
    (P : GooseLocalGS GF → IProp GF) : IProp GF :=
  iprop(∀ L : GooseLocalGS GF, ⌜@ThreadGS.threadBound GF L.goose_threadGS = T⌝ -∗
    ⌜L.goose_go_local_context = σ.goState.goLctx⌝ -∗
    extsLocalStart (L := L) σ.world -∗
    ownGoState (hG := L.goose_go_stateGS) σ.goState.packageState ={⊤}=∗ P L)

/-- The frame of node `i` (local ghost state `L`) in an execution with crashes:
the node's initial state `σ₀` (its Go context is `L`'s), its thread bound, and
its guarantee that the precondition `P i` of its boot program holds after it
crashes, for whatever local ghost state `L'` the restart gets, from `L`'s
`crashed`, the extensions' `crashStart L L'` and `L'`'s empty package state. -/
def crashFrame [G : GooseGlobalGS .hasLC GF] (T : Nat) (es : List (Expr × state))
    (P : Nat → GooseLocalGS GF → IProp GF) (i : Nat) (L : GooseLocalGS GF) : IProp GF :=
  iprop(∃ (e : Expr) (σ₀ : state), ⌜es[i]? = some (e, σ₀)⌝ ∗
    ⌜@ThreadGS.threadBound GF L.goose_threadGS = T⌝ ∗
    ⌜L.goose_go_local_context = σ₀.goState.goLctx⌝ ∗
    ∀ L' : GooseLocalGS GF, crashed (hC := L.goose_crashGS) -∗ extsCrashStart L L' -∗
      ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ P i L')

/-- The proof obligation of a boot program in every generation of node `i`
(the `Hwp` of `goose_dist_crash_adequacy`, for the global ghost state `G`). -/
abbrev BootWp [G : GooseGlobalGS .hasLC GF] (T : Nat) (es : List (Expr × state))
    (φ : Nat → val → Prop) (P : Nat → GooseLocalGS GF → IProp GF) : Prop :=
  ∀ (L : GooseLocalGS GF) (i : Nat) (e : Expr) (σ : state), es[i]? = some (e, σ) →
    @ThreadGS.threadBound GF L.goose_threadGS = T →
    L.goose_go_local_context = σ.goState.goLctx →
    ⊢ P i L -∗ threadTok (hT := L.goose_threadGS) ={⊤}=∗
      gooseWptp (L := L) [e] [fun v => iprop(⌜φ i v⌝)] ∗ crashFrame T es P i L

/-- A crash of a node, in the ghost state: the node's part of the state
interpretation gives way to that of a new local ghost state `L'`
(`goose_crash_step`), whose boot program the node's crash frame and `Hwp`
prove. -/
theorem dist_crash_node [hPre : GooseGpreS GF] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (es : List (Expr × state)) (φ : Nat → val → Prop) (P : Nat → GooseLocalGS GF → IProp GF)
    (Hwp : BootWp T es φ P) {c : BDistCfg} {i : Nat} {tp : List Expr} {σ : state} {t : Nat}
    {e : Expr} {σ' : state} (hi : c.nodes[i]? = some (tp, σ, t))
    (hboot : (es.map Prod.fst)[i]? = some e) (hc : Crash σ σ') (κs : List Observation) :
    ⊢ distInv (GF := GF) (crashFrame T es P) φ c κs ={⊤}=∗
      distInv (crashFrame T es P) φ ⟨c.nodes.set i ([e], σ', T - 2), c.global, c.steps⟩ κs := by
  unfold distInv nodeInv
  iintro ⟨Hg, Hnodes⟩
  icases BigSepL.bigSepL_insert_acc hi $$ Hnodes with ⟨⟨%L, Hl, -, HR⟩, Hclose⟩
  unfold crashFrame
  icases HR with ⟨%e₀, %σ₀, %Hes, %HT, %Hlctx, HΨ⟩
  obtain rfl : e₀ = e := by
    simp only [List.getElem?_map, Hes, Option.map_some, Option.some.injEq] at hboot
    exact hboot
  have hT : 1 < T := HT ▸ L.goose_threadGS.threadBound_gt
  ihave Hσ := (bstateInterp_split (L := L) σ c.global c.steps t κs).2 $$ [Hl Hg]
  · iframe
  imod goose_crash_step (L := L) T hT hc c.global ⟨c.steps, t⟩ κs $$ Hσ
    with ⟨%L', %HL'lctx, %HL'T, Hσ, Hcr, Hcs, Hgs, Htok⟩
  imod HΨ $$ %L' Hcr Hcs Hgs with HP
  imod Hwp L' i e₀ σ₀ Hes HL'T (by rw [HL'lctx, Hlctx]) $$ HP Htok with ⟨Hwp, HR⟩
  icases (bstateInterp_split (L := L') σ' c.global c.steps (T - 2) κs).1 $$ Hσ with ⟨Hl, Hg⟩
  imodintro
  iframe Hg
  iapply Hclose
  iexists L'
  iframe Hl
  isplitl [Hwp]
  · iexists 0
    simp only [forkPosts, List.replicate_zero]
    iexact Hwp
  unfold crashFrame
  iexact HR

/-- One step with crashes, in the ghost state. -/
theorem dist_crash_step [hPre : GooseGpreS GF] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (es : List (Expr × state)) (φ : Nat → val → Prop) (P : Nat → GooseLocalGS GF → IProp GF)
    (Hwp : BootWp T es φ P) {c c' : BDistCfg} {κ : List Observation}
    (H : BDistCrashStep (es.map Prod.fst) T c κ c') (κs : List Observation) :
    ⊢ distInv (GF := GF) (crashFrame T es P) φ c (κ ++ κs) -∗ £ 1 ={⊤,∅}=∗
      |={∅}▷=>^[1] |={∅,⊤}=> distInv (crashFrame T es P) φ c' κs := by
  cases H with
  | step H => exact dist_step _ φ H κs
  | crash hi hboot hc =>
    rw [List.nil_append]
    iintro Hσ _
    imod dist_crash_node T es φ P Hwp hi hboot hc κs $$ Hσ with Hσ
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hcl
    iapply step_fupdN_intro Std.LawfulSet.subset_refl
    iintro !>
    imod Hcl
    imodintro
    iexact Hσ

/-- `n` steps with crashes, in the ghost state. -/
theorem dist_crash_preservation [hPre : GooseGpreS GF] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (es : List (Expr × state)) (φ : Nat → val → Prop) (P : Nat → GooseLocalGS GF → IProp GF)
    (Hwp : BootWp T es φ P) {n : Nat} {c c' : BDistCfg} {κs : List Observation}
    (H : BDistCrashNsteps (es.map Prod.fst) T n c κs c') (κs' : List Observation) :
    ⊢ distInv (GF := GF) (crashFrame T es P) φ c (κs ++ κs') -∗ £ n ={⊤,∅}=∗
      |={∅}▷=>^[n] |={∅,⊤}=> distInv (crashFrame T es P) φ c' κs' := by
  induction H with
  | refl c =>
    simp only [Nat.repeat, List.nil_append]
    iintro Hσ _
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hcl
    imod Hcl
    imodintro
    iexact Hσ
  | @cons n c₁ c₂ c₃ κ κs₁ hstep _ ih =>
    iintro Hσ Hcred
    rw [List.append_assoc, Nat.add_comm n 1]
    icases lc_split.1 $$ Hcred with ⟨Hcred₁, Hcred₂⟩
    imod dist_crash_step T es φ P Hwp hstep (κs₁ ++ κs') $$ Hσ Hcred₁ with H
    imodintro
    rw [(step_fupdN_add (n := 1) (m := n)).to_eq]
    iapply step_fupdN_wand $$ H
    iintro H
    iapply fupd_step_fupdN_absorb
    imod H with Hσ
    imod ih $$ Hσ Hcred₂ with H
    imodintro
    iexact H

/-- Crash adequacy of the bounded semantics of a distributed system: under the
hypotheses of `goose_dist_crash_adequacy`, in every execution with crashes of
the bounded semantics from `bdistInit N T es g`, every thread `e` of every node
`i` can take a step or is a value; a value is not a panic, and if it is the
main thread's, it satisfies `φ i`. -/
theorem goose_dist_crash_adequacy_blang [hPre : GooseGpreS GF] (N T : Nat) (hN : 0 < N)
    (hT : 1 < T) (es : List (Expr × state)) (g : GlobalState) (φ : Nat → val → Prop)
    (hφ : ∀ i p, ¬ φ i (PanicV p))
    (Hinitg : extsInitgP g.globalWorld)
    (Hinit : ∀ n, n ∈ es → extsInitP n.2.world g.globalWorld)
    (P : ∀ [GooseGlobalGS .hasLC GF], Nat → GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld ={⊤}=∗
        [∗list] i ↦ n ∈ es, nodeStart T n.2 (P i))
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      ∀ (i : Nat) (e : Expr) (σ : state), es[i]? = some (e, σ) →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P i hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ i v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          extsCrashStart hG.goose_localGS L' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ P i L')
    {n : Nat} {κs : List Observation} {c : BDistCfg}
    (Hsteps : BDistCrashNsteps (es.map Prod.fst) T n (bdistInit N T es g) κs c)
    {i : Nat} {tp : List Expr} {σ : state} {t : Nat} (Hi : c.nodes[i]? = some (tp, σ, t))
    {j : Nat} {e : Expr} (Hj : tp[j]? = some e) :
    PrimStep.NotStuck (e, c.nodeState σ t) ∧
      ∀ v, e = Val v → v.isPanic = false ∧ (j = 0 → φ i v) := by
  refine dist_soundness (GF := GF) N hN g φ hφ Hinitg n κs c ?_ Hi Hj
  intro G HN
  -- the boot obligation of every generation, as `BootWp`
  have Hboot : BootWp (G := G) T es φ P := by
    intro L i e σ Hes HT Hlctx
    iintro HP Htok
    imod (@Hwp ⟨G, L⟩ HN HT i e σ Hes Hlctx) $$ HP Htok with ⟨Hwp, HΨ⟩
    imodintro
    isplitl [Hwp]
    · simp only [gooseWptp]
      iapply BigSepL2.bigSepL2_singleton.2
      iexact Hwp
    unfold crashFrame
    iexists e, σ
    iframe HΨ
    ipureintro
    exact ⟨Hes, HT, Hlctx⟩
  iintro Hgstart Hg Hf
  imod (@Hstart G HN) $$ Hgstart with Hnodes
  imod goose_nodes_init_gen (G := G) T hT g es φ Hinit (fun i n => nodeStart T n.2 (P i))
    (crashFrame T es P) ?_ $$ Hnodes with Hnodes
  · intro i e σ L Hes HT Hlctx
    iintro Hn Hstart Hgs Htok
    unfold nodeStart
    imod Hn $$ %L %HT %Hlctx Hstart Hgs with HP
    iapply Hboot L i e σ Hes HT Hlctx $$ HP Htok
  have Hpres := dist_crash_preservation (G := G) T es φ P Hboot Hsteps []
  rw [List.append_nil] at Hpres
  imod Hpres $$ [Hg Hnodes] Hf with H
  · unfold distInv bdistInit
    iframe
  imodintro
  iapply step_fupdN_wand $$ H
  iintro H
  imod H
  imodintro
  iexists _
  iexact H

/-- Crash adequacy of GooseLang for distributed systems, for the real
semantics: for any bounds `N` and `T`, for the system whose node `i` has the
boot program `es[i].1`, which it runs from the local state `es[i].2` at the
start and after every crash, all nodes sharing the global state `g`, if

* `P i L` is the precondition of node `i`'s boot program, over the local
  ghost state `L` of a generation of the node (the run between two crashes);
* `Hstart`: for every global ghost state with receipt bound `N`, the
  extensions' global start resources give, after a fancy update (the global
  setup, which may allocate the invariants the nodes share), the start of
  every node (`nodeStart`: `P i` for the first generation, from the node's
  start resources);
* `Hwp`: in every generation of every node `i`, the WP of its boot program
  with postcondition `φ i` from `P i` and the main thread's token, together
  with `P i L'` of whatever next local ghost state `L'` its crash allocates,
  from the generation's `crashed`, the extensions' `crashStart` resources and
  `L'`'s empty package state;

with postconditions that exclude panics (`hφ`), then in every real execution
with crashes of the system (`DistCrashNsteps`, the boot programs
`es.map Prod.fst`) of fewer than `N` steps in all (crashes included), from a
configuration in which each node has its main thread only, along which every
node has fewer than `T` live threads (`DistCrashThreadsBelow`), for every node
`i` with thread pool `tp` and local state `σ`:
* if the node's main thread has terminated with `v` then `φ i v`;
* every thread of the node is a value or can take a step;
* no thread of the node has an unrecovered panic. -/
theorem goose_dist_crash_adequacy [hPre : GooseGpreS GF] (N T : Nat)
    (es : List (Expr × state)) (g : GlobalState) (φ : Nat → val → Prop)
    (hφ : ∀ i p, ¬ φ i (PanicV p))
    (Hinitg : extsInitgP g.globalWorld)
    (Hinit : ∀ n, n ∈ es → extsInitP n.2.world g.globalWorld)
    (P : ∀ [GooseGlobalGS .hasLC GF], Nat → GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld ={⊤}=∗
        [∗list] i ↦ n ∈ es, nodeStart T n.2 (P i))
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      ∀ (i : Nat) (e : Expr) (σ : state), es[i]? = some (e, σ) →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P i hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ i v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          extsCrashStart hG.goose_localGS L' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ P i L')
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps (es.map Prod.fst) n (distInit es g) κs c)
    (Hbound : n < N) (Hthreads : ∀ n, n ∈ es → n.2.threads = 1)
    (Hlive : DistCrashThreadsBelow (es.map Prod.fst) T n (distInit es g)) :
    ∀ i tp σ, c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → φ i v) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) := by
  intro i tp σ Hi
  have hlen : i < es.length := by
    have := (List.getElem?_eq_some_iff.mp Hi).1
    rw [Hsteps.length] at this
    simpa [distInit] using this
  have hT : 1 < T := by
    have := Hlive.start (i := i) (tp := [es[i].1]) (σ := es[i].2) (by simp [distInit, hlen])
    rw [Hthreads _ (List.getElem_mem hlen)] at this
    exact this
  obtain ⟨bc, Hb, He⟩ := bdist_crash_nsteps_of_real Hsteps T Hlive (bdistInit N T es g)
    (bdistInit_erase N T es g) (by simp only [bdistInit]; omega) (bdistInit_fuelOk Hthreads)
  subst He
  simp only [BDistCfg.erase, List.getElem?_map] at Hi
  obtain ⟨⟨tp₀, σ₀, t⟩, Hbi, hx⟩ := Option.map_eq_some_iff.mp Hi
  obtain ⟨rfl, rfl⟩ : tp = tp₀ ∧ σ = σ₀ := by
    simp only [Prod.mk.injEq] at hx; exact ⟨hx.1.symm, hx.2.symm⟩
  have Hadeq := fun {m κs' c'} (Hm : BDistCrashNsteps (es.map Prod.fst) T m bc κs' c')
      {i tp σ t} (Hi : c'.nodes[i]? = some (tp, σ, t)) {j} {e} (Hj : tp[j]? = some e) =>
    goose_dist_crash_adequacy_blang N T (by omega) hT es g φ hφ Hinitg Hinit P Hstart Hwp
      (Hb.append Hm) Hi Hj
  refine ⟨?_, ?_, ?_⟩
  · rintro v tp' rfl
    exact ((Hadeq (.refl _) Hbi (j := 0) (e := Val v) rfl).2 v rfl).2 rfl
  · intro e he
    obtain ⟨j, Hj⟩ := List.getElem?_of_mem he
    exact realNotStuck_of_bounded (Hadeq (.refl _) Hbi Hj).1
  · intro e he Hu
    obtain ⟨m, κs', c', tp', j, p, Hm, Hi', Hj, -⟩ := unrecoveredPanic_node Hbi he Hu
    have := (Hadeq Hm.crash Hi' Hj).2 (PanicV p) rfl
    simp at this

end dist_crash

end Perennial
