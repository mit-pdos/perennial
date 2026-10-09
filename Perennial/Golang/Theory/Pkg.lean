/-
Package initialization.

* `ownInitializing get_is_pkg_init`: permission to run `package.init`
  (exclusive, since Go packages are initialized sequentially).
* `IsPkgInit PROP pkg_name`: the (canonical) post-initialization predicate of a
  package, split into the auto-generated dependency part `isPkgInitDeps` and
  the user-specified part `isPkgInitDef`; `isPkgInit pkg_name` asserts both.
* `GetIsPkgInitWf PROP pkg_name`: a pure predicate constraining
  `get_is_pkg_init` to contain the init predicates of `pkg_name` and its
  transitive dependencies.
* `define_is_pkg_init P` (term) builds an `IsPkgInit` instance whose
  dependencies are computed from `pkgImportedPkgs`; `build_get_is_pkg_init_wf`
  (term) builds the `GetIsPkgInitWf` instance.
* Tactics: `solve_pkg_init` (prove a goal `isPkgInit pkg` from the
  intuitionistic context), `iPkgInit` (solve `isPkgInit` goals and conjuncts
  at the front of the goal).
-/
module

public import Perennial.Golang.Theory.PostLifting
public import Perennial.Golang.Defn.Pkg
public import Perennial.Algebra.BigOp
public meta import Perennial.Golang.Theory.PostLifting

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

noncomputable section init_defns
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]

def IsInit [FfiModel] (σ : state) : Prop :=
  σ.goState.packageState = ∅

/-- Permission to run `package.init`. `get_is_pkg_init` maps every package to
its agreed-upon post-init predicate. -/
def ownInitializingDef (get_is_pkg_init : GoString → IProp GF) : IProp GF :=
  iprop(∃ package_inited : GMap GoString Bool,
    "Hg" ∷ ownGoState package_inited ∗
    "#Hinit" ∷ □ ([∗map] pkg_name ↦ inited ∈ package_inited,
      if inited then get_is_pkg_init pkg_name else iprop(True)))

@[irreducible] def ownInitializing (get_is_pkg_init : GoString → IProp GF) : IProp GF :=
  ownInitializingDef get_is_pkg_init

theorem ownInitializing_unseal : @ownInitializing = @ownInitializingDef := by
  funext; with_unfolding_all rfl

end init_defns

section package_init_and_defined
variable {PROP : Type _} [BI PROP]

/-- `IsPkgInit PROP pkg_name` connects a package name (the full package path) to
its post-initialization predicate. There should be only one instance for each
package. -/
class IsPkgInit (PROP : Type _) [BI PROP] (pkg_name : GoString) where
  /-- auto-generated; includes the `isPkgInit` of the dependencies -/
  isPkgInitDeps : PROP
  /-- user-specified -/
  isPkgInitDef : PROP

export IsPkgInit (isPkgInitDeps isPkgInitDef)

def isPkgInitWrap (pkg_name : GoString) [IsPkgInit PROP pkg_name] : PROP :=
  iprop("#Hdeps" ∷ □ isPkgInitDeps (PROP := PROP) pkg_name ∗
    "#Hinit" ∷ □ isPkgInitDef (PROP := PROP) pkg_name)

/-- `isPkgInit pkg_name` asserts the predicate of the `IsPkgInit` instance
(sealed). -/
@[irreducible] def isPkgInit (pkg_name : GoString) [IsPkgInit PROP pkg_name] : PROP :=
  isPkgInitWrap pkg_name

theorem isPkgInit_unfold (pkg_name : GoString) [IsPkgInit PROP pkg_name] :
    isPkgInit (PROP := PROP) pkg_name =
      iprop("#Hdeps" ∷ □ isPkgInitDeps (PROP := PROP) pkg_name ∗
        "#Hinit" ∷ □ isPkgInitDef (PROP := PROP) pkg_name) := by
  with_unfolding_all rfl

instance isPkgInit_pers (pkg_name : GoString) [IsPkgInit PROP pkg_name] :
    Persistent (isPkgInit (PROP := PROP) pkg_name) := by
  rw [isPkgInit_unfold]; unfold named; infer_instance

/-- Access the user-defined init predicate. -/
theorem isPkgInit_access (pkg_name : GoString) [IsPkgInit PROP pkg_name] :
    isPkgInit (PROP := PROP) pkg_name ⊢ isPkgInitDef pkg_name := by
  rw [isPkgInit_unfold]
  iintro ⟨_, #H⟩
  iexact H

theorem isPkgInit_unfold_deps (pkg_name : GoString) [IsPkgInit PROP pkg_name] :
    isPkgInit (PROP := PROP) pkg_name ⊢ isPkgInitDeps pkg_name := by
  rw [isPkgInit_unfold]
  iintro ⟨#H, _⟩
  iexact H

/-- Maps `pkg_name` to a pure predicate that constrains `get_is_pkg_init` to
have all of the init predicates for `pkg_name` and its transitive dependencies. -/
class GetIsPkgInitWf (PROP : Type _) [BI PROP] (pkg_name : GoString) where
  get_is_pkg_init_prop_def : (GoString → PROP) → Prop

/-- `get_is_pkg_init` satisfies the well-formedness condition of `pkg_name`. -/
abbrev GetIsPkgInitProp (pkg_name : GoString) [GetIsPkgInitWf PROP pkg_name]
    (get_is_pkg_init : GoString → PROP) : Prop :=
  GetIsPkgInitWf.get_is_pkg_init_prop_def pkg_name get_is_pkg_init

end package_init_and_defined

/-! ## Building `IsPkgInit` and `GetIsPkgInitWf` instances -/

section builders
open Lean Elab Term Meta

/-- The list of imported packages of `pkg` (from its `PkgInfo` instance), as a
list of expressions. -/
meta def importedPkgs (pkg : Lean.Expr) : TermElabM (List Lean.Expr) := do
  let deps ← whnf (← mkAppOptM ``pkgImportedPkgs #[some pkg, none])
  let rec go (e : Lean.Expr) (fuel : Nat) : TermElabM (List Lean.Expr) := do
    match fuel with
    | 0 => throwError "importedPkgs: list too long"
    | fuel + 1 =>
      let e ← whnf e
      if e.isAppOfArity ``List.cons 3 then
        return e.getArg! 1 :: (← go (e.getArg! 2) fuel)
      else if e.isAppOfArity ``List.nil 1 then return []
      else throwError "build_pkg_init_deps: unable to match deps list {e}"
  go deps 10000

/-- `define_is_pkg_init P`: an `IsPkgInit PROP pkg` instance with user part `P`
and dependency part `isPkgInit dep1 ∗ ... ∗ True` computed from
`pkgImportedPkgs pkg`. Must be used where the expected type is known. -/
elab "define_is_pkg_init " P:term:max : term <= ety => do
  let ety ← whnfR (← instantiateMVars ety)
  unless ety.isAppOfArity ``IsPkgInit 3 do
    throwError "define_is_pkg_init: expected type is {ety}, not `IsPkgInit _ _`"
  let prop := ety.getArg! 0
  let bi := ety.getArg! 1
  let pkg := ety.getArg! 2
  let deps ← importedPkgs pkg
  let trueP ← mkAppOptM ``BIBase.pure #[some prop, none, some (mkConst ``True)]
  let mut acc := trueP
  for d in deps.reverse do
    let inst ← synthInstance (← mkAppOptM ``IsPkgInit #[some prop, some bi, some d])
    let pd ← mkAppOptM ``isPkgInit #[some prop, some bi, some d, some inst]
    acc ← mkAppOptM ``BIBase.sep #[some prop, none, some pd, some acc]
  let P ← elabTermEnsuringType P prop
  mkAppOptM ``IsPkgInit.mk #[some prop, some bi, some pkg, some acc, some P]

/-- `build_get_is_pkg_init_wf`: the `GetIsPkgInitWf PROP pkg` instance saying
`get_is_pkg_init pkg = isPkgInit pkg` and recursively the same for the
dependencies. Must be used where the expected type is known. -/
elab "build_get_is_pkg_init_wf" : term <= ety => do
  let ety ← whnfR (← instantiateMVars ety)
  unless ety.isAppOfArity ``GetIsPkgInitWf 3 do
    throwError "build_get_is_pkg_init_wf: expected type is {ety}, not `GetIsPkgInitWf _ _`"
  let prop := ety.getArg! 0
  let bi := ety.getArg! 1
  let pkg := ety.getArg! 2
  let deps ← importedPkgs pkg
  let fTy ← mkArrow (mkConst ``GoString) prop
  let p ← withLocalDeclD `get_is_pkg_init fTy fun g => do
    let inst ← synthInstance (← mkAppOptM ``IsPkgInit #[some prop, some bi, some pkg])
    let lhs := mkApp g pkg
    let rhs ← mkAppOptM ``isPkgInit #[some prop, some bi, some pkg, some inst]
    let mut acc : Lean.Expr := mkConst ``True
    for d in deps.reverse do
      let instD ← synthInstance (← mkAppOptM ``GetIsPkgInitWf #[some prop, some bi, some d])
      let pd ← mkAppOptM ``GetIsPkgInitProp #[some prop, some bi, some d, some instD, some g]
      acc := mkApp2 (mkConst ``And) pd acc
    mkLambdaFVars #[g] (mkApp2 (mkConst ``And) (← mkEq lhs rhs) acc)
  mkAppOptM ``GetIsPkgInitWf.mk #[some prop, some bi, some pkg, some p]

end builders

/-! ## Tactics for `isPkgInit` -/

theorem pkg_init_from_hyp {PROP : Type _} [BI PROP] [BIAffine PROP] {Δ Δ' P T : PROP} {p : Bool}
    (h : Δ ⊣⊢ Δ' ∗ iprop(□?p P)) (c : P ⊢ T) : Δ ⊢ T :=
  h.1.trans (sep_elim_right.trans (intuitionisticallyIf_elim.trans c))

theorem pkg_init_sep_l {PROP : Type _} [BI PROP] [BIAffine PROP] {A B T : PROP} (c : A ⊢ T) :
    iprop(A ∗ B) ⊢ T := sep_elim_left.trans c

theorem pkg_init_sep_r {PROP : Type _} [BI PROP] [BIAffine PROP] {A B T : PROP} (c : B ⊢ T) :
    iprop(A ∗ B) ⊢ T := sep_elim_right.trans c

theorem pkg_init_intuitionistically {PROP : Type _} [BI PROP] {A T : PROP} (c : A ⊢ T) :
    iprop(□ A) ⊢ T := intuitionistically_elim.trans c

section tactics
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- A proof of `P ⊢ target`, where `target` is `isPkgInit pkg`, by unfolding
`isPkgInit` hypotheses into their dependencies. -/
meta partial def pkgInitChain (target P : Lean.Expr) (fuel : Nat := 200) : MetaM (Option Lean.Expr) := do
  if fuel == 0 then return none
  let P ← instantiateMVars P
  if ← withReducible (isDefEq P target) then
    return some (← mkAppOptM ``BIBase.Entails.rfl #[none, none, some P])
  let P' ← whnfR P
  if P'.isAppOfArity ``isPkgInit 4 then
    -- unfold the instance (e.g. built by `define_is_pkg_init`) to `IsPkgInit.mk`
    -- and take its dependency field (`whnf` would also unfold the BI operations)
    let rec instFields (inst : Lean.Expr) (fuel : Nat) : MetaM (Option Lean.Expr) := do
      let inst := (← instantiateMVars inst).headBeta
      if inst.isAppOfArity ``IsPkgInit.mk 5 then return some (inst.getArg! 3)
      if fuel == 0 then return none
      match ← unfoldDefinition? inst with
      | some i => instFields i (fuel - 1)
      | none => return none
    let some deps ← instFields (P'.getArg! 3) 20 | return none
    let some c ← pkgInitChain target deps (fuel - 1) | return none
    let pf1 ← mkAppOptM ``isPkgInit_unfold_deps #[none, none, some (P'.getArg! 2), some (P'.getArg! 3)]
    return some (← mkAppM ``BIBase.Entails.trans #[pf1, c])
  if P'.isAppOfArity ``BIBase.sep 4 then
    if let some c ← pkgInitChain target (P'.getArg! 2) (fuel - 1) then
      return some (← mkAppOptM ``pkg_init_sep_l
        #[none, none, none, some (P'.getArg! 2), some (P'.getArg! 3), none, some c])
    if let some c ← pkgInitChain target (P'.getArg! 3) (fuel - 1) then
      return some (← mkAppOptM ``pkg_init_sep_r
        #[none, none, none, some (P'.getArg! 2), some (P'.getArg! 3), none, some c])
    return none
  if P'.isAppOfArity ``BIBase.intuitionistically 3 then
    if let some c ← pkgInitChain target (P'.getArg! 2) (fuel - 1) then
      return some (← mkAppM ``pkg_init_intuitionistically #[c])
  return none

/-- Solve a goal `isPkgInit pkg` from an intuitionistic
hypothesis, unfolding `isPkgInit` hypotheses into their dependencies. -/
elab "solve_pkg_init" : tactic => do
  ProofModeM.runTactic `solve_pkg_init fun mvar { hyps, goal, .. } => do
    let target ← whnfR (← instantiateMVars goal)
    unless target.isAppOfArity ``isPkgInit 4 do
      throwIPMError "not an isPkgInit goal: {goal}"
    for (_, ivar, p, P) in hypsList hyps do
      unless isTrue p do continue
      if let some c ← pkgInitChain target P then
        let r := hyps.remove true ivar
        mvar.assign (← mkAppOptM ``pkg_init_from_hyp
          #[none, none, none, none, some r.e', some r.out', none, some r.p, some r.pf, some c])
        return
    throwIPMError "could not prove {goal} from the intuitionistic context"

end tactics

/-- Solve an `isPkgInit` goal, or the `isPkgInit` conjuncts
at the front of a `∗` goal. Fails if no progress is made. -/
macro "iPkgInit" : tactic => `(tactic| first
  | solve_pkg_init
  | (isplitr; · solve_pkg_init
     repeat (isplitr; · solve_pkg_init)))

section package_init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

theorem wp_package_init (pkg_name : GoString) [PkgInfo pkg_name] (init_func : val)
    (get_is_pkg_init : GoString → IProp GF) (isPkgInit : IProp GF) (Φ : val → IProp GF)
    (heq : get_is_pkg_init pkg_name = isPkgInit) :
    iprop(ownInitializing get_is_pkg_init ∗
      (ownInitializing get_is_pkg_init -∗
        WP (App (Val init_func) (Val #())) {{ _v, □ isPkgInit ∗ ownInitializing get_is_pkg_init }}))
    ⊢ iprop((ownInitializing get_is_pkg_init ∗ isPkgInit -∗ Φ #()) -∗
      WP (App (Val (package.init pkg_name)) (Val init_func)) {{ Φ }}) := by
  subst heq
  rw [ownInitializing_unseal, package.init_unseal]
  unfold ownInitializingDef
  iintro ⟨Hown, Hpre⟩ HΦ
  wp_call
  icases Hown with ⟨%σ, Hg, #Hinit⟩
  wp_apply_core wp_PackageInitCheck pkg_name σ $$ Hg
  iintro Hg
  cases hσ : (σ !! pkg_name).getD false
  · wp_pures
    wp_apply_core wp_PackageInitStart pkg_name σ $$ Hg
    iintro Hg
    wp_pures
    ihave Hpre := Hpre $$ [Hg]
    · iexists (<[pkg_name := false]> σ)
      iframe Hg
      imodintro
      iapply BigSepM.bigSepM_insert_elim $$ [] Hinit
      simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial
    wp_apply_core wp_wand $$ Hpre
    iintro %_ ⟨#Hinitd, Hown⟩
    icases Hown with ⟨%σ', Hg, #Hinit'⟩
    wp_pures
    wp_apply_core wp_PackageInitFinish pkg_name σ' $$ Hg
    iintro Hg
    iapply HΦ
    iframe Hinitd
    iexists (<[pkg_name := true]> σ')
    iframe Hg
    imodintro
    iapply BigSepM.bigSepM_insert_elim $$ [] Hinit'
    simp only [↓reduceIte]
    iexact Hinitd
  · wp_pures
    iapply HΦ
    cases hl : σ !! pkg_name with
    | none => simp [hl] at hσ
    | some b =>
      simp [hl] at hσ
      subst hσ
      ihave Hx := BigSepM.bigSepM_lookup (Φ := fun k (b : Bool) =>
        if b then get_is_pkg_init k else iprop(True)) hl $$ Hinit
      isplitl [Hg]
      · iexists σ
        iframe Hg
        imodintro
        iexact Hinit
      · simp only [↓reduceIte]
        iexact Hx

end package_init

end Perennial
