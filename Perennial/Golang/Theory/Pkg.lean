/-
Port of `new/golang/theory/pkg.v`: package initialization.

* `own_initializing get_is_pkg_init`: permission to run `package.init`
  (exclusive, since Go packages are initialized sequentially).
* `IsPkgInit PROP pkg_name`: the (canonical) post-initialization predicate of a
  package, split into the auto-generated dependency part `is_pkg_init_deps` and
  the user-specified part `is_pkg_init_def`; `is_pkg_init pkg_name` asserts both.
* `GetIsPkgInitWf PROP pkg_name`: a pure predicate constraining
  `get_is_pkg_init` to contain the init predicates of `pkg_name` and its
  transitive dependencies.
* `define_is_pkg_init P` (term) builds an `IsPkgInit` instance whose
  dependencies are computed from `pkg_imported_pkgs`; `build_get_is_pkg_init_wf`
  (term) builds the `GetIsPkgInitWf` instance.
* Tactics: `solve_pkg_init` (prove a goal `is_pkg_init pkg` from the
  intuitionistic context), `iPkgInit` (solve `is_pkg_init` goals and conjuncts
  at the front of the goal).
-/
import Perennial.Golang.Theory.Assume
import Perennial.Golang.Defn.Pkg
import Perennial.Algebra.BigOp

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

noncomputable section init_defns
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]

def is_init [ffi_model] (σ : state) : Prop :=
  σ.go_state.package_state = ∅

/-- Permission to run `package.init`. `get_is_pkg_init` maps every package to
its agreed-upon post-init predicate. -/
def own_initializing_def (get_is_pkg_init : go_string → IProp GF) : IProp GF :=
  iprop(∃ package_inited : gmap go_string Bool,
    "Hg" ∷ own_go_state package_inited ∗
    "#Hinit" ∷ □ ([∗map] pkg_name ↦ inited ∈ package_inited,
      if inited then get_is_pkg_init pkg_name else iprop(True)))

/-- Rocq `Opaque own_initializing`. -/
@[irreducible] def own_initializing (get_is_pkg_init : go_string → IProp GF) : IProp GF :=
  own_initializing_def get_is_pkg_init

theorem own_initializing_unseal : @own_initializing = @own_initializing_def := by
  funext; with_unfolding_all rfl

end init_defns

section package_init_and_defined
variable {PROP : Type _} [BI PROP]

/-- `IsPkgInit PROP pkg_name` connects a package name (the full package path) to
its post-initialization predicate. There should be only one instance for each
package. -/
class IsPkgInit (PROP : Type _) [BI PROP] (pkg_name : go_string) where
  /-- auto-generated; includes the `is_pkg_init` of the dependencies -/
  is_pkg_init_deps : PROP
  /-- user-specified -/
  is_pkg_init_def : PROP

export IsPkgInit (is_pkg_init_deps is_pkg_init_def)

def is_pkg_init_wrap (pkg_name : go_string) [IsPkgInit PROP pkg_name] : PROP :=
  iprop("#Hdeps" ∷ □ is_pkg_init_deps (PROP := PROP) pkg_name ∗
    "#Hinit" ∷ □ is_pkg_init_def (PROP := PROP) pkg_name)

/-- `is_pkg_init pkg_name` asserts the predicate of the `IsPkgInit` instance
(Rocq `Opaque is_pkg_init`). -/
@[irreducible] def is_pkg_init (pkg_name : go_string) [IsPkgInit PROP pkg_name] : PROP :=
  is_pkg_init_wrap pkg_name

theorem is_pkg_init_unfold (pkg_name : go_string) [IsPkgInit PROP pkg_name] :
    is_pkg_init (PROP := PROP) pkg_name =
      iprop("#Hdeps" ∷ □ is_pkg_init_deps (PROP := PROP) pkg_name ∗
        "#Hinit" ∷ □ is_pkg_init_def (PROP := PROP) pkg_name) := by
  with_unfolding_all rfl

instance is_pkg_init_pers (pkg_name : go_string) [IsPkgInit PROP pkg_name] :
    Persistent (is_pkg_init (PROP := PROP) pkg_name) := by
  rw [is_pkg_init_unfold]; unfold named; infer_instance

/-- Access the user-defined init predicate. -/
theorem is_pkg_init_access (pkg_name : go_string) [IsPkgInit PROP pkg_name] :
    is_pkg_init (PROP := PROP) pkg_name ⊢ is_pkg_init_def pkg_name := by
  rw [is_pkg_init_unfold]
  iintro ⟨_, #H⟩
  iexact H

theorem is_pkg_init_unfold_deps (pkg_name : go_string) [IsPkgInit PROP pkg_name] :
    is_pkg_init (PROP := PROP) pkg_name ⊢ is_pkg_init_deps pkg_name := by
  rw [is_pkg_init_unfold]
  iintro ⟨#H, _⟩
  iexact H

/-- Maps `pkg_name` to a pure predicate that constrains `get_is_pkg_init` to
have all of the init predicates for `pkg_name` and its transitive dependencies. -/
class GetIsPkgInitWf (PROP : Type _) [BI PROP] (pkg_name : go_string) where
  get_is_pkg_init_prop_def : (go_string → PROP) → Prop

/-- Rocq `get_is_pkg_init_prop pkg_name get_is_pkg_init`. -/
abbrev get_is_pkg_init_prop (pkg_name : go_string) [GetIsPkgInitWf PROP pkg_name]
    (get_is_pkg_init : go_string → PROP) : Prop :=
  GetIsPkgInitWf.get_is_pkg_init_prop_def pkg_name get_is_pkg_init

end package_init_and_defined

/-! ## Building `IsPkgInit` and `GetIsPkgInitWf` instances -/

section builders
open Lean Elab Term Meta

/-- The list of imported packages of `pkg` (from its `PkgInfo` instance), as a
list of expressions. -/
def importedPkgs (pkg : Expr) : TermElabM (List Expr) := do
  let deps ← whnf (← mkAppOptM ``pkg_imported_pkgs #[some pkg, none])
  let rec go (e : Expr) (fuel : Nat) : TermElabM (List Expr) := do
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
and dependency part `is_pkg_init dep1 ∗ ... ∗ True` computed from
`pkg_imported_pkgs pkg`. Must be used where the expected type is known. -/
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
    let pd ← mkAppOptM ``is_pkg_init #[some prop, some bi, some d, some inst]
    acc ← mkAppOptM ``BIBase.sep #[some prop, none, some pd, some acc]
  let P ← elabTermEnsuringType P prop
  mkAppOptM ``IsPkgInit.mk #[some prop, some bi, some pkg, some acc, some P]

/-- `build_get_is_pkg_init_wf`: the `GetIsPkgInitWf PROP pkg` instance saying
`get_is_pkg_init pkg = is_pkg_init pkg` and recursively the same for the
dependencies. Must be used where the expected type is known. -/
elab "build_get_is_pkg_init_wf" : term <= ety => do
  let ety ← whnfR (← instantiateMVars ety)
  unless ety.isAppOfArity ``GetIsPkgInitWf 3 do
    throwError "build_get_is_pkg_init_wf: expected type is {ety}, not `GetIsPkgInitWf _ _`"
  let prop := ety.getArg! 0
  let bi := ety.getArg! 1
  let pkg := ety.getArg! 2
  let deps ← importedPkgs pkg
  let fTy ← mkArrow (mkConst ``go_string) prop
  let p ← withLocalDeclD `get_is_pkg_init fTy fun g => do
    let inst ← synthInstance (← mkAppOptM ``IsPkgInit #[some prop, some bi, some pkg])
    let lhs := mkApp g pkg
    let rhs ← mkAppOptM ``is_pkg_init #[some prop, some bi, some pkg, some inst]
    let mut acc : Expr := mkConst ``True
    for d in deps.reverse do
      let instD ← synthInstance (← mkAppOptM ``GetIsPkgInitWf #[some prop, some bi, some d])
      let pd ← mkAppOptM ``get_is_pkg_init_prop #[some prop, some bi, some d, some instD, some g]
      acc := mkApp2 (mkConst ``And) pd acc
    mkLambdaFVars #[g] (mkApp2 (mkConst ``And) (← mkEq lhs rhs) acc)
  mkAppOptM ``GetIsPkgInitWf.mk #[some prop, some bi, some pkg, some p]

end builders

/-! ## Tactics for `is_pkg_init` -/

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

/-- A proof of `P ⊢ target`, where `target` is `is_pkg_init pkg`, by unfolding
`is_pkg_init` hypotheses into their dependencies. -/
partial def pkgInitChain (target P : Expr) (fuel : Nat := 200) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let P ← instantiateMVars P
  if ← withReducible (isDefEq P target) then
    return some (← mkAppM ``BIBase.Entails.rfl #[])
  let P' ← whnfR P
  if P'.isAppOfArity ``is_pkg_init 4 then
    let deps ← mkAppM ``is_pkg_init_deps #[P'.getArg! 2]
    let deps ← withTransparency .instances <| whnf deps
    let some c ← pkgInitChain target deps (fuel - 1) | return none
    let pf1 ← mkAppOptM ``is_pkg_init_unfold_deps #[none, none, some (P'.getArg! 2), some (P'.getArg! 3)]
    return some (← mkAppM ``BIBase.Entails.trans #[pf1, c])
  if P'.isAppOfArity ``BIBase.sep 4 then
    if let some c ← pkgInitChain target (P'.getArg! 2) (fuel - 1) then
      return some (← mkAppM ``pkg_init_sep_l #[c])
    if let some c ← pkgInitChain target (P'.getArg! 3) (fuel - 1) then
      return some (← mkAppM ``pkg_init_sep_r #[c])
    return none
  if P'.isAppOfArity ``BIBase.intuitionistically 3 then
    if let some c ← pkgInitChain target (P'.getArg! 2) (fuel - 1) then
      return some (← mkAppM ``pkg_init_intuitionistically #[c])
  return none

/-- Rocq `solve_pkg_init`: solve a goal `is_pkg_init pkg` from an intuitionistic
hypothesis, unfolding `is_pkg_init` hypotheses into their dependencies. -/
elab "solve_pkg_init" : tactic => do
  ProofModeM.runTactic `solve_pkg_init fun mvar { hyps, goal, .. } => do
    let target ← whnfR (← instantiateMVars goal)
    unless target.isAppOfArity ``is_pkg_init 4 do
      throwIPMError "not an is_pkg_init goal: {goal}"
    for (_, ivar, p, P) in hypsList hyps do
      unless isTrue p do continue
      if let some c ← pkgInitChain target P then
        let r := hyps.remove true ivar
        mvar.assign (← mkAppM ``pkg_init_from_hyp #[r.pf, c])
        return
    throwIPMError "could not prove {goal} from the intuitionistic context"

end tactics

/-- Rocq `iPkgInit`: solve an `is_pkg_init` goal, or the `is_pkg_init` conjuncts
at the front of a `∗` goal. Fails if no progress is made. -/
macro "iPkgInit" : tactic => `(tactic| first
  | solve_pkg_init
  | (isplitr; · solve_pkg_init
     repeat (isplitr; · solve_pkg_init)))

section package_init
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

theorem wp_package_init (pkg_name : go_string) [PkgInfo pkg_name] (init_func : val)
    (get_is_pkg_init : go_string → IProp GF) (is_pkg_init : IProp GF) (Φ : val → IProp GF)
    (heq : get_is_pkg_init pkg_name = is_pkg_init) :
    iprop(own_initializing get_is_pkg_init ∗
      (own_initializing get_is_pkg_init -∗
        WP (App (Val init_func) (Val #())) {{ _v, □ is_pkg_init ∗ own_initializing get_is_pkg_init }}))
    ⊢ iprop((own_initializing get_is_pkg_init ∗ is_pkg_init -∗ Φ #()) -∗
      WP (App (Val (package.init pkg_name)) (Val init_func)) {{ Φ }}) := by
  subst heq
  rw [own_initializing_unseal, package.init_unseal]
  unfold own_initializing_def
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
