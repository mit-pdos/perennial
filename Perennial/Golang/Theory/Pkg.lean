/-
Package initialization.

* `ownInitializing get_is_pkg_init`: permission to run `package.init`
  (exclusive, since Go packages are initialized sequentially).
* `IsPkgInit PROP pkg_name`: the (canonical) post-initialization predicate of a
  package, split into the auto-generated dependency part `isPkgInitDeps` and
  the user-specified part `isPkgInitDef`; `isPkgInit pkg_name` asserts both.
* `IsPkgInitParam PROP pkg_name`: a package whose fact takes a parameter (a family of
  `IsPkgInit` instances); `isPkgInitSome pkg_name`, its fact at some parameter, is what
  its importers' facts hold of it.
* `GetIsPkgInitWf PROP pkg_name`: a pure predicate constraining
  `get_is_pkg_init` to contain the init predicates of `pkg_name` and its
  transitive dependencies.
* `define_is_pkg_init P` (term) builds an `IsPkgInit` instance whose
  dependencies are computed from `pkgImportedPkgs`; `build_get_is_pkg_init_wf`
  (term) builds the `GetIsPkgInitWf` instance.
* Tactics: `solve_pkg_init` (prove a goal `isPkgInit pkg` or `isPkgInitSome pkg`
  from the intuitionistic context), `iPkgInit` (solve such goals and conjuncts
  at the front of the goal).
-/
module

public import Perennial.Golang.Theory.PostLifting
public import Perennial.Golang.Defn.Pkg
public import Perennial.Algebra.BigOp
public meta import Perennial.Golang.Theory.PostLifting

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

noncomputable section init_defns
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

def IsInit (σ : state) : Prop :=
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

noncomputable section init_lb
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-! ## Initialized packages stay initialized

`ownGoState σ` (inside `ownInitializing g`) holds the authority of a ghost map of the packages `σ`
has initialized, which only grows (`GoStateGS.packageMonoName`); its persistent fragment
`ownGoStateLb σ0` names packages known initialized. So every proof that keeps
`ownInitializing g`, whatever it does, keeps them initialized (`wp_ownInitializingLb`): a
package's `wp_initialize'` need not be restated to say so. -/

/-- `ownInitializing g`, with every package `σ0` has initialized initialized. -/
def ownInitializingLb (get_is_pkg_init : GoString → IProp GF) (σ0 : GMap GoString Bool) :
    IProp GF :=
  iprop(∃ package_inited : GMap GoString Bool,
    ownGoState package_inited ∗
    □ ([∗map] pkg_name ↦ inited ∈ package_inited,
      if inited then get_is_pkg_init pkg_name else iprop(True)) ∗
    ⌜pkgInitLe σ0 package_inited⌝)

/-- `ownInitializingLb g σ0` is `ownInitializing g` and the persistent fact that `σ0`'s packages
are initialized. -/
theorem ownInitializingLb_iff (get_is_pkg_init : GoString → IProp GF) (σ0 : GMap GoString Bool) :
    ownInitializingLb get_is_pkg_init σ0 ⊣⊢
      ownInitializing get_is_pkg_init ∗ ownGoStateLb σ0 := by
  rw [ownInitializing_unseal]
  unfold ownInitializingDef ownInitializingLb
  constructor
  · iintro ⟨%σ, Hg, #Hinit, %Hle⟩
    ihave ⟨Hg, #Hlb⟩ := ownGoState_get_lb σ $$ Hg
    isplitl [Hg]
    · iexists σ
      iframe Hg Hinit
    · iapply ownGoStateLb_mono Hle $$ Hlb
  · iintro ⟨⟨%σ, Hg, #Hinit⟩, #Hlb⟩
    ihave %Hle := ownGoStateLb_le σ0 σ $$ Hlb Hg
    iexists σ
    iframe Hg Hinit
    ipureintro; exact Hle

theorem ownInitializing_lb_empty (get_is_pkg_init : GoString → IProp GF) :
    ownInitializing get_is_pkg_init ⊢ ownInitializingLb get_is_pkg_init ∅ := by
  iintro Hown
  iapply (ownInitializingLb_iff get_is_pkg_init ∅).2
  iframe Hown
  iapply ownGoStateLb_empty

/-- **Initialized packages stay initialized**, through any proof that keeps
`ownInitializing g`: from `ownInitializingLb g σ0`, a WP whose postcondition has
`ownInitializing g` ends with `ownInitializingLb g σ0`. -/
theorem wp_ownInitializingLb (get_is_pkg_init : GoString → IProp GF) (σ0 : GMap GoString Bool)
    (e : Expr) (s : Stuckness) (E : CoPset) (Ψ : val → IProp GF) :
    ⊢ ownInitializingLb get_is_pkg_init σ0 -∗
      (ownInitializing get_is_pkg_init -∗
        WP e @ s; E {{ v, ownInitializing get_is_pkg_init ∗ Ψ v }}) -∗
      WP e @ s; E {{ v, ownInitializingLb get_is_pkg_init σ0 ∗ Ψ v }} := by
  iintro Hlb Hwp
  ihave ⟨Hown, #Hl⟩ := (ownInitializingLb_iff get_is_pkg_init σ0).1 $$ Hlb
  iapply wp_wand $$ [Hwp Hown]
  · iapply Hwp $$ Hown
  iintro %v ⟨Hown, HΨ⟩
  iframe HΨ
  iapply (ownInitializingLb_iff get_is_pkg_init σ0).2
  iframe Hown Hl

/-- The triple form: an initializer that meets the standard spec (Perennial's
`initialize'.spec` shape) keeps every package initialized before initialized. -/
theorem initLb_of_initSpec (init : val) (get_is_pkg_init : GoString → IProp GF) (Q : IProp GF)
    (Hstd : {{ ownInitializing get_is_pkg_init }} (App (Val init) (Val #()))
      {{ RET #(); ownInitializing get_is_pkg_init ∗ Q }}) (σ0 : GMap GoString Bool) :
    {{ ownInitializingLb get_is_pkg_init σ0 }} (App (Val init) (Val #()))
      {{ RET #(); ownInitializingLb get_is_pkg_init σ0 ∗ Q }} := by
  iintro %Φ Hlb HΦ
  ihave ⟨Hown, #Hl⟩ := (ownInitializingLb_iff get_is_pkg_init σ0).1 $$ Hlb
  iapply Hstd $$ Hown
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply (ownInitializingLb_iff get_is_pkg_init σ0).2
  iframe Hown Hl

end init_lb

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

/-! ### Packages whose fact takes a parameter

A package's fact may name something chosen by the program's proof rather than fixed by the
package: per-run ghost state that the proof allocates before the program starts (the ghost
name of a registry the package's initializer fills), say. Such a package declares
`IsPkgInitParam PROP pkg` (a family of `IsPkgInit` instances, one per value of `Param`)
instead of a single `IsPkgInit` instance. Code proved at a known parameter uses the
instance at that value (`IsPkgInitParam.inst x`, typically through a local instance taking
the parameter's class as an argument); an importer's fact holds `isPkgInitSome pkg` (the
fact at some parameter: `define_is_pkg_init` writes it), so the importer's `IsPkgInit`
instance does not take the parameter. The parameter does reach the importers'
`GetIsPkgInitWf` instances (`build_get_is_pkg_init_wf` is unchanged): the well-formedness
of `get_is_pkg_init` is what fixes the fact the package's initializer establishes, at the
parameter its importers' initializers rely on. -/

/-- A package whose post-initialization fact is a family of `IsPkgInit` instances indexed
by `Param`. A package has either an `IsPkgInitParam` instance or an unconditional
`IsPkgInit` one, not both. -/
class IsPkgInitParam (PROP : Type _) [BI PROP] (pkg_name : GoString) where
  /-- what the package's fact is parameterized by -/
  Param : Type
  /-- the package's `IsPkgInit` instance at each parameter -/
  inst : Param → IsPkgInit PROP pkg_name

/-- The fact of a parameterized package at some parameter: what its importers' facts hold
of it (`define_is_pkg_init`). -/
def isPkgInitSome (pkg_name : GoString) [IsPkgInitParam PROP pkg_name] : PROP :=
  iprop(∃ x : IsPkgInitParam.Param PROP pkg_name,
    @isPkgInit PROP _ pkg_name (IsPkgInitParam.inst x))

instance isPkgInitSome_pers (pkg_name : GoString) [IsPkgInitParam PROP pkg_name] :
    Persistent (isPkgInitSome (PROP := PROP) pkg_name) := by
  unfold isPkgInitSome; infer_instance

theorem isPkgInitSome_intro (pkg_name : GoString) [IsPkgInitParam PROP pkg_name]
    (x : IsPkgInitParam.Param PROP pkg_name) :
    @isPkgInit PROP _ pkg_name (IsPkgInitParam.inst x) ⊢
      isPkgInitSome (PROP := PROP) pkg_name :=
  exists_intro (Ψ := fun x => @isPkgInit PROP _ pkg_name (IsPkgInitParam.inst x)) x

theorem isPkgInitSome_elim (pkg_name : GoString) [IsPkgInitParam PROP pkg_name] {Q : PROP}
    (h : ∀ x : IsPkgInitParam.Param PROP pkg_name,
      @isPkgInit PROP _ pkg_name (IsPkgInitParam.inst x) ⊢ Q) :
    isPkgInitSome (PROP := PROP) pkg_name ⊢ Q :=
  exists_elim h

instance isPkgInitSome_fromExists (pkg_name : GoString) [IsPkgInitParam PROP pkg_name] :
    Iris.ProofMode.FromExists (isPkgInitSome (PROP := PROP) pkg_name)
      (fun x => @isPkgInit PROP _ pkg_name (IsPkgInitParam.inst x)) :=
  ⟨.rfl⟩

instance isPkgInitSome_intoExists (pkg_name : GoString) [IsPkgInitParam PROP pkg_name] :
    Iris.ProofMode.IntoExists (isPkgInitSome (PROP := PROP) pkg_name)
      (fun x => @isPkgInit PROP _ pkg_name (IsPkgInitParam.inst x)) :=
  ⟨.rfl⟩

/-- `iframe` proves `isPkgInitSome pkg` from the package's fact at a parameter. -/
instance isPkgInitSome_frame (p : Bool) (pkg_name : GoString) [IsPkgInitParam PROP pkg_name]
    (x : IsPkgInitParam.Param PROP pkg_name) :
    Iris.ProofMode.Frame p (@isPkgInit PROP _ pkg_name (IsPkgInitParam.inst x))
      (isPkgInitSome (PROP := PROP) pkg_name) iprop(emp) where
  frame := sep_emp.1.trans (intuitionisticallyIf_elim.trans (isPkgInitSome_intro pkg_name x))

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
`pkgImportedPkgs pkg`. A dependency with an `IsPkgInitParam` instance contributes
`isPkgInitSome dep` instead (whether or not an `IsPkgInit` instance for it is in
scope, so that the fact does not depend on where it is defined). Must be used where
the expected type is known. -/
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
    let pd ← match ← synthInstance? (← mkAppOptM ``IsPkgInitParam #[some prop, some bi, some d]) with
      | some pinst => mkAppOptM ``isPkgInitSome #[some prop, some bi, some d, some pinst]
      | none =>
        let inst ← synthInstance (← mkAppOptM ``IsPkgInit #[some prop, some bi, some d])
        mkAppOptM ``isPkgInit #[some prop, some bi, some d, some inst]
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

/-- A proof of `P ⊢ target`, where `target` is `isPkgInit pkg` or `isPkgInitSome pkg`, by
unfolding `isPkgInit` hypotheses into their dependencies. `failed` holds the packages whose
dependencies were already searched without reaching `target`: the packages form a DAG
(every package reaches `fmt`, `errors`, `sync`, ...), and without it each path to a
package searched its whole dependency graph again (3.5s a call in etcd's server, 45 of
`EtcdServer.LeaseRenew`'s 220s). It only prunes searches that fail, so the proof found is
the one found without it.

A target `isPkgInitSome pkg` is also proved from `pkg`'s fact at a parameter
(`isPkgInit pkg` at an instance that unfolds to `IsPkgInitParam.inst x`). A hypothesis
`isPkgInitSome pkg` is an atom, and the search descends through it under a binder for the
parameter (`isPkgInitSome_elim`), to targets that do not depend on it. -/
meta partial def pkgInitChain (target P : Lean.Expr) (fuel : Nat := 200)
    (failed : Option (IO.Ref (Std.HashSet Lean.Expr)) := none) : MetaM (Option Lean.Expr) := do
  let failed ← match failed with
    | some r => pure r
    | none => IO.mkRef {}
  if fuel == 0 then return none
  let P ← instantiateMVars P
  if ← withReducible (isDefEq P target) then
    return some (← mkAppOptM ``BIBase.Entails.rfl #[none, none, some P])
  let P' ← whnfR P
  if P'.isAppOfArity ``isPkgInit 4 then
    let key := P'.getArg! 2
    -- `target` is `isPkgInitSome key` and `P'` is `key`'s fact at a parameter
    if target.isAppOfArity ``isPkgInitSome 4 then
      if ← withReducible (isDefEq (target.getArg! 2) key) then
        let pinst := target.getArg! 3
        let paramTy ← mkAppOptM ``IsPkgInitParam.Param
          #[some (target.getArg! 0), some (target.getArg! 1), some key, some pinst]
        let x ← mkFreshExprMVar paramTy
        let instX ← mkAppOptM ``IsPkgInitParam.inst
          #[some (target.getArg! 0), some (target.getArg! 1), some key, some pinst, some x]
        if ← isDefEq instX (P'.getArg! 3) then
          let x ← instantiateMVars x
          unless x.hasExprMVar do
            return some (← mkAppOptM ``isPkgInitSome_intro
              #[none, none, some key, some pinst, some x])
    if (← failed.get).contains key then return none
    -- unfold the instance (e.g. built by `define_is_pkg_init`) to `IsPkgInit.mk`
    -- and take its dependency field (`whnf` would also unfold the BI operations)
    let rec instFields (inst : Lean.Expr) (fuel : Nat) : MetaM (Option Lean.Expr) := do
      let inst := (← instantiateMVars inst).headBeta
      if inst.isAppOfArity ``IsPkgInit.mk 5 then return some (inst.getArg! 3)
      if fuel == 0 then return none
      match ← unfoldDefinition? inst with
      | some i => instFields i (fuel - 1)
      | none =>
        -- a projection, e.g. `IsPkgInitParam.inst x`: reduce the instance term only
        let i ← whnf inst
        if i == inst then return none
        instFields i (fuel - 1)
    let some deps ← instFields (P'.getArg! 3) 20 | failed.modify (·.insert key); return none
    let some c ← pkgInitChain target deps (fuel - 1) failed | failed.modify (·.insert key); return none
    let pf1 ← mkAppOptM ``isPkgInit_unfold_deps #[none, none, some (P'.getArg! 2), some (P'.getArg! 3)]
    return some (← mkAppM ``BIBase.Entails.trans #[pf1, c])
  if P'.isAppOfArity ``isPkgInitSome 4 then
    let key := P'.getArg! 2
    if (← failed.get).contains key then return none
    let prop := P'.getArg! 0
    let bi := P'.getArg! 1
    let pinst := P'.getArg! 3
    let paramTy ← mkAppOptM ``IsPkgInitParam.Param #[some prop, some bi, some key, some pinst]
    let r ← withLocalDeclD `x paramTy fun x => do
      let instX ← mkAppOptM ``IsPkgInitParam.inst #[some prop, some bi, some key, some pinst, some x]
      let Px ← mkAppOptM ``isPkgInit #[some prop, some bi, some key, some instX]
      let some c ← pkgInitChain target Px (fuel - 1) failed | return none
      let c ← instantiateMVars c
      -- the proof found must not fix the parameter (it may when the target mentions `key`'s
      -- instance at a parameter: `target` then is not provable from `isPkgInitSome key`)
      if c.hasExprMVar then return none
      return some (← mkLambdaFVars #[x] c)
    let some h := r | failed.modify (·.insert key); return none
    return some (← mkAppOptM ``isPkgInitSome_elim
      #[none, none, some key, some pinst, some target, some h])
  if P'.isAppOfArity ``BIBase.sep 4 then
    if let some c ← pkgInitChain target (P'.getArg! 2) (fuel - 1) failed then
      return some (← mkAppOptM ``pkg_init_sep_l
        #[none, none, none, some (P'.getArg! 2), some (P'.getArg! 3), none, some c])
    if let some c ← pkgInitChain target (P'.getArg! 3) (fuel - 1) failed then
      return some (← mkAppOptM ``pkg_init_sep_r
        #[none, none, none, some (P'.getArg! 2), some (P'.getArg! 3), none, some c])
    return none
  if P'.isAppOfArity ``BIBase.intuitionistically 3 then
    if let some c ← pkgInitChain target (P'.getArg! 2) (fuel - 1) failed then
      return some (← mkAppM ``pkg_init_intuitionistically #[c])
  return none

/-- Solve a goal `isPkgInit pkg` or `isPkgInitSome pkg` from an intuitionistic
hypothesis, unfolding `isPkgInit` hypotheses into their dependencies. -/
elab "solve_pkg_init" : tactic => do
  ProofModeM.runTactic `solve_pkg_init fun mvar { hyps, goal, .. } => do
    let target ← whnfR (← instantiateMVars goal)
    unless target.isAppOfArity ``isPkgInit 4 || target.isAppOfArity ``isPkgInitSome 4 do
      throwIPMError "not an isPkgInit goal: {goal}"
    let failed ← IO.mkRef ({} : Std.HashSet Lean.Expr)
    for (_, ivar, p, P) in hypsList hyps do
      unless isTrue p do continue
      if let some c ← pkgInitChain target P (failed := some failed) then
        let r := hyps.remove true ivar
        mvar.assign (← mkAppOptM ``pkg_init_from_hyp
          #[none, none, none, none, some r.e', some r.out', none, some r.p, some r.pf, some c])
        return
    throwIPMError "could not prove {goal} from the intuitionistic context"

end tactics

/-- Solve an `isPkgInit` (or `isPkgInitSome`) goal, or such conjuncts
at the front of a `∗` goal. Fails if no progress is made. -/
macro "iPkgInit" : tactic => `(tactic| first
  | solve_pkg_init
  | (isplitr; · solve_pkg_init
     repeat (isplitr; · solve_pkg_init)))

section package_init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- The initialization of a package by its function `init_func` (a function value,
`rec: f x := body`), which must not panic. -/
theorem wp_package_init (pkg_name : GoString) [PkgInfo pkg_name] (f x : Binder) (body : Expr)
    (get_is_pkg_init : GoString → IProp GF) (isPkgInit : IProp GF) (Φ : val → IProp GF)
    (heq : get_is_pkg_init pkg_name = isPkgInit) :
    let init_func := RecV f x body
    iprop(ownInitializing get_is_pkg_init ∗
      (ownInitializing get_is_pkg_init -∗
        WP (App (Val init_func) (Val #())) {{ v, ⌜v.isPanic = false⌝ ∗ □ isPkgInit ∗
          ownInitializing get_is_pkg_init }}))
    ⊢ iprop((ownInitializing get_is_pkg_init ∗ isPkgInit -∗ Φ #()) -∗
      WP (App (Val (package.init pkg_name)) (Val init_func)) {{ Φ }}) := by
  intro init_func
  have hinit : init_func.isPanic = false := rfl
  clear_value init_func
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
    iintro %_ ⟨%Hnp, #Hinitd, Hown⟩
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
