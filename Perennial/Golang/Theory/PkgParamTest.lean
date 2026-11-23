/-
Regression tests for packages whose fact takes a parameter (`IsPkgInitParam`,
`isPkgInitSome`; `Perennial/Golang/Theory/Pkg.lean`).

Four hand-written packages, each with an initializer in the shape goose emits:
`toyleaf` (no imports), `toyparam` (imports `toyleaf`; its fact names a parameter, a
`ToyGS` the program's proof chooses), `toyimp` (imports `toyparam`) and `toytop` (imports
`toyimp`). The tests check that
* `define_is_pkg_init` gives `toyimp` a fact holding `isPkgInitSome toyparam`, and its
  `IsPkgInit` instance takes no parameter;
* `build_get_is_pkg_init_wf` is unchanged: `toyimp`'s `GetIsPkgInitWf` takes the
  parameter, and fixes `toyparam`'s fact at it;
* the initializers' proofs go through as for any package (`is_pkg_init_finish` proves an
  `isPkgInitSome` conjunct from the fact at a parameter);
* `solve_pkg_init` proves `isPkgInitSome` targets, and descends through `isPkgInitSome`
  hypotheses (but never proves a fact at a parameter from `isPkgInitSome`).
-/
module

public import Perennial.Golang.Theory

@[expose] public section

namespace Perennial
open Iris Iris.BI Iris.ProofMode

noncomputable section

namespace pkg_id
def toyleaf : GoString := go!"example.com/toyleaf"
def toyparam : GoString := go!"example.com/toyparam"
def toyimp : GoString := go!"example.com/toyimp"
def toytop : GoString := go!"example.com/toytop"
end pkg_id

instance : PkgInfo pkg_id.toyleaf where pkgImportedPkgs := []
instance : PkgInfo pkg_id.toyparam where pkgImportedPkgs := [pkg_id.toyleaf]
instance : PkgInfo pkg_id.toyimp where pkgImportedPkgs := [pkg_id.toyparam]
instance : PkgInfo pkg_id.toytop where pkgImportedPkgs := [pkg_id.toyimp]

section code
variable [GooseExts] [GoGlobalContext]

/-- An initializer: run `package.init pkg` on a body calling `deps`' initializers in order. -/
def toyInit (pkg : GoString) (deps : List val) : val :=
  LamV BAnon (App (Val (package.init pkg)) (Lam BAnon
    (App (Val exceptionDo) (deps.foldr
      (fun d e => App (App (Val exceptionSeq) (Lam BAnon e))
        (App (Val doExecute) (App (Val d) (Val #()))))
      (App (Val doExecute) (Val #()))))))

def toyleaf.initialize' : val := toyInit pkg_id.toyleaf []
def toyparam.initialize' : val := toyInit pkg_id.toyparam [toyleaf.initialize']
def toyimp.initialize' : val := toyInit pkg_id.toyimp [toyparam.initialize']
def toytop.initialize' : val := toyInit pkg_id.toytop [toyimp.initialize']

end code

/-- What `toyparam`'s fact is parameterized by: chosen by the program's proof (in a real
package, the ghost name of state the proof allocates for the run). -/
class ToyGS where
  γ : Nat
  small : γ < 100

section instances
variable {hlc : HasLC} {GF : BundledGFunctors}

instance : IsPkgInit (IProp GF) pkg_id.toyleaf := define_is_pkg_init iprop(True)
instance : GetIsPkgInitWf (IProp GF) pkg_id.toyleaf := build_get_is_pkg_init_wf

/-- `toyparam`'s fact at each parameter. -/
instance toyparam.isPkgInitParam : IsPkgInitParam (IProp GF) pkg_id.toyparam where
  Param := ToyGS
  inst x := define_is_pkg_init iprop(⌜x.γ < 100⌝)

/-- `toyparam`'s fact at the parameter in scope, for code proved at a known parameter. -/
instance toyparam.isPkgInit_inst [x : ToyGS] : IsPkgInit (IProp GF) pkg_id.toyparam :=
  IsPkgInitParam.inst (PROP := IProp GF) (pkg_name := pkg_id.toyparam) x

instance toyparam.getIsPkgInitWf [ToyGS] : GetIsPkgInitWf (IProp GF) pkg_id.toyparam :=
  build_get_is_pkg_init_wf

/-- No `ToyGS` in scope: `toyimp`'s fact names `toyparam` through `isPkgInitSome`. -/
instance toyimp.isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.toyimp := define_is_pkg_init iprop(True)

example : isPkgInitDeps (PROP := IProp GF) pkg_id.toyimp =
    iprop(isPkgInitSome (PROP := IProp GF) pkg_id.toyparam ∗ True) := rfl

/-- The well-formedness takes the parameter, explicitly. -/
instance toyimp.getIsPkgInitWf [ToyGS] : GetIsPkgInitWf (IProp GF) pkg_id.toyimp :=
  build_get_is_pkg_init_wf

/-- Defined where a `ToyGS` is in scope, the fact is the same: `define_is_pkg_init` takes
`isPkgInitSome` for a parameterized package whatever instances are in scope. -/
example [ToyGS] : (define_is_pkg_init iprop(True) : IsPkgInit (IProp GF) pkg_id.toyimp) =
    toyimp.isPkgInit_inst := rfl

instance toytop.isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.toytop := define_is_pkg_init iprop(True)
instance toytop.getIsPkgInitWf [ToyGS] : GetIsPkgInitWf (IProp GF) pkg_id.toytop :=
  build_get_is_pkg_init_wf

/-- `toyimp`'s well-formedness fixes `toyparam`'s fact at the parameter in scope. -/
example [ToyGS] (g : GoString → IProp GF) (h : GetIsPkgInitProp pkg_id.toyimp g) :
    g pkg_id.toyparam = isPkgInit (PROP := IProp GF) pkg_id.toyparam := h.2.1.1

end instances

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

theorem toyleaf.wp_initialize' (g : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.toyleaf g) :
    {{ ownInitializing g }} (App (Val toyleaf.initialize') (Val #()))
    {{ RET #(); ownInitializing g ∗ isPkgInit (PROP := IProp GF) pkg_id.toyleaf }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

/-- The parameterized package's initializer, at the parameter in scope. -/
theorem toyparam.wp_initialize' [ToyGS] (g : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.toyparam g) :
    {{ ownInitializing g }} (App (Val toyparam.initialize') (Val #()))
    {{ RET #(); ownInitializing g ∗ isPkgInit (PROP := IProp GF) pkg_id.toyparam }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply toyleaf.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hleaf⟩
  iframe Hown
  is_pkg_init_finish
  ipureintro
  exact ToyGS.small

/-- An importer's initializer: its fact's `isPkgInitSome toyparam` comes from `toyparam`'s
fact at the parameter its well-formedness names. -/
theorem toyimp.wp_initialize' [ToyGS] (g : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.toyimp g) :
    {{ ownInitializing g }} (App (Val toyimp.initialize') (Val #()))
    {{ RET #(); ownInitializing g ∗ isPkgInit (PROP := IProp GF) pkg_id.toyimp }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply toyparam.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hparam⟩
  iframe Hown
  is_pkg_init_finish

theorem toytop.wp_initialize' [ToyGS] (g : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.toytop g) :
    {{ ownInitializing g }} (App (Val toytop.initialize') (Val #()))
    {{ RET #(); ownInitializing g ∗ isPkgInit (PROP := IProp GF) pkg_id.toytop }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply toyimp.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Himp⟩
  iframe Hown
  is_pkg_init_finish

/-! `solve_pkg_init` and `iPkgInit` with `isPkgInitSome`. -/

/-- An `isPkgInitSome` target, found as an atom in a dependency's fact. -/
example : ⊢ isPkgInit (PROP := IProp GF) pkg_id.toytop -∗
    isPkgInitSome (PROP := IProp GF) pkg_id.toyparam := by
  iintro #H
  solve_pkg_init

/-- An `isPkgInitSome` target, from the fact at a parameter. -/
example [ToyGS] : ⊢ isPkgInit (PROP := IProp GF) pkg_id.toyparam -∗
    isPkgInitSome (PROP := IProp GF) pkg_id.toyparam := by
  iintro #H
  solve_pkg_init

/-- The same by `iframe`. -/
example [ToyGS] : ⊢ isPkgInit (PROP := IProp GF) pkg_id.toyparam -∗
    isPkgInitSome (PROP := IProp GF) pkg_id.toyparam := by
  iintro #H
  iframe H

/-- Descending through `isPkgInitSome` to a dependency of the parameterized package. -/
example : ⊢ isPkgInitSome (PROP := IProp GF) pkg_id.toyparam -∗
    isPkgInit (PROP := IProp GF) pkg_id.toyleaf := by
  iintro #H
  solve_pkg_init

/-- ... from further up, with other conjuncts (`iPkgInit`). -/
example : ⊢ isPkgInit (PROP := IProp GF) pkg_id.toytop -∗
    isPkgInit (PROP := IProp GF) pkg_id.toyleaf ∗ isPkgInitSome (PROP := IProp GF) pkg_id.toyparam ∗
      isPkgInit (PROP := IProp GF) pkg_id.toyimp := by
  iintro #H
  iPkgInit
  solve_pkg_init

/-- `isPkgInitSome` does not give the fact at a particular parameter. -/
example [ToyGS] : ⊢ isPkgInit (PROP := IProp GF) pkg_id.toytop -∗ ⌜False⌝ -∗
    isPkgInit (PROP := IProp GF) pkg_id.toyparam := by
  iintro #H %Hf
  fail_if_success solve_pkg_init
  exact Hf.elim

end proofs

end

end Perennial
