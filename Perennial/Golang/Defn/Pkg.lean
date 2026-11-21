/-
Package initialization.
-/
module

public import Perennial.Golang.Defn.PostLang

@[expose] public section

namespace Perennial

/-- `PkgInfo` associates a pkg_name to its static information. -/
class PkgInfo (pkg_name : GoString) where
  pkgImportedPkgs : List GoString

-- `pkgImportedPkgs pkg_name` takes `pkg_name` explicitly.
export PkgInfo (pkgImportedPkgs)

namespace package
section defns
variable [GooseExts] [GoLocalContext] [GoGlobalContext]

def initDef (pkg_name : GoString) : val :=
  λ: "init",
    if: PackageInitCheck pkg_name #() then #()
    else PackageInitStart pkg_name #() ;; "init" #() ;; PackageInitFinish pkg_name #()
@[irreducible] def init (pkg_name : GoString) : val := initDef pkg_name
theorem init_unseal : init = initDef := by with_unfolding_all rfl
end defns
end package

namespace go

/-- The model of a package variable's initializer that is skipped: `def X.init : val :=
go.skipInit` in `Perennial/TrustedCode`, for a variable `X` listed as `trusted` in its package's
`.toml`. It does nothing.

**The trusted claim** of each use: *Go's initializer of the variable can be skipped.* Goose emits
no `GlobalAlloc` for a `trusted` variable (its `X.init` is its whole initialization), so the
variable is left unallocated: nothing gives a points-to for it, and any load or store of it is
stuck, so a proof must show that no verified code reaches one. Taking its address (`&X`,
`GlobalVarAddr`) steps, to the address Go would give: the model's executions are a superset of
Go's. Go's initializer must therefore have no effect that verified code can observe beyond the
variable itself (no panic, no other variable written, nothing in the outside world the model
tracks); each use's docstring says why that holds.

Reducible, so that `wp_call` (and `wp_auto`) step through `X.init` to the no-op;
`grep go.skipInit` lists every skipped initializer. -/
@[reducible] def skipInit [GooseExts] [GoGlobalContext] : val := λ: <>, #()

/-- A package variable that goose does not translate: an entry of a package's
`skipped' : List go.SkippedVar` (in `Perennial/Code/<pkg>.lean`), one per variable listed in a
`skip` entry of the package's goose config. The variable has no Lean name, allocation or
initialization step, so no translated or hand-written code can name it.

**The trusted claim** of each entry: not running the variable's Go initializer is unobservable
(it terminates, cannot panic, and has no effect beyond the variable), for the reason it gives.
The record is informational, unused by the semantics: tools that read the Lean environment list
the entries in a result's import closure. `name` is the variable's `pkg.X` (`pkg._@file.go:L:
var _ ...` for a blank one): a string, which gives no handle on the variable. -/
structure SkippedVar where
  name : String
  reason : String

end go

end Perennial
