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

end go

end Perennial
