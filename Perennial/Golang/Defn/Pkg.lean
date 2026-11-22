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

/-- A package variable that goose does not translate: an entry of a package's
`skipped' : List go.SkippedVar` (in `Perennial/Code/<pkg>.lean`), one per variable listed in a
`skip` entry of the package's goose config. The variable has no Lean name, allocation or
initialization step, so no translated or hand-written code can name it. (Hand-written Lean can
still write the variable's address from a literal name, `GlobalVarAddr go!"pkg.X"`: that steps,
to the address Go would give, but the variable is never allocated, so a load or store through it
is stuck, and `etc/trusted-delta.py` flags every such literal, `global-var-addr`.)

**The trusted claim** of each entry: not running the variable's Go initializer is unobservable
(it terminates, cannot panic, and has no effect beyond the variable), for the reason it gives.
The record is informational, unused by the semantics: tools that read the Lean environment list
the entries in a result's import closure, and a change to an entry (a Go upgrade that adds,
moves or changes a skipped variable) is a change to the trusted base. `name` is the variable's
`pkg.X` (`pkg._@file.go:L` for a blank one, named by its position): a string, which gives no
handle on the variable. `decl` is its Go declaration on one line (a long one cut short, ending
with a hash of the whole declaration), so that a changed initializer changes the entry. -/
structure SkippedVar where
  name : String
  reason : String
  decl : String

end go

end Perennial
