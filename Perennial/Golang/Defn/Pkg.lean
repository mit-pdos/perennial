/-
Port of `new/golang/defn/pkg.v`: package initialization.
-/
import Perennial.Golang.Defn.PostLang

namespace Perennial

/-- `PkgInfo` associates a pkg_name to its static information. -/
class PkgInfo (pkg_name : GoString) where
  pkgImportedPkgs : List GoString

-- `pkgImportedPkgs pkg_name` takes `pkg_name` explicitly, as in Rocq.
export PkgInfo (pkgImportedPkgs)

namespace package
section defns
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

def initDef (pkg_name : GoString) : val :=
  λ: "init",
    if: PackageInitCheck pkg_name #() then #()
    else PackageInitStart pkg_name #() ;; "init" #() ;; PackageInitFinish pkg_name #()
@[irreducible] def init (pkg_name : GoString) : val := initDef pkg_name
theorem init_unseal : init = initDef := by with_unfolding_all rfl
end defns
end package

end Perennial
