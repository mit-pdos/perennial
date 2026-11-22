/-
Checks of the aliases of `goose/testdata/examples/xpkgalias`: every alias has a reducible
descriptor `A.ty`, defined as that of the type it denotes, whether its package's configuration
translates it (`dep.A`), axiomatizes it (`dep.L`, `dep.M`, `dep.G`, `dep.PtrLater`,
`dep.Tagged`, `xpkgalias.C`) or trusts it (`dep.Tr`).
-/
module

public import Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.xpkgalias
public import Perennial.Code.sync

@[expose] public section

namespace Perennial
namespace github_com.mit_pdos.perennial.goose.testdata.examples.xpkgalias
variable [GooseExts] [GoGlobalContext]

example : dep.A.ty = dep.X.ty := rfl
example : dep.L.ty = dep2.Y.ty := rfl
-- `sync` is not imported by dep's translation: the descriptor is written out
example : dep.M.ty = sync.Mutex.ty := by unfold sync.Mutex.ty; rfl
example (T : go.GoType) : dep.G.ty T = dep2.Box.ty T := rfl
example : dep.Tr.ty = go.GoType.PointerType dep.X.ty := rfl
example : dep.PtrLater.ty = go.GoType.PointerType dep.Later.ty := rfl
example : C.ty = dep.A.ty := rfl
-- an unnamed struct type's fields carry their tags
example : dep.Tagged.ty = go.StructType dep.«struct#d5167f74».fields := rfl
example : dep.«struct#d5167f74».fields = [go.field_decl.Field go!"f" go.uint64 go!"json:\"f\""] := by
  unfold dep.«struct#d5167f74».fields; rfl

end github_com.mit_pdos.perennial.goose.testdata.examples.xpkgalias
end Perennial
