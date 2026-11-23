/-
Trusted code for `github.com/mit-pdos/perennial/goose/testdata/examples/modeloverlay`, in
namespace `github_com.mit_pdos.perennial.goose.testdata.examples.modeloverlay` (as the generated
package): the primitive stub `choose` of its Go model overlay
(`goose/testdata/models/modeloverlay/model.go`).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.mit_pdos.perennial.goose.testdata.examples.modeloverlay
section code
variable [GooseExts] [GoGlobalContext]

/-- `choose()`: an arbitrary boolean (its Go body returns `false`). -/
def choose.impl : val :=
  λ: <>, ArbitraryInt =⟨go.uint64⟩ #(W64 0)

end code
end github_com.mit_pdos.perennial.goose.testdata.examples.modeloverlay

end Perennial
