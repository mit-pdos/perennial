/-
Port of `new/trusted_code/github_com/mit_pdos/gokv/trusted_proph.v`. Rocq
defines these at top level; here they are in namespace
`github_com.mit_pdos.gokv.trusted_proph`, as the generated package.
-/
import Perennial.Golang.Defn.Pre

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.mit_pdos.gokv.trusted_proph
section defs
variable [FfiSyntax]

def NewProph.impl : val :=
  λ: <>, NewProph

def ResolveBytes.impl : val :=
  λ: "p" "slice",
  let: "s" := Convert (go.SliceType go.byte) go.string "slice" in
  ResolveProph "p" "s"

end defs
end github_com.mit_pdos.gokv.trusted_proph

end Perennial
