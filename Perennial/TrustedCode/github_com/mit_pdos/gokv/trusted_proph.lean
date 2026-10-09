/-
Trusted Go model of `github.com/mit-pdos/gokv/trusted_proph`, in namespace
`github_com.mit_pdos.gokv.trusted_proph`, as the generated package.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

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
