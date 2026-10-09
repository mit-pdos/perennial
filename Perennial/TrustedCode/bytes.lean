/-
Trusted model of `bytes` (namespace `bytes`, as the generated package).
-/
import Perennial.Golang.Defn.Pre

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace bytes
section code
variable [FfiSyntax] [GoGlobalContext]

/-- `bytes.Compare(a, b)`: `-1`, `0` or `+1` as `a` is lexicographically less than, equal
to or greater than `b` (a nil slice is the empty one). Go implements it in
`internal/bytealg` (assembly); the model compares the two slices' contents as strings,
whose `<` is bytewise lexicographic, as `bytes.Equal` does with `==`. -/
def Compare.impl : val :=
  λ: "a" "b",
    let: "sa" := Convert (go.SliceType go.byte) go.string "a" in
    let: "sb" := Convert (go.SliceType go.byte) go.string "b" in
    if: "sa" <⟨go.string⟩ "sb" then #(W64 (-1))
    else if: "sa" =⟨go.string⟩ "sb" then #(W64 0)
    else #(W64 1)

end code
end bytes

end Perennial
