/-
Trusted code for `github.com/goose-lang/primitive/disk` (namespace
`github_com.goose_lang.primitive.disk`, as the generated package), built on the
disk FFI of `Perennial.GooseLang.Ffi.DiskFfi.Impl`.

TODO: this isn't correct, the new translation needs certain go_type definitions.
-/
module

public import Perennial.Golang.Defn
public import Perennial.GooseLang.Ffi.DiskFfi.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.goose_lang.primitive.disk

/-
This is generalized over `ext` so functions that are generalized over `ext`
can refer to it. The only definition in a goose translation that is
specialized to a concrete FFI is the Assumptions propclass. So, only `ⁱᵐᵖˡ`
stuff should be specialized to the ffi in trusted code.
-/
section disk_consts
variable [FfiSyntax] [GoGlobalContext]
def BlockSize : val :=
  #(W64 4096)
end disk_consts

section disk
attribute [local instance] disk_op disk_model
variable [GoGlobalContext]

def Get.impl : val :=
  λ: <>, ExtV ()

def Read.impl : val :=
  λ: "a",
  let: "p" := ExternalOp DiskOp.ReadOp "a" in
  FullSlice (go.ArrayType 4096 go.byte) ("p", #(W64 0), #(W64 4096), #(W64 4096))

def ReadTo.impl : val :=
  λ: "a" "buf",
  let: "p" := ExternalOp DiskOp.ReadOp "a" in
  FuncResolve "copy" [go.SliceType go.byte] #() "buf" ("p", #(W64 4096), #(W64 4096))

def Write.impl : val :=
  λ: "a" "b",
  ExternalOp DiskOp.WriteOp ("a", IndexRef (go.SliceType go.byte) ("b", #(W64 0)))

def Barrier.impl : val :=
  λ: <>, #()

def Size.impl : val :=
  λ: "v",
     ExternalOp DiskOp.SizeOp "v"

end disk

end github_com.goose_lang.primitive.disk

end Perennial
