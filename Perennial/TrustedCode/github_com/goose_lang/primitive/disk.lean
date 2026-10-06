/-
Port of `new/trusted_code/github_com/goose_lang/primitive/disk.v` (namespace
`github_com.goose_lang.primitive.disk`, as the generated package).

TODO (from Rocq): this isn't correct, the new translation needs certain
go_type definitions.

NOTE: depends on the port of `src/goose_lang/ffi/disk_ffi/impl.v`
(`Perennial.GooseLang.Ffi.DiskFfi.Impl`, providing `disk_op : ffi_syntax`,
`disk_model : ffi_model` and the opcodes `DiskOp.*`), which does not exist yet;
adjust the import/names once it does.
-/
import Perennial.Golang.Defn
import Perennial.GooseLang.Ffi.DiskFfi.Impl

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

def «Getⁱᵐᵖˡ» : val :=
  λ: <>, ExtV ()

def «Readⁱᵐᵖˡ» : val :=
  λ: "a",
  let: "p" := ExternalOp DiskOp.ReadOp "a" in
  FullSlice (go.ArrayType 4096 go.byte) ("p", #(W64 0), #(W64 4096), #(W64 4096))

def «ReadToⁱᵐᵖˡ» : val :=
  λ: "a" "buf",
  let: "p" := ExternalOp DiskOp.ReadOp "a" in
  FuncResolve "copy" [go.SliceType go.byte] #() "buf" ("p", #(W64 4096), #(W64 4096))

def «Writeⁱᵐᵖˡ» : val :=
  λ: "a" "b",
  ExternalOp DiskOp.WriteOp ("a", IndexRef (go.SliceType go.byte) ("b", #(W64 0)))

def «Barrierⁱᵐᵖˡ» : val :=
  λ: <>, #()

def «Sizeⁱᵐᵖˡ» : val :=
  λ: "v",
     ExternalOp DiskOp.SizeOp "v"

end disk

end github_com.goose_lang.primitive.disk

end Perennial
