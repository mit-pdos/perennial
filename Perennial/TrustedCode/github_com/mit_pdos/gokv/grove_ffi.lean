/-
Port of `new/trusted_code/github_com/mit_pdos/gokv/grove_ffi.v` (namespace
`github_com.mit_pdos.gokv.grove_ffi`, as the generated package).

NOTE: depends on the port of `src/goose_lang/ffi/grove_ffi/impl.v`
(`Perennial.GooseLang.Ffi.GroveFfi.Impl`, providing `grove_op : ffi_syntax`,
`grove_model : ffi_model` and the opcodes `GroveOp.*`), which does not exist
yet; adjust the import/names once it does.
-/
import Perennial.Golang.Defn
import Perennial.GooseLang.Ffi.GroveFfi.Impl

set_option linter.iris.style.nameCheck false

namespace Perennial

attribute [local instance] grove_op grove_model

namespace github_com.mit_pdos.gokv.grove_ffi
/-! Grove user-facing operations. -/
section grove
variable [GoGlobalContext]

-- These are pointers in Go.
def «Listenerⁱᵐᵖˡ» : go.GoType := «unsafe».Pointer
def «Connectionⁱᵐᵖˡ» : go.GoType := «unsafe».Pointer
def Address : go.GoType := go.uint64

/-- Type: func(uint64) Listener -/
def «Listenⁱᵐᵖˡ» : val :=
  λ: "e", Alloc (ExternalOp GroveOp.ListenOp "e")

/-- Type: func(uint64) (bool, Connection) -/
def «Connectⁱᵐᵖˡ» : val :=
  λ: "e",
    let: "c" := ExternalOp GroveOp.ConnectOp "e" in
    let: "err" := Fst "c" in
    let: "socket" := Alloc (Snd "c") in
    ("err", "socket")

/-- Type: func(Listener) Connection -/
def «Acceptⁱᵐᵖˡ» : val :=
  λ: "e", Alloc (ExternalOp GroveOp.AcceptOp (Load "e"))

/-- Type: func(Connection, []byte) -/
def «Sendⁱᵐᵖˡ» : val :=
  λ: "e" "m", ExternalOp GroveOp.SendOp (Load "e", (IndexRef (go.SliceType go.byte) ("m", #(W64 0)),
                                          FuncResolve go.len [go.SliceType go.byte] "m"))

/-- Type: func(Connection) (bool, []byte) -/
def «Receiveⁱᵐᵖˡ» : val :=
  λ: "e",
    let: "r" := ExternalOp GroveOp.RecvOp (Load "e") in
    let: "err" := Fst "r" in
    let: "slice" := Snd "r" in
    let: "ptr" := Fst "slice" in
    let: "len" := Snd "slice" in

    ("err", (InternalMakeSlice ("ptr", "len", "len")))

/-- FileRead pretends that the operation can never fail.
The Go implementation will accordingly abort the program if an I/O error
occurs. -/
def «FileReadⁱᵐᵖˡ» : val :=
  λ: "f",
    let: "ret" := ExternalOp GroveOp.FileReadOp "f" in
    let: "err" := Fst "ret" in
    let: "slice" := Snd "ret" in
    if: "err" then AngelicExit #() else
    let: "ptr" := Fst "slice" in
    let: "len" := Snd "slice" in
    InternalMakeSlice ("ptr", "len", "len")

/-- FileWrite pretends that the operation can never fail.
The Go implementation will accordingly abort the program if an I/O error
occurs. -/
def «FileWriteⁱᵐᵖˡ» : val :=
  λ: "f" "c",
    let: "err" := ExternalOp GroveOp.FileWriteOp ("f", (IndexRef (go.SliceType go.byte) ("c", #(W64 0)),
                                               FuncResolve go.len [go.SliceType go.byte] "c")) in
    if: "err" then AngelicExit #() else
    #()

/-- FileAppend pretends that the operation can never fail.
The Go implementation will accordingly abort the program if an I/O error
occurs. -/
def «FileAppendⁱᵐᵖˡ» : val :=
  λ: "f" "c",
    let: "err" := ExternalOp GroveOp.FileAppendOp ("f", (IndexRef (go.SliceType go.byte) ("c", #(W64 0)),
                                               FuncResolve go.len [go.SliceType go.byte] "c")) in
    if: "err" then AngelicExit #() else
    #()

/-- Type: func() uint64 -/
def «GetTSCⁱᵐᵖˡ» : val :=
  λ: <>, ExternalOp GroveOp.GetTscOp #()

/-- Type: func() (uint64, uint64) -/
def «GetTimeRangeⁱᵐᵖˡ» : val :=
  λ: <>, ExternalOp GroveOp.GetTimeRangeOp #()

end grove

namespace Connection
abbrev t := Loc
end Connection

namespace Listener
abbrev t := Loc
end Listener

end github_com.mit_pdos.gokv.grove_ffi

end Perennial
