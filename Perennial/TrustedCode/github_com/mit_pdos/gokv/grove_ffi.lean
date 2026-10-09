/-
Trusted Go model of `github.com/mit-pdos/gokv/grove_ffi` (namespace
`github_com.mit_pdos.gokv.grove_ffi`, as the generated package), in terms of
the Grove FFI of `Perennial.GooseLang.Ffi.GroveFfi.Impl` (`grove_op`,
`grove_model` and the opcodes `GroveOp.*`).
-/
module

public import Perennial.Golang.Defn
public import Perennial.GooseLang.Ffi.GroveFfi.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

attribute [local instance] grove_op grove_model

namespace github_com.mit_pdos.gokv.grove_ffi
/-! Grove user-facing operations. -/
section grove
variable [GoGlobalContext]

-- These are pointers in Go.
def Listener.ty : go.GoType := «unsafe».Pointer
def Connection.ty : go.GoType := «unsafe».Pointer
def Address.ty : go.GoType := go.uint64

/-- Type: func(uint64) Listener -/
def Listen.impl : val :=
  λ: "e", Alloc (ExternalOp GroveOp.ListenOp "e")

/-- Type: func(uint64) (bool, Connection) -/
def Connect.impl : val :=
  λ: "e",
    let: "c" := ExternalOp GroveOp.ConnectOp "e" in
    let: "err" := Fst "c" in
    let: "socket" := Alloc (Snd "c") in
    ("err", "socket")

/-- Type: func(Listener) Connection -/
def Accept.impl : val :=
  λ: "e", Alloc (ExternalOp GroveOp.AcceptOp (Load "e"))

/-- Type: func(Connection, []byte) -/
def Send.impl : val :=
  λ: "e" "m", ExternalOp GroveOp.SendOp (Load "e", (IndexRef (go.SliceType go.byte) ("m", #(W64 0)),
                                          FuncResolve go.len [go.SliceType go.byte] "m"))

/-- Type: func(Connection) (bool, []byte) -/
def Receive.impl : val :=
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
def FileRead.impl : val :=
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
def FileWrite.impl : val :=
  λ: "f" "c",
    let: "err" := ExternalOp GroveOp.FileWriteOp ("f", (IndexRef (go.SliceType go.byte) ("c", #(W64 0)),
                                               FuncResolve go.len [go.SliceType go.byte] "c")) in
    if: "err" then AngelicExit #() else
    #()

/-- FileAppend pretends that the operation can never fail.
The Go implementation will accordingly abort the program if an I/O error
occurs. -/
def FileAppend.impl : val :=
  λ: "f" "c",
    let: "err" := ExternalOp GroveOp.FileAppendOp ("f", (IndexRef (go.SliceType go.byte) ("c", #(W64 0)),
                                               FuncResolve go.len [go.SliceType go.byte] "c")) in
    if: "err" then AngelicExit #() else
    #()

/-- Type: func() uint64 -/
def GetTSC.impl : val :=
  λ: <>, ExternalOp GroveOp.GetTscOp #()

/-- Type: func() (uint64, uint64) -/
def GetTimeRange.impl : val :=
  λ: <>, ExternalOp GroveOp.GetTimeRangeOp #()

end grove

abbrev Connection := Loc

abbrev Listener := Loc

end github_com.mit_pdos.gokv.grove_ffi

end Perennial
