/-
Trusted Go model of the functions of `github.com/mit-pdos/gokv/grove_ffi` (namespace
`github_com.mit_pdos.gokv.grove_ffi`, as the generated package), in terms of the operations of
the Grove extension of `Perennial.GooseLang.Ext.Grove.Impl` (`ExternalOp groveExt.name "Listen"`,
...), for any program whose extensions include it. The package's types are translated.

The extension's operations take and return byte strings as Go string values (`#data`); the
model converts between them and `[]byte`. `FileRead`'s result has an arbitrary capacity at
least its length (`slice._new_cap`, the capacity `append` chooses), as `os.ReadFile`'s does.
`FileAppend` appends in pieces of arbitrary sizes, each one step, as a concurrent `FileRead` may
see part of a `write(2)`.
A `Listener` or `Connection` is a fresh cell holding the extension's socket value.
-/
module

public import Perennial.Golang.Defn
public import Perennial.GooseLang.Ext.Grove.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.mit_pdos.gokv.grove_ffi
section grove
variable [GooseExts] [GoGlobalContext]

/-- Type: func(Address) Listener -/
def Listen.impl : val :=
  λ: "host", Alloc (ExternalOp groveExt.name "Listen" "host")

/-- Type: func(Address) ConnectRet -/
def Connect.impl : val :=
  λ: "host",
    let: "r" := ExternalOp groveExt.name "Connect" "host" in
    if: Fst "r" then
      CompositeLiteral (go.Named go!"github.com/mit-pdos/gokv/grove_ffi.ConnectRet" [])
        (LiteralValue [KeyedElement (some (KeyField go!"Err")) (ElementExpression go.bool #true)])
    else
      CompositeLiteral (go.Named go!"github.com/mit-pdos/gokv/grove_ffi.ConnectRet" [])
        (LiteralValue [
          KeyedElement (some (KeyField go!"Err")) (ElementExpression go.bool #false),
          KeyedElement (some (KeyField go!"Connection"))
            (ElementExpression (go.Named go!"github.com/mit-pdos/gokv/grove_ffi.Connection" [])
              (Alloc (Snd "r")))])

/-- Type: func(Listener) Connection -/
def Accept.impl : val :=
  λ: "l", Alloc (ExternalOp groveExt.name "Accept" (Load "l"))

/-- Type: func(Connection, []byte) bool -/
def Send.impl : val :=
  λ: "c" "data",
    ExternalOp groveExt.name "Send" (Load "c", Convert (go.SliceType go.byte) go.string "data")

/-- Type: func(Connection) ReceiveRet -/
def Receive.impl : val :=
  λ: "c",
    let: "r" := ExternalOp groveExt.name "Receive" (Load "c") in
    if: Fst "r" then
      CompositeLiteral (go.Named go!"github.com/mit-pdos/gokv/grove_ffi.ReceiveRet" [])
        (LiteralValue [KeyedElement (some (KeyField go!"Err")) (ElementExpression go.bool #true)])
    else
      CompositeLiteral (go.Named go!"github.com/mit-pdos/gokv/grove_ffi.ReceiveRet" [])
        (LiteralValue [
          KeyedElement (some (KeyField go!"Err")) (ElementExpression go.bool #false),
          KeyedElement (some (KeyField go!"Data"))
            (ElementExpression (go.SliceType go.byte)
              (Convert go.string (go.SliceType go.byte) (Snd "r")))])

/-- Type: func(string) []byte -/
def FileRead.impl : val :=
  λ: "filename",
    let: "b" := Convert go.string (go.SliceType go.byte)
      (ExternalOp groveExt.name "FileRead" "filename") in
    let: "n" := FuncResolve go.len [go.SliceType go.byte] #() "b" in
    let: "s" := FuncResolve go.make3 [go.SliceType go.byte] #() "n" (slice._new_cap "n") in
    FuncResolve go.copy [go.SliceType go.byte] #() "s" "b" ;;
    "s"

/-- Type: func(string, []byte) -/
def FileWrite.impl : val :=
  λ: "filename" "content",
    ExternalOp groveExt.name "FileWrite"
      ("filename", Convert (go.SliceType go.byte) go.string "content")

/-- An arbitrary length (`ArbitraryInt`) in `1..n`, or `n` (a helper of `FileAppend.impl`, not
a function of `grove_ffi`). -/
def FileAppend.pieceLen : val :=
  λ: "n",
    let: "k" := ArbitraryInt in
    if: (#(W64 0) <⟨go.int⟩ "k") && ("k" ≤⟨go.int⟩ "n") then "k" else "n"

/-- Appends the string `s` to file `filename` in one or more pieces, first to last (a helper of
`FileAppend.impl`, not a function of `grove_ffi`): each piece is a prefix of what remains, of
arbitrary length (`FileAppend.pieceLen`), non-empty unless `s` is empty (one empty piece). -/
def FileAppend.appendPieces : val :=
  rec: "loop" "filename" "s" :=
    let: "n" := FuncResolve go.len [go.string] #() "s" in
    let: "k" := FileAppend.pieceLen "n" in
    ExternalOp groveExt.name "FileAppend" ("filename", Slice go.string ("s", #(W64 0), "k")) ;;
    if: "k" <⟨go.int⟩ "n" then "loop" "filename" (Slice go.string ("s", "k", "n")) else #()

/-- Type: func(string, []byte) -/
def FileAppend.impl : val :=
  λ: "filename" "data",
    FileAppend.appendPieces "filename" (Convert (go.SliceType go.byte) go.string "data")

/-- Type: func() uint64 -/
def GetTSC.impl : val :=
  λ: <>, ExternalOp groveExt.name "GetTSC" #()

/-- Type: func() (uint64, uint64) -/
def GetTimeRange.impl : val :=
  λ: <>, ExternalOp groveExt.name "GetTimeRange" #()

end grove
end github_com.mit_pdos.gokv.grove_ffi

end Perennial
