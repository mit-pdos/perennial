/-
Trusted Go model of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs/netext`
(namespace of the generated package), in terms of the network extension of
`Perennial.GooseLang.Ext.Net.Impl` (`netExt` and its operations `NetOp.*`),
for any program whose extensions include it.

The Go functions modelled here are the primitives `send(to, data string)` and
`recv() (string, string)`; `Send` and `Recv`, which convert between `[]byte`
and strings around them, are translated. A Go string is a value (`#s`), as the
extension's operations take and return, and a Go function returning two
results returns their pair.

**The Go primitives have no implementation** (they block forever): the
network is a toy, the example extension of the distributed adequacy theorem,
and this model is its specification (see `Perennial/GooseLang/Ext/Net/Impl.lean`),
not the model of existing Go code. A real implementation would be
irreducible (sockets: system calls), as `fsext`'s `os` calls are. A program
verified against the model is verified for any network that delivers only
messages that were sent, with their senders' addresses. Against the stubs
themselves the model is only less defined than Go in the harmless sense: a
Go run blocks a goroutine at its first `send` or `recv`, which is a run of
the model in which that goroutine is never scheduled again.
-/
module

public import Perennial.Golang.Defn
public import Perennial.GooseLang.Ext.Net.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext
section net
variable [GooseExts] [GoGlobalContext]

/-- Type: func(string, string) -/
def send.impl : val :=
  λ: "to" "data", ExternalOp (extOp netExt NetOp.SendOp) ("to", "data")

/-- Type: func() (string, string) -/
def recv.impl : val :=
  λ: <>, ExternalOp (extOp netExt NetOp.RecvOp) #()

end net
end github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext

end Perennial
