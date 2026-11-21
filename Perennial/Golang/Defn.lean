/-
The complete Go semantics.
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.Golang.Defn.Chan
public import Perennial.Golang.Defn.String
public import Perennial.Code.github_com.mit_pdos.perennial.goose.model.pool

@[expose] public section

namespace Perennial

namespace go

/-- `go.Semantics` is the top-level typeclass covering all of Go language
semantics guarantees. `pool_sem` is the Go model of the state of a `sync.Pool`
(`goose/model/pool`), which the trusted `sync.(*Pool).Get` and `Put` call
(`TrustedCode/sync.lean`). -/
class Semantics [GooseExts] [GoLocalContext] [GoGlobalContext] where
  [sem_fn : GoSemanticsFunctions]
  [core_sem : go.PreSemantics]
  [chan_sem : go.ChanSemantics]
  [string_sem : go.StringSemantics]
  [pool_sem : github_com.mit_pdos.perennial.goose.model.pool.Assumptions]

attribute [instance] Semantics.sem_fn Semantics.core_sem Semantics.chan_sem Semantics.string_sem
  Semantics.pool_sem
export Semantics (sem_fn chan_sem string_sem pool_sem)

end go

end Perennial
