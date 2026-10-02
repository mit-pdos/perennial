/-
Port of `new/golang/defn.v`: the complete Go semantics.
-/
import Perennial.Golang.Defn.Pre
import Perennial.Golang.Defn.Chan
import Perennial.Golang.Defn.String

namespace Perennial

namespace go

/-- `go.Semantics` is the top-level typeclass covering all of Go language
semantics guarantees. -/
class Semantics [ffi_syntax] [GoLocalContext] [GoGlobalContext] where
  [sem_fn : GoSemanticsFunctions]
  [core_sem : go.PreSemantics]
  [chan_sem : go.ChanSemantics]
  [string_sem : go.StringSemantics]

attribute [instance] Semantics.sem_fn Semantics.core_sem Semantics.chan_sem Semantics.string_sem
export Semantics (sem_fn chan_sem string_sem)

end go

end Perennial
