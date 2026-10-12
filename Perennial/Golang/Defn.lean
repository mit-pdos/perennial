/-
The complete Go semantics.
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.Golang.Defn.Chan
public import Perennial.Golang.Defn.String

@[expose] public section

namespace Perennial

namespace go

/-- `go.Semantics` is the top-level typeclass covering all of Go language
semantics guarantees. -/
class Semantics [FfiSyntax] [GoLocalContext] [GoGlobalContext] where
  [sem_fn : GoSemanticsFunctions]
  [core_sem : go.PreSemantics]
  [interface_sem : go.InterfaceSemantics]
  [chan_sem : go.ChanSemantics]
  [string_sem : go.StringSemantics]
  /-- `nil` converted to an interface type, in the representation of
  `InterfaceSemantics` (`GoInterface`). -/
  convert_nil_interface (elems : List go.InterfaceElem) :
    ⟦Convert go.untypedNil (go.InterfaceType elems), UntypedNil⟧ ⤳[under] #interface.nil

attribute [instance] Semantics.sem_fn Semantics.core_sem Semantics.interface_sem Semantics.chan_sem
  Semantics.string_sem Semantics.convert_nil_interface
export Semantics (sem_fn chan_sem string_sem)

end go

end Perennial
