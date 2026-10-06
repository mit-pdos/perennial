/-
Port of `new/golang/defn/pre.v`.
-/
import Perennial.Golang.Defn.Exception
import Perennial.Golang.Defn.Pkg
import Perennial.Golang.Defn.Loop
import Perennial.Golang.Defn.Array
import Perennial.Golang.Defn.Slice
import Perennial.Golang.Defn.Map
import Perennial.Golang.Defn.Predeclared
import Perennial.Golang.Defn.Defer
import Perennial.Golang.Defn.Interface

namespace Perennial

namespace go

/-- `go.PreSemantics` has the parts of Gooses's Go semantics that do not rely on
code written in Go itself. For instance, Goose has a channel model implemented
in Go so channel semantics are not present here. Instead, the channel model
proof actually uses the below semantics. -/
class PreSemantics [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] :
    Prop where
  [core_sem : go.CoreSemantics]
  [interface_sem : go.InterfaceSemantics]
  [array_sem : go.ArraySemantics]
  [map_sem : go.MapSemantics]
  [slice_sem : go.SliceSemantics]
  [predeclared_sem : go.PredeclaredSemantics]

attribute [instance] PreSemantics.core_sem PreSemantics.interface_sem PreSemantics.array_sem
  PreSemantics.map_sem PreSemantics.slice_sem PreSemantics.predeclared_sem
export PreSemantics (interface_sem array_sem map_sem slice_sem predeclared_sem)

end go

end Perennial
