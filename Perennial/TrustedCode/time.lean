/-
Port of `new/trusted_code/time.v` (namespace `time`, as the generated
package).
-/
import Perennial.Golang.Defn

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace time
section code
variable [FfiSyntax] [GoGlobalContext]

def newTimer.impl : val :=
  λ: "when" "period" "f" "arg" "cp", #()

def runtimeNano.impl : val :=
  λ: <>, ArbitraryInt

-- TODO: could avoid making this trusted by verifying the real implementation,
-- which requires verifying `internal/godebug`.
def syncTimer.impl : val :=
  λ: "c",
     if: ArbitraryInt =⟨go.int64⟩ #(W64 0) then "c"
     else #chan.nil

def arbitraryTime : val :=
  λ: <>,
     -- generate a simple non-monotonic time without any nanoseconds and
     -- location of UTC
     let: "wall_seconds" := ArbitraryInt in
     CompositeLiteral (go.Named go!"time.Time" []) (LiteralValue [
        KeyedElement (some (KeyField go!"wall")) (ElementExpression go.uint64 #(W64 0)),
        KeyedElement (some (KeyField go!"ext")) (ElementExpression go.int64 "wall_seconds"),
        KeyedElement (some (KeyField go!"loc")) (ElementExpression «unsafe».Pointer #null)
     ])

def After.impl : val :=
  λ: "d",
    let: "ch" := FuncResolve go.make2 [go.ChannelType go.sendrecv (go.Named go!"time.Time" [])]
      #() #(W64 0) in
    -- delay is modeled as a no-op
    Fork (chan.send (go.Named go!"time.Time" []) "ch" (arbitraryTime #())) ;;
    "ch"

def Sleep.impl : val :=
  λ: "d", #()

end code
end time

end Perennial
