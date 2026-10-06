/-
Port of `new/trusted_code/github_com/goose_lang/primitive.v`.

The definitions live in the namespace of the generated package
(`github_com.goose_lang.primitive`), where the generated code refers to them.
Rocq's trusted `primitive.Mutex` (the named type) is not defined here: the
generated code defines `github_com.goose_lang.primitive.Mutex`.
-/
import Perennial.Golang.Defn.Pre
import Perennial.Golang.Defn.Lock

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.goose_lang.primitive
section code
variable [FfiSyntax] [GoGlobalContext]

/-- `Assume c` goes into an endless loop if `c` does not hold. So proofs can
assume that it holds. -/
def «Assumeⁱᵐᵖˡ» : val :=
  λ: "cond", if: Var "cond" then #()
             else (rec: "loop" <> := Var "loop" #()) #()

/-- `Assert c` raises UB (program gets stuck via `Panic`) if `c` does not
hold. So proofs have to show it always holds. -/
def «Assertⁱᵐᵖˡ» : val :=
  λ: "cond", if: Var "cond" then #()
             else Panic "assert failed"

/-- `Exit n` is supposed to exit the process. We cannot directly model this in
GooseLang, so we just loop. -/
def «Exitⁱᵐᵖˡ» : val :=
  λ: <>, (rec: "loop" <> := Var "loop" #()) #()

def Millisecond : val := #(W64 1000000)
def Second : val := #(W64 1000000000)

def «Sleepⁱᵐᵖˡ» : val := λ: "duration", #()

def «TimeNowⁱᵐᵖˡ» : val := λ: <>, ArbitraryInt

def «AfterFuncⁱᵐᵖˡ» : val := λ: "duration" "f", Fork "f" ;; Alloc "f"

def «RandomUint64ⁱᵐᵖˡ» : val := λ: <>, ArbitraryInt

def «NewProphⁱᵐᵖˡ» : val := λ: <>, NewProph

def «ResolveProphⁱᵐᵖˡ» : val := λ: "p" "val", ResolveProph (Var "p") (Var "val")

def «Linearizeⁱᵐᵖˡ» : val := λ: <>, #()

@[reducible] def «Mutexⁱᵐᵖˡ» : go.GoType := go.bool

def «Mutex__Lockⁱᵐᵖˡ» : val :=
  λ: "m" <>, lock.lock "m"

def «Mutex__Unlockⁱᵐᵖˡ» : val :=
  λ: "m" <>, lock.unlock "m"

@[reducible] def «ProphIdⁱᵐᵖˡ» : go.GoType := go.prophId

end code

namespace Mutex
abbrev t := Bool
end Mutex

namespace ProphId
abbrev t := Perennial.proph_id
end ProphId

end github_com.goose_lang.primitive

end Perennial
