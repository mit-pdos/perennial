/-
Trusted definitions of `github.com/goose-lang/primitive`.

The definitions live in the namespace of the generated package
(`github_com.goose_lang.primitive`), where the generated code refers to them.
The named type `primitive.Mutex` is not defined here: the
generated code defines `github_com.goose_lang.primitive.Mutex`.
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.Golang.Defn.Lock

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.goose_lang.primitive
section code
variable [FfiSyntax] [GoGlobalContext]

/-- `Assume c` goes into an endless loop if `c` does not hold. So proofs can
assume that it holds. -/
def Assume.impl : val :=
  λ: "cond", if: Var "cond" then #()
             else (rec: "loop" <> := Var "loop" #()) #()

/-- `Assert c` raises UB (program gets stuck via `Panic`) if `c` does not
hold. So proofs have to show it always holds. -/
def Assert.impl : val :=
  λ: "cond", if: Var "cond" then #()
             else Panic "assert failed"

/-- `Exit n` is supposed to exit the process. We cannot directly model this in
GooseLang, so we just loop. -/
def Exit.impl : val :=
  λ: <>, (rec: "loop" <> := Var "loop" #()) #()

def Millisecond : val := #(W64 1000000)
def Second : val := #(W64 1000000000)

def Sleep.impl : val := λ: "duration", #()

def TimeNow.impl : val := λ: <>, ArbitraryInt

def AfterFunc.impl : val := λ: "duration" "f", Fork "f" ;; Alloc "f"

def RandomUint64.impl : val := λ: <>, ArbitraryInt

def NewProph.impl : val := λ: <>, NewProph

def ResolveProph.impl : val := λ: "p" "val", ResolveProph (Var "p") (Var "val")

/-- `p.ResolveBool(b)` resolves the prophecy `p` with the value `#b`. -/
def ProphId.ResolveBool.impl : val := λ: "p" "b", ResolveProph (Var "p") (Var "b")

/-- `p.ResolveU64(x)` resolves the prophecy `p` with the value `#x`. -/
def ProphId.ResolveU64.impl : val := λ: "p" "x", ResolveProph (Var "p") (Var "x")

def Linearize.impl : val := λ: <>, #()

@[reducible] def Mutex.underlying : go.GoType := go.bool

def Mutex.Lock.impl : val :=
  λ: "m" <>, lock.lock "m"

def Mutex.Unlock.impl : val :=
  λ: "m" <>, lock.unlock "m"

@[reducible] def ProphId.underlying : go.GoType := go.prophId

end code

abbrev Mutex := Bool

abbrev ProphId := Perennial.proph_id

end github_com.goose_lang.primitive

end Perennial
