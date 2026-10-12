/-
Trusted code for the Go `errors` package, in namespace `errors` (as the generated
package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace errors
section code
variable [FfiSyntax] [GoGlobalContext]

/-- The name of `reflectlite.TypeOf(target).Comparable()` in the model of `Is` (a helper of
the model, not a function of package `errors`): whether the dynamic type of the (non-nil)
interface `target` is comparable. It has no body (`internal/reflectlite` is not translated);
`errors.wp_reflectliteComparable` (`Proof/errors.lean`) specifies it.

Why an axiom: GooseLang has no operation that inspects the dynamic type of an interface value
(only type assertions against a static type), so neither goose's translation of
`internal/reflectlite` nor hand-written GooseLang can compute it. The lower rung would be a new
rule of the Go semantics (a comparability test on an interface's dynamic type, refining
`CheckComparable`), which would make this function translatable and remove the axiom; that is
a change to the semantics, left as a proposal. The axiom replaces the larger one it allowed to
prove (`errors.wp_Is`, formerly an axiom about all of `Is`). -/
noncomputable def reflectliteComparable : GoString := go!"errors.reflectliteComparable"

/-- `Is(err, target)`. Go's `Is` is

```go
func Is(err, target error) bool {
	if err == nil || target == nil {
		return err == target
	}
	isComparable := reflectlite.TypeOf(target).Comparable()
	return is(err, target, isComparable)
}
```

(`is`, which walks the error tree, is translated). The model is goose's translation of it
with the reflection call `reflectlite.TypeOf(target).Comparable()` replaced by a call
`reflectliteComparable(target)`, and `is` named by its Go name `errors.is`. -/
noncomputable def Is.impl : val :=
  (LamV "err"
  (Lam "target"
  (App (Val exceptionDo)
  (Let "target" (App (Val (GoInstruction (GoAlloc go.error))) (Var "target"))
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (Var "err"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.error))) (Var "target"))
  (App (App (Val (GoInstruction (FuncResolve reflectliteComparable []))) (Val #())) (Var "$a0")))
  (Let "isComparable" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Let "$a0" (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.error))) (Var "target"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad go.bool))) (Var "isComparable"))
  (App (App (App (App (Val (GoInstruction (FuncResolve go!"errors.is" []))) (Val #())) (Var "$a0")) (Var "$a1")) (Var "$a2"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "isComparable") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "target")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (GoLoad go.error))) (Var "target")))))
  (App (Val doExecute)
  (Val #())))))))))

end code
end errors

end Perennial
