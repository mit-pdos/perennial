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
variable [GooseExts] [GoGlobalContext]

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
with the reflection call `reflectlite.TypeOf(target).Comparable()` replaced by `true`, and `is`
named by its Go name `errors.is`.

Departure from Go: GooseLang cannot inspect the dynamic type of an interface value, so the
model takes every `target` to be comparable. For a `target` whose dynamic type is not
comparable (a slice type, say), Go's `is` skips `err == target`; the model performs it, and
when some error of the tree has `target`'s type that comparison is stuck (`CheckComparable`
has no rule for an uncomparable type). The model is thus less defined than Go there, never
different: `wp_Is` only admits `nil` and pointer targets. A semantics rule testing the
comparability of an interface's dynamic type (refining `CheckComparable`) would let goose
translate `Is` and remove this departure. -/
noncomputable def Is.impl : val :=
  (LamV "err"
  (Lam "target"
  (App (Val exceptionDo)
  (Let "target" (App (Val (GoInstruction (GoAlloc go.error))) (Var "target"))
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (Var "err"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #true)
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

/-- The initializer of `errorType` (`errors/wrap.go`):

```go
var errorType = reflectlite.TypeOf((*error)(nil)).Elem()
```

The model does nothing, and `errorType` is not allocated. Its value is the runtime type
descriptor of `error`, which the semantics cannot represent: `reflectlite.TypeOf` is
`abi.TypeOf`, which reads the descriptor out of an interface's memory through `unsafe`.
Go's initializer reads a static descriptor and allocates nothing the program can see, so it
cannot panic and has no other effect. Its only reader is `As` (it calls
`targetType.Implements(errorType)`), which is not translated; a translated reader could not
load the variable (nothing gives a points-to for it). -/
def errorType.init : val :=
  λ: <>, #()

end code
end errors

end Perennial
