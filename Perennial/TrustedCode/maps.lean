/-
Trusted code for the Go `maps` package, in namespace `maps` (as the generated package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace maps
section code
variable [GooseExts] [GoGlobalContext]

/-- `Clone(m)` (maps/maps.go): `nil` if `m` is `nil`, else `clone(m).(M)`, where `clone(m any) any`
is a `go:linkname` to the runtime (`runtime/map.go`'s `maps_clone`, which calls
`internal/runtime/maps`'s `clone`): a new map holding `m`'s entries, of `m`'s dynamic type, so the
assertion `.(M)` always succeeds. Goose rejects `clone` (an external function, no Go body), and a
model of `clone` alone cannot be written: it takes an `any`, while the semantics' map operations
(`map.forRange`, `map.insert`, `make`) take the map's type statically. So `Clone`, whose type
parameters give that type, is the trusted unit. The model is goose's translation of

```go
func Clone[M ~map[K]V, K comparable, V any](m M) M {
	if m == nil {
		return nil
	}
	r := make(M, len(m))
	for k, v := range m {
		r[k] = v
	}
	return r
}
```

that is, the same `nil` test, and a fresh map filled with `m`'s entries by assignment (a shallow
copy, as Go's documentation says). It does not depart from Go's observable behaviour: the result is
a new map (no other reference to it exists; a write to it is not seen in `m`), with the same
entries, and `nil` exactly when `m` is (an empty non-nil `m` gives an empty non-nil map). The
runtime's capacity hint and its copying of the table layout are unobservable. Entries whose key is
not equal to itself (a float `NaN`) are each inserted as a new entry by `r[k] = v`, as the runtime
copies them; the map specs exclude such keys (`SafeMapKey`). Go evidence:
`goose/model/maps/clone_test.go` (the model above against `maps.Clone`). -/
noncomputable def Clone.impl (M K V : go.GoType) : val :=
  (LamV "m"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc M))) (App (Val (GoInstruction (GoZeroVal M))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "m" (App (Val (GoInstruction (GoAlloc M))) (Var "m"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (App (Val (GoInstruction (FuncResolve go.make2 [M]))) (Val #())) (Let "$a0" (App (Val (GoInstruction (GoLoad M))) (Var "m"))
  (App (App (Val (GoInstruction (FuncResolve go.len [M]))) (Val #())) (Var "$a0"))))
  (Let "r" (App (Val (GoInstruction (GoAlloc M))) (App (Val (GoInstruction (GoZeroVal M))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad M))) (Var "r"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore M))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "$range" (App (Val (GoInstruction (GoLoad M))) (Var "m"))
  (Let "v" (App (Val (GoInstruction (GoAlloc V))) (App (Val (GoInstruction (GoZeroVal V))) (Val #())))
  (Let "k" (App (Val (GoInstruction (GoAlloc K))) (App (Val (GoInstruction (GoZeroVal K))) (Val #())))
  (App (App (Val (map.forRange K V)) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad V))) (Var "v"))
  (App (Val doExecute)
  (App (App (App (Val (map.insert K)) (App (Val (GoInstruction (GoLoad M))) (Var "r"))) (App (Val (GoInstruction (GoLoad K))) (Var "k"))) (Var "$r0"))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore K))) (Pair (Var "k") (Var "$key")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore V))) (Pair (Var "v") (Var "$value"))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore M))) (Pair (Var "r") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals M))) (Pair (App (Val (GoInstruction (GoLoad M))) (Var "m")) (App (Val (GoInstruction (Convert go.untypedNil M))) (Val UntypedNil)))))
  (Let "$r0" (App (Val (GoInstruction (Convert go.untypedNil M))) (Val UntypedNil))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore M))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val (GoInstruction (GoLoad M))) (Var "$res0")))))

end code
end maps

end Perennial
