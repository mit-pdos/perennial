/-
Trusted code for the Go `errors` package (namespace `errors`, as the generated package).

`As` is a Go model (`goose/model/overlay/errors/wrap.go`, translated): Go's `As`, whose tree walk
`asWalk` is Go's `as` with its reflection moved into one function, `asAssign`. `asAssign(err,
target)` is that reflection (Go, in the model:

```go
val := reflectlite.ValueOf(target)
typ := val.Type()
if typ.Kind() != reflectlite.Ptr || val.IsNil() {
	panic("errors: target must be a non-nil pointer")
}
targetType := typ.Elem()
if targetType.Kind() != reflectlite.Interface && !targetType.Implements(errorType) {
	panic("errors: *target must be interface or implement error")
}
if reflectlite.TypeOf(err).AssignableTo(targetType) {
	val.Elem().Set(reflectlite.ValueOf(err))
	return true
}
return false
```

), which is the semantics' `AsAssign` on `(err, target)` (`go.InterfaceSemantics.as_assign_step`):
where Go panics (a target that is not a non-`nil` pointer to an interface type or a type
implementing `error`) it has no semantics, so the model is stuck there, as it is where Go assigns
a type to a non-interface type of the same underlying type that is not that type.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace errors
section code
variable [GooseExts] [GoGlobalContext]

def asAssign.impl : val :=
  λ: "err" "target", AsAssign ("err", "target")

end code
end errors

end Perennial
