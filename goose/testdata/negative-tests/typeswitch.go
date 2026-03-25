package unittest

// Something difficult to translate: we need a notion of type identity for
// PtrTo[T] that's distinct for every T. On top of that, int64 and int are
// distinct types for the purpose of type identity.

type PtrTo[T any] *T

func discriminate(x interface{}) string {
	switch x.(type) {
	case PtrTo[int]:
		return "int"
	case PtrTo[int64]:
		return "int64"
	case PtrTo[string]:
		return "string"
	case PtrTo[*string]:
		return "*string"
	}
	return "unknown"
}

func useDiscriminate() {
	var x int64
	discriminate(PtrTo[int64](&x))
}
