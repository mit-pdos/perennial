package v1

// The caller and dependency deliberately have the same package name.
import bv1 "github.com/mit-pdos/perennial/goose/testdata/examples/v1_imports/b/v1"

func Add(x uint64) uint64 {
	return bv1.Add(x) - 1
}
