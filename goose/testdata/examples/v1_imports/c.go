package c

import (
	av1 "github.com/mit-pdos/perennial/goose/testdata/examples/v1_imports/a/v1"
	bv1 "github.com/mit-pdos/perennial/goose/testdata/examples/v1_imports/b/v1"
)

func AddBoth(x uint64) uint64 {
	return av1.Add(x) + bv1.Add(x)
}
