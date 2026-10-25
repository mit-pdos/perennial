package transitive

import av1 "github.com/mit-pdos/perennial/goose/testdata/examples/v1_imports/a/v1"

// Import the bridge last: it exports b/v1, shadowing a/v1's short Rocq name.
import bridge "github.com/mit-pdos/perennial/goose/testdata/examples/v1_imports"

func Add(x uint64) uint64 {
	return av1.Add(x) + bridge.AddBoth(x)
}
