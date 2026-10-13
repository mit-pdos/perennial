package evalorder_mapindex

// Go evaluates the map operand (ms(1)) before the key (g(2)); the map
// primitives take the key as a curried argument, evaluated first.

func g(k uint64) uint64                   { return k }
func ms(k uint64) map[uint64]uint64 { return map[uint64]uint64{} }

func f() uint64 {
	return ms(1)[g(2)] // ERROR evaluation order
}
