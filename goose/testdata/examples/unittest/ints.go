package unittest

func useInts(x uint64, y uint32) (uint64, uint32) {
	var z uint64
	z = uint64(y)
	z = z + 1
	var y2 uint32
	y2 = y + 3
	return z, y2
}

func signedMidpoint(x int, y int) int {
	return (x + y) / 2
}

type my_u32 uint32

type also_u32 my_u32

const ConstWithAbbrevType also_u32 = 3
