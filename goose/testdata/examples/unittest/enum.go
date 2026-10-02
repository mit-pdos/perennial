package unittest

type Enum1 uint64

const (
	Enum1A Enum1 = iota
	Enum1B
	Enum1C
)

type Enum2 int

const (
	Enum2A         Enum2 = 1    // line comment 1
	Enum2B, Enum2C       = 3, 4 // line comment 2
	Enum2D         Enum2 = 15   // line comment 3
)
