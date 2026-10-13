package proph_in_struct

import "github.com/goose-lang/primitive"

// The model keeps a ProphId in memory (8 bytes) where gc's is a struct{} (0 bytes), so a
// struct holding one would not have gc's layout.

type typing struct {
	proph primitive.ProphId // ERROR a ProphId in a struct
}
