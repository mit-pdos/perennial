package proph_pointer

import "github.com/goose-lang/primitive"

// gc gives every ProphId (a struct{}) the same address; the model's are distinct.

var p *primitive.ProphId // ERROR a pointer to a ProphId
