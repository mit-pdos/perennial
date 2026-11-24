// Package gomodel is the harness's internal/gomodel (goose/model/overlay/internal/gomodel): the
// same choices, and a Stuck that panics "stuck" instead of blocking, so that a differential test
// sees where the model has no behaviour.
package gomodel

// Choose is false, as in the overlay's Go body.
func Choose() bool {
	return false
}

// ChooseUint64 is 0, as in the overlay's Go body.
func ChooseUint64() uint64 {
	return 0
}

// Stuck panics "stuck".
func Stuck() {
	panic("stuck")
}

// StartRead does nothing, as in the overlay's Go body.
func StartRead[T any](p *T) {}
