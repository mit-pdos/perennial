package channel

// This file has the channel select model. This is not used by Goose directly
// but only by the tests (so the tests trust that this model matches the
// GooseLang model that is actually used for verification).

import "github.com/goose-lang/primitive"

type SelectDir uint64

const (
	SelectSend SelectDir = 0 // case ch <- Send
	SelectRecv SelectDir = 1 // case <-ch:
)

// Non-blocking select with 1 case (send or receive)
// For receive: value parameter is ignored
// Returns (selected, received_value, ok)
func NonBlockingSelect1[T any](ch *Channel[T], dir SelectDir, value T) (bool, T, bool) {
	var zero T

	if dir == SelectSend {
		selected := ch.TrySend(value, false)
		return selected, zero, false
	} else { // SelectRecv
		selected, recv_val, ok := ch.TryReceive(false)
		return selected, recv_val, ok
	}
}

// Blocking select with 2 cases
// Returns (caseIndex, received_value1, received_value2, ok)
func BlockingSelect2[T1, T2 any](
	ch1 *Channel[T1], dir1 SelectDir, val1 T1,
	ch2 *Channel[T2], dir2 SelectDir, val2 T2) (uint64, T1, T2, bool) {

	var zero1 T1
	var zero2 T2

	for {
		// Flip coin each iteration
		if primitive.RandomUint64()%2 == 0 {
			// Try case 1
			if dir1 == SelectSend {
				if ch1.TrySend(val1, true) {
					return 0, zero1, zero2, false
				}
			} else {
				selected, recv_val, ok := ch1.TryReceive(true)
				if selected {
					return 0, recv_val, zero2, ok
				}
			}
		} else {
			// Try case 2
			if dir2 == SelectSend {
				if ch2.TrySend(val2, true) {
					return 1, zero1, zero2, false
				}
			} else {
				selected, recv_val, ok := ch2.TryReceive(true)
				if selected {
					return 1, zero1, recv_val, ok
				}
			}
		}
	}
}

// Non-blocking select with 2 cases
// Returns (caseIndex, received_value1, received_value2, ok)
// caseIndex = 2 means no selection
func NonBlockingSelect2[T1, T2 any](
	ch1 *Channel[T1], dir1 SelectDir, val1 T1,
	ch2 *Channel[T2], dir2 SelectDir, val2 T2) (uint64, T1, T2, bool) {

	var zero1 T1
	var zero2 T2

	// Randomize which case to try first
	if primitive.RandomUint64()%2 == 0 {
		// Try case 1 first
		if dir1 == SelectSend {
			if ch1.TrySend(val1, false) {
				return 0, zero1, zero2, false
			}
		} else {
			selected, recv_val, ok := ch1.TryReceive(false)
			if selected {
				return 0, recv_val, zero2, ok
			}
		}

		// Try case 2
		if dir2 == SelectSend {
			if ch2.TrySend(val2, false) {
				return 1, zero1, zero2, false
			}
		} else {
			selected, recv_val, ok := ch2.TryReceive(false)
			if selected {
				return 1, zero1, recv_val, ok
			}
		}
	} else {
		// Try case 2 first
		if dir2 == SelectSend {
			if ch2.TrySend(val2, false) {
				return 1, zero1, zero2, false
			}
		} else {
			selected, recv_val, ok := ch2.TryReceive(false)
			if selected {
				return 1, zero1, recv_val, ok
			}
		}

		// Try case 1
		if dir1 == SelectSend {
			if ch1.TrySend(val1, false) {
				return 0, zero1, zero2, false
			}
		} else {
			selected, recv_val, ok := ch1.TryReceive(false)
			if selected {
				return 0, recv_val, zero2, ok
			}
		}
	}

	// Nothing selected
	return 2, zero1, zero2, false
}

func BlockingSelect3[T1, T2, T3 any](
	ch1 *Channel[T1], dir1 SelectDir, val1 T1,
	ch2 *Channel[T2], dir2 SelectDir, val2 T2,
	ch3 *Channel[T3], dir3 SelectDir, val3 T3) (uint64, T1, T2, T3, bool) {
	var zero1 T1
	var zero2 T2
	var zero3 T3
	for {
		// Randomly pick one of 3 cases
		r := primitive.RandomUint64() % 3
		switch r {
		case 0:
			// Try case 1
			if dir1 == SelectSend {
				if ch1.TrySend(val1, true) {
					return 0, zero1, zero2, zero3, false
				}
			} else {
				selected, recv_val, ok := ch1.TryReceive(true)
				if selected {
					return 0, recv_val, zero2, zero3, ok
				}
			}
		case 1:
			// Try case 2
			if dir2 == SelectSend {
				if ch2.TrySend(val2, true) {
					return 1, zero1, zero2, zero3, false
				}
			} else {
				selected, recv_val, ok := ch2.TryReceive(true)
				if selected {
					return 1, zero1, recv_val, zero3, ok
				}
			}
		default:
			// Try case 3
			if dir3 == SelectSend {
				if ch3.TrySend(val3, true) {
					return 2, zero1, zero2, zero3, false
				}
			} else {
				selected, recv_val, ok := ch3.TryReceive(true)
				if selected {
					return 2, zero1, zero2, recv_val, ok
				}
			}
		}
	}
}

// Non-blocking select with 3 cases
// Returns (caseIndex, received_value1, received_value2, received_value3, ok)
// caseIndex = 3 means no selection
func NonBlockingSelect3[T1, T2, T3 any](
	ch1 *Channel[T1], dir1 SelectDir, val1 T1,
	ch2 *Channel[T2], dir2 SelectDir, val2 T2,
	ch3 *Channel[T3], dir3 SelectDir, val3 T3) (uint64, T1, T2, T3, bool) {
	var zero1 T1
	var zero2 T2
	var zero3 T3

	// Start with a random case
	start := primitive.RandomUint64() % 3

	// Try all 3 cases starting from the random one
	for i := uint64(0); i < 3; i++ {
		caseIdx := (start + i) % 3

		if caseIdx == 0 {
			if dir1 == SelectSend {
				if ch1.TrySend(val1, false) {
					return 0, zero1, zero2, zero3, false
				}
			} else {
				selected, recv_val, ok := ch1.TryReceive(false)
				if selected {
					return 0, recv_val, zero2, zero3, ok
				}
			}
		} else if caseIdx == 1 {
			if dir2 == SelectSend {
				if ch2.TrySend(val2, false) {
					return 1, zero1, zero2, zero3, false
				}
			} else {
				selected, recv_val, ok := ch2.TryReceive(false)
				if selected {
					return 1, zero1, recv_val, zero3, ok
				}
			}
		} else { // caseIdx == 2
			if dir3 == SelectSend {
				if ch3.TrySend(val3, false) {
					return 2, zero1, zero2, zero3, false
				}
			} else {
				selected, recv_val, ok := ch3.TryReceive(false)
				if selected {
					return 2, zero1, zero2, recv_val, ok
				}
			}
		}
	}

	// Nothing selected
	return 3, zero1, zero2, zero3, false
}
