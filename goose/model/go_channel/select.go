package go_channel

// This file has the channel select model. This is not used by Goose directly
// but only by the tests (so the tests trust that this model matches the
// GooseLang model that is actually used for verification).

type SelectDir uint64

const (
	SelectSend SelectDir = 0 // case ch <- Send
	SelectRecv SelectDir = 1 // case <-ch:
)

// Non-blocking select with 1 case (send or receive)
// For receive: value parameter is ignored
// Returns (selected, received_value, ok)
func NonBlockingSelect1[T any](ch Channel[T], dir SelectDir, value T) (bool, T, bool) {
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
	ch1 Channel[T1], dir1 SelectDir, val1 T1,
	ch2 Channel[T2], dir2 SelectDir, val2 T2) (uint64, T1, T2, bool) {

	var zero1 T1
	var zero2 T2

	if dir1 == SelectSend && dir2 == SelectSend {
		select {
		case ch1 <- val1:
			return 0, zero1, zero2, false
		case ch2 <- val2:
			return 1, zero1, zero2, false
		}
	} else if dir1 == SelectSend && dir2 == SelectRecv {
		select {
		case ch1 <- val1:
			return 0, zero1, zero2, false
		case v2, ok := <-ch2:
			return 1, zero1, v2, ok
		}
	} else if dir1 == SelectRecv && dir2 == SelectSend {
		select {
		case v1, ok := <-ch1:
			return 0, v1, zero2, ok
		case ch2 <- val2:
			return 1, zero1, zero2, false
		}
	} else { // both recv
		select {
		case v1, ok := <-ch1:
			return 0, v1, zero2, ok
		case v2, ok := <-ch2:
			return 1, zero1, v2, ok
		}
	}
}

// Non-blocking select with 2 cases
// Returns (caseIndex, received_value1, received_value2, ok)
// caseIndex = 2 means no selection
func NonBlockingSelect2[T1, T2 any](
	ch1 Channel[T1], dir1 SelectDir, val1 T1,
	ch2 Channel[T2], dir2 SelectDir, val2 T2) (uint64, T1, T2, bool) {

	var zero1 T1
	var zero2 T2

	if dir1 == SelectSend && dir2 == SelectSend {
		select {
		case ch1 <- val1:
			return 0, zero1, zero2, false
		case ch2 <- val2:
			return 1, zero1, zero2, false
		default:
			return 2, zero1, zero2, false
		}
	} else if dir1 == SelectSend && dir2 == SelectRecv {
		select {
		case ch1 <- val1:
			return 0, zero1, zero2, false
		case v2, ok := <-ch2:
			return 1, zero1, v2, ok
		default:
			return 2, zero1, zero2, false
		}
	} else if dir1 == SelectRecv && dir2 == SelectSend {
		select {
		case v1, ok := <-ch1:
			return 0, v1, zero2, ok
		case ch2 <- val2:
			return 1, zero1, zero2, false
		default:
			return 2, zero1, zero2, false
		}
	} else { // both recv
		select {
		case v1, ok := <-ch1:
			return 0, v1, zero2, ok
		case v2, ok := <-ch2:
			return 1, zero1, v2, ok
		default:
			return 2, zero1, zero2, false
		}
	}
}

func BlockingSelect3[T1, T2, T3 any](
	ch1 Channel[T1], dir1 SelectDir, val1 T1,
	ch2 Channel[T2], dir2 SelectDir, val2 T2,
	ch3 Channel[T3], dir3 SelectDir, val3 T3) (uint64, T1, T2, T3, bool) {
	var zero1 T1
	var zero2 T2
	var zero3 T3

	// We need to handle all 8 combinations of send/recv for 3 channels
	// This is verbose but straightforward
	if dir1 == SelectSend && dir2 == SelectSend && dir3 == SelectSend {
		select {
		case ch1 <- val1:
			return 0, zero1, zero2, zero3, false
		case ch2 <- val2:
			return 1, zero1, zero2, zero3, false
		case ch3 <- val3:
			return 2, zero1, zero2, zero3, false
		}
	} else if dir1 == SelectSend && dir2 == SelectSend && dir3 == SelectRecv {
		select {
		case ch1 <- val1:
			return 0, zero1, zero2, zero3, false
		case ch2 <- val2:
			return 1, zero1, zero2, zero3, false
		case v3, ok := <-ch3:
			return 2, zero1, zero2, v3, ok
		}
	} else if dir1 == SelectSend && dir2 == SelectRecv && dir3 == SelectSend {
		select {
		case ch1 <- val1:
			return 0, zero1, zero2, zero3, false
		case v2, ok := <-ch2:
			return 1, zero1, v2, zero3, ok
		case ch3 <- val3:
			return 2, zero1, zero2, zero3, false
		}
	} else if dir1 == SelectSend && dir2 == SelectRecv && dir3 == SelectRecv {
		select {
		case ch1 <- val1:
			return 0, zero1, zero2, zero3, false
		case v2, ok := <-ch2:
			return 1, zero1, v2, zero3, ok
		case v3, ok := <-ch3:
			return 2, zero1, zero2, v3, ok
		}
	} else if dir1 == SelectRecv && dir2 == SelectSend && dir3 == SelectSend {
		select {
		case v1, ok := <-ch1:
			return 0, v1, zero2, zero3, ok
		case ch2 <- val2:
			return 1, zero1, zero2, zero3, false
		case ch3 <- val3:
			return 2, zero1, zero2, zero3, false
		}
	} else if dir1 == SelectRecv && dir2 == SelectSend && dir3 == SelectRecv {
		select {
		case v1, ok := <-ch1:
			return 0, v1, zero2, zero3, ok
		case ch2 <- val2:
			return 1, zero1, zero2, zero3, false
		case v3, ok := <-ch3:
			return 2, zero1, zero2, v3, ok
		}
	} else if dir1 == SelectRecv && dir2 == SelectRecv && dir3 == SelectSend {
		select {
		case v1, ok := <-ch1:
			return 0, v1, zero2, zero3, ok
		case v2, ok := <-ch2:
			return 1, zero1, v2, zero3, ok
		case ch3 <- val3:
			return 2, zero1, zero2, zero3, false
		}
	} else { // all recv
		select {
		case v1, ok := <-ch1:
			return 0, v1, zero2, zero3, ok
		case v2, ok := <-ch2:
			return 1, zero1, v2, zero3, ok
		case v3, ok := <-ch3:
			return 2, zero1, zero2, v3, ok
		}
	}
}

// Non-blocking select with 3 cases
// Returns (caseIndex, received_value1, received_value2, received_value3, ok)
// caseIndex = 3 means no selection
func NonBlockingSelect3[T1, T2, T3 any](
	ch1 Channel[T1], dir1 SelectDir, val1 T1,
	ch2 Channel[T2], dir2 SelectDir, val2 T2,
	ch3 Channel[T3], dir3 SelectDir, val3 T3) (uint64, T1, T2, T3, bool) {
	var zero1 T1
	var zero2 T2
	var zero3 T3

	// We need to handle all 8 combinations of send/recv for 3 channels
	if dir1 == SelectSend && dir2 == SelectSend && dir3 == SelectSend {
		select {
		case ch1 <- val1:
			return 0, zero1, zero2, zero3, false
		case ch2 <- val2:
			return 1, zero1, zero2, zero3, false
		case ch3 <- val3:
			return 2, zero1, zero2, zero3, false
		default:
			return 3, zero1, zero2, zero3, false
		}
	} else if dir1 == SelectSend && dir2 == SelectSend && dir3 == SelectRecv {
		select {
		case ch1 <- val1:
			return 0, zero1, zero2, zero3, false
		case ch2 <- val2:
			return 1, zero1, zero2, zero3, false
		case v3, ok := <-ch3:
			return 2, zero1, zero2, v3, ok
		default:
			return 3, zero1, zero2, zero3, false
		}
	} else if dir1 == SelectSend && dir2 == SelectRecv && dir3 == SelectSend {
		select {
		case ch1 <- val1:
			return 0, zero1, zero2, zero3, false
		case v2, ok := <-ch2:
			return 1, zero1, v2, zero3, ok
		case ch3 <- val3:
			return 2, zero1, zero2, zero3, false
		default:
			return 3, zero1, zero2, zero3, false
		}
	} else if dir1 == SelectSend && dir2 == SelectRecv && dir3 == SelectRecv {
		select {
		case ch1 <- val1:
			return 0, zero1, zero2, zero3, false
		case v2, ok := <-ch2:
			return 1, zero1, v2, zero3, ok
		case v3, ok := <-ch3:
			return 2, zero1, zero2, v3, ok
		default:
			return 3, zero1, zero2, zero3, false
		}
	} else if dir1 == SelectRecv && dir2 == SelectSend && dir3 == SelectSend {
		select {
		case v1, ok := <-ch1:
			return 0, v1, zero2, zero3, ok
		case ch2 <- val2:
			return 1, zero1, zero2, zero3, false
		case ch3 <- val3:
			return 2, zero1, zero2, zero3, false
		default:
			return 3, zero1, zero2, zero3, false
		}
	} else if dir1 == SelectRecv && dir2 == SelectSend && dir3 == SelectRecv {
		select {
		case v1, ok := <-ch1:
			return 0, v1, zero2, zero3, ok
		case ch2 <- val2:
			return 1, zero1, zero2, zero3, false
		case v3, ok := <-ch3:
			return 2, zero1, zero2, v3, ok
		default:
			return 3, zero1, zero2, zero3, false
		}
	} else if dir1 == SelectRecv && dir2 == SelectRecv && dir3 == SelectSend {
		select {
		case v1, ok := <-ch1:
			return 0, v1, zero2, zero3, ok
		case v2, ok := <-ch2:
			return 1, zero1, v2, zero3, ok
		case ch3 <- val3:
			return 2, zero1, zero2, zero3, false
		default:
			return 3, zero1, zero2, zero3, false
		}
	} else { // all recv
		select {
		case v1, ok := <-ch1:
			return 0, v1, zero2, zero3, ok
		case v2, ok := <-ch2:
			return 1, zero1, v2, zero3, ok
		case v3, ok := <-ch3:
			return 2, zero1, zero2, v3, ok
		default:
			return 3, zero1, zero2, zero3, false
		}
	}
}
