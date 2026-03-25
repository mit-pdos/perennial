package channel_examples

// Example with 2 nonblocking ops that should not match.
func select_nb_not_ready() {
	ch := make(chan struct{})
	go func() {
		select {
		case <-ch:
			panic("bad")
		default:
		}
	}()

	select {
	case ch <- struct{}{}:
		panic("bad")
	default:
	}
}

func select_nb_guaranteed_ready() {
	x := make(chan int)
	close(x)
	select {
	// non-blocking receive is guaranteed to execute
	case <-x:
	default:
		// must prove unreachable
		close(x)
	}
}

// Non-blocking send cannot send on a full buffer
func select_nb_full_buffer_not_ready() {
	// 1. Buffered channel of size 1
	ch := make(chan int, 1)

	// 2. Fill the buffer
	ch <- 0

	// 3. Nonblocking select:
	//    the send case would panic,
	//    so it must NOT be taken.
	select {
	case ch <- 0:
		panic("unreachable")
	default:
		// benign: correct behavior
	}
}
