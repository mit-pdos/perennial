// Package go_channel provides the same interface as model/channel, but using the built-in channels as the implementation.
//
// This is only used for testing the model - it makes it easy to use the same example with the model and Go channels.
package go_channel

type Channel[T any] chan T

func NewChannel[T any](cap int) Channel[T] {
	return make(chan T, cap)
}

// Non-Blocking send operation for select statements. Blocking send and blocking select
// statements simply call this in a for loop until it returns true.
func (c Channel[T]) TrySend(val T, blocking bool) bool {
	if blocking {
		c <- val
		return true
	}
	select {
	case c <- val:
		return true
	default:
		return false
	}
}

// c.Send(val)
//
// is equivalent to:
//
// c <- val
func (c Channel[T]) Send(v T) {
	c <- v
}

// Non-blocking receive function used for select statements.
// The blocking parameter here is used to determine whether or not we will make an offer to a
// waiting sender. If true, we will make an offer since blocking receive is modeled as a for loop
// around nonblocking TryReceive. If false, we don't make an offer since we don't need to match
// with another non-blocking send.
func (c Channel[T]) TryReceive(blocking bool) (bool, T, bool) {
	if blocking {
		v, ok := <-c
		return true, v, ok
	}
	select {
	case v, ok := <-c:
		return true, v, ok
	default:
		var zero T
		return false, zero, true
	}
}

// Equivalent to:
// value, ok := <-c
// Notably, this requires the user to consume the ok bool which is not actually required with Go
// channels. This should be able to be solved by adding an overload wrapper that discards the ok
// bool.

func (c Channel[T]) Receive() (T, bool) {
	v, ok := <-c
	return v, ok
}

// c.Close()
//
// is equivalent to:
//
// close(c)
func (c Channel[T]) Close() {
	close(c)
}

// v := c.ReceiveDiscardOk
//
// is equivalent to:
// v := c<-
func (c Channel[T]) ReceiveDiscardOk() T {
	return_val, _ := c.Receive()
	return return_val
}

// c.Len()
//
// is equivalent to:
// len(c)
//
// This might not be worth specifying since it is hard to make good use of channel length
// semantics.
func (c Channel[T]) Len() int {
	return len(c)
}

// c.Cap()
//
// is equivalent to:
// cap(c)
func (c Channel[T]) Cap() int {
	return cap(c)
}

// c.Iter() returns an iterator that models a for range loop over the channel.
func (c Channel[T]) Iter() func(yield func(T) bool) {
	return func(yield func(T) bool) {
		for v := range c {
			if !yield(v) {
				return
			}
		}
	}
}
