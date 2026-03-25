package channel

import (
	"github.com/goose-lang/primitive"
)

type offerState uint64

const (
	buffered offerState = iota
	idle
	sndPending
	rcvPending
	sndCommit
	rcvDone
	closed
)

type Channel[T any] struct {
	cap int

	// mu protects all remaining fields
	mu    *primitive.Mutex
	state offerState
	// used only for buffered channels
	buffer []T
	// in-flight value used only for unbuffered channels
	v T
}

func NewChannel[T any](cap int) *Channel[T] {
	local_state := idle
	if cap > 0 {
		local_state = buffered
	}
	return &Channel[T]{
		cap:    cap,
		mu:     new(primitive.Mutex),
		buffer: make([]T, 0),
		state:  local_state,
	}
}

// Non-Blocking send operation for select statements. Blocking send and blocking select
// statements simply call this in a for loop until it returns true.
func (c *Channel[T]) TrySend(val T, blocking bool) bool {
	c.mu.Lock()
	switch c.state {
	case closed:
		panic("send on closed channel")
	case buffered:
		// If we have room, buffer our value
		if len(c.buffer) < int(c.cap) {
			c.buffer = append(c.buffer, val)
			c.mu.Unlock()
			return true
		}
		c.mu.Unlock()
		return false
	case rcvPending:
		// Receiver offers, accept offer.
		c.state = sndCommit
		c.v = val
		c.mu.Unlock()
		return true
	case idle:
		// Make an offer only if blocking.
		if blocking {
			c.state = sndPending
			// Save the value in case the receiver completes the exchange.
			c.v = val
			c.mu.Unlock()
			c.mu.Lock()
			switch c.state {
			// Receiver accepts, reset the channel.
			case rcvDone:
				c.state = idle
				c.mu.Unlock()
				return true
			// Offer still stands, rescind it.
			case sndPending:
				c.state = idle
				c.mu.Unlock()
				return false
			// This protocol doesn't work if other parties can cancel the exchange.
			default:
				panic("Invalid state transition with open receive offer")
			}
		}
		// Nonblocking sends can't make offers, only can accept them.
		c.mu.Unlock()
		return false
	// An exchange is in progress that we can't participate in.
	default:
		c.mu.Unlock()
		return false
	}
}

// c.Send(val)
//
// is equivalent to:
//
// c <- val
func (c *Channel[T]) Send(v T) {
	if c == nil {
		// Block forever
		for {
		}
	}
	for !c.TrySend(v, true) {
	}
}

// Non-blocking receive function used for select statements.
// The blocking parameter here is used to determine whether or not we will make an offer to a
// waiting sender. If true, we will make an offer since blocking receive is modeled as a for loop
// around nonblocking TryReceive. If false, we don't make an offer since we don't need to match
// with another non-blocking send.
func (c *Channel[T]) TryReceive(blocking bool) (bool, T, bool) {
	var local_val T
	// First critical section: determine state and get value if sender is ready
	c.mu.Lock()
	switch c.state {
	case buffered:
		var v T
		if len(c.buffer) > 0 {
			val_copy := c.buffer[0]
			c.buffer = c.buffer[1:]
			c.mu.Unlock()
			return true, val_copy, true
		}
		c.mu.Unlock()
		return false, v, true
	case closed:
		// For a buffered channel, we drain the buffer before returning ok=false.
		if len(c.buffer) > 0 {
			val_copy := c.buffer[0]
			c.buffer = c.buffer[1:]
			c.mu.Unlock()
			return true, val_copy, true
		}
		c.mu.Unlock()
		return true, local_val, false
	// Sender is making an offer, accept it
	case sndPending:
		local_val = c.v
		c.state = rcvDone
		c.mu.Unlock()
		return true, local_val, true
	case idle:
		if blocking {
			c.state = rcvPending
			c.mu.Unlock()
			c.mu.Lock()
			switch c.state {
			// Offer wasn't accepted in time, rescind it.
			case rcvPending:
				c.state = idle
				c.mu.Unlock()
				return false, local_val, true
			// Offer was accepted, reset channel.
			case sndCommit:
				c.state = idle
				local_val = c.v
				c.mu.Unlock()
				return true, local_val, true
			default:
				// The protocol does not allow interference when an offer is outgoing.
				panic("not supposed to be here!")
			}
		}
		// For nonblocking, we can't make offers, only can complete them.
		c.mu.Unlock()
		return false, local_val, true
	// An exchange is in progress that we can't participate in.
	default:
		c.mu.Unlock()
		return false, local_val, true
	}
}

// Equivalent to:
// value, ok := <-c
// Notably, this requires the user to consume the ok bool which is not actually required with Go
// channels. This should be able to be solved by adding an overload wrapper that discards the ok
// bool.

func (c *Channel[T]) Receive() (T, bool) {
	if c == nil {
		// Block forever
		for {
		}
	}
	for {
		success, v, ok := c.TryReceive(true)
		if success {
			return v, ok
		}
	}
}

// This is a non-blocking attempt at closing. The only reason close blocks ever is because there
// may be successful exchanges that need to complete, which is equivalent to the go runtime where
// the closer must still obtain the channel's lock
func (c *Channel[T]) tryClose() bool {
	c.mu.Lock()
	switch c.state {
	case closed:
		panic("close of closed channel")
	case idle, buffered:
		c.state = closed
		c.mu.Unlock()
		return true
	// For unbuffered channels, if there is an exchange in progress, let the exchange complete.
	// In the runtime channel code the lock is held while this happens.
	default:
		c.mu.Unlock()
		return false
	}
}

// c.Close()
//
// is equivalent to:
//
// close(c)
func (c *Channel[T]) Close() {
	if c == nil {
		panic("close of nil channel")
	}
	for !c.tryClose() {
	}
}

// v := c.ReceiveDiscardOk
//
// is equivalent to:
// v := c<-
func (c *Channel[T]) ReceiveDiscardOk() T {
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
func (c *Channel[T]) Len() int {
	if c == nil {
		return 0
	}
	c.mu.Lock()
	chan_len := len(c.buffer)
	c.mu.Unlock()
	return chan_len
}

// c.Cap()
//
// is equivalent to:
// cap(c)
func (c *Channel[T]) Cap() int {
	if c == nil {
		return 0
	}
	return c.cap
}

// c.Iter() returns an iterator that models a for range loop over the channel.
func (c *Channel[T]) Iter() func(yield func(T) bool) {
	return func(yield func(T) bool) {
		for {
			selected, v, ok := c.TryReceive(true)
			// no progress this iteration, try again
			if !selected {
				continue
			}
			// iteration is done
			if !ok {
				return
			}
			if !yield(v) {
				// early exit
				return
			}
		}
	}
}
