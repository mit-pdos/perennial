package channel_examples

import (
	"time"

	"github.com/mit-pdos/perennial/goose/testdata/examples/channel/lock"
)

type Cond struct {
	L       lock.Lock
	waiters []chan struct{} // protected by L
}

func NewCond(L lock.Lock) *Cond {
	return &Cond{L: L}
}

// Wait blocks until signaled. Caller must hold c.L; will hold c.L on return.
func (c *Cond) Wait() {
	ch := make(chan struct{})
	c.waiters = append(c.waiters, ch)

	c.L.Unlock()
	<-ch
	c.L.Lock()
}

// Signal wakes one waiter (FIFO). Caller must hold c.L.
func (c *Cond) Signal() {
	if len(c.waiters) == 0 {
		return
	}
	ch := c.waiters[0]
	copy(c.waiters[0:], c.waiters[1:])
	c.waiters = c.waiters[:len(c.waiters)-1]
	close(ch)
}

// Broadcast wakes all waiters. Caller must hold c.L.
func (c *Cond) Broadcast() {
	for _, ch := range c.waiters {
		close(ch)
	}
	c.waiters = nil
}

func (c *Cond) WaitFor(d time.Duration) bool {
	if d <= 0 {
		return false
	}
	ch := make(chan struct{})
	c.waiters = append(c.waiters, ch)

	c.L.Unlock()

	done := make(chan struct{})
	go func() {
		time.Sleep(d)
		close(done)
	}()

	signaled := false
	select {
	case <-ch: // signaled (channel closed by Signal/Broadcast)
		signaled = true
	case <-done: // timed out
		signaled = false
	}

	c.L.Lock()

	if !signaled {
		// If timeout and signal raced, ch may already be closed. Treat as signaled.
		select {
		case <-ch:
			return true
		default:
		}
		// Otherwise remove our waiter entry so future Signal still wakes an active waiter.
		for i := range c.waiters {
			if c.waiters[i] == ch {
				copy(c.waiters[i:], c.waiters[i+1:])
				c.waiters = c.waiters[:len(c.waiters)-1]
				break
			}
		}
	}

	return signaled
}

func (c *Cond) WaitUntil(deadline time.Time) bool {
	return c.WaitFor(time.Until(deadline))
}
