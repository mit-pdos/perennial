package elimination_stack

import (
	"sync"
	"time"
)

// LockedStack is a simple mutex-protected LIFO stack.
type LockedStack struct {
	mu    sync.Mutex
	stack []string
}

func NewLockedStack() *LockedStack {
	return &LockedStack{stack: make([]string, 0)}
}

func (s *LockedStack) Push(value string) {
	s.mu.Lock()
	s.stack = append(s.stack, value)
	s.mu.Unlock()
}

func (s *LockedStack) Pop() (string, bool) {
	s.mu.Lock()
	if len(s.stack) == 0 {
		s.mu.Unlock()
		return "", false
	}
	last := len(s.stack) - 1
	v := s.stack[last]
	s.stack = s.stack[:last]
	s.mu.Unlock()
	return v, true
}

const timeout = 10 * time.Microsecond

// EliminationStack composes a single-slot exchanger over a LockedStack.
type EliminationStack struct {
	base      *LockedStack
	exchanger chan string // unbuffered: rendezvous
}

// NewEliminationStack constructs a new elimination stack
// using a fresh LockedStack and a small default timeout.
func NewEliminationStack() *EliminationStack {
	return &EliminationStack{
		base:      NewLockedStack(),
		exchanger: make(chan string),
	}
}

// Push first tries one-shot elimination; on timeout, falls back to the locked stack.
func (s *EliminationStack) Push(value string) {
	select {
	case s.exchanger <- value:
		// Eliminated with a concurrent Pop.
		return
	case <-time.After(timeout):
		// Timeout; use central stack.
	}
	s.base.Push(value)
}

// Pop first tries one-shot elimination; on timeout, falls back to the locked stack.
func (s *EliminationStack) Pop() (string, bool) {
	select {
	case v := <-s.exchanger:
		// Eliminated with a concurrent Push.
		return v, true
	case <-time.After(timeout):
		// Timeout; use central stack.
	}
	return s.base.Pop()
}
