package lock

import (
	"time"
)

// Lock is a channel-based lock.
// Acquire by sending a token into the channel.
// Release by receiving that token back out.
type Lock struct {
	ch chan struct{}
}

// NewLock returns a new Lock backed by a buffered channel of size 1.
func NewLock() Lock {
	return Lock{
		ch: make(chan struct{}, 1),
	}
}

func (l Lock) Lock() {
	l.ch <- struct{}{}
}

// Unlock releases the lock by receiving from the channel.
// This will block if the lock is not currently held.
func (l Lock) Unlock() {
	<-l.ch
}

// TryLock attempts to acquire the lock without blocking.
// Returns true on success, false if already held.
func (l Lock) TryLock() bool {
	select {
	case l.ch <- struct{}{}:
		return true
	default:
		return false
	}
}

// LockWithTimeout attempts to acquire the lock, timing out after d.
// Returns true if acquired, false if timed out.
func (l Lock) LockWithTimeout(d time.Duration) bool {
	select {
	case l.ch <- struct{}{}:
		return true
	case <-time.After(d):
		return false
	}
}
