// Package overlaytests holds tests of the Go models (goose/model/overlay) that
// Go's own tests do not make: behaviours where a model could be more defined
// than Go. They pass against the real standard library (go test ./...) and
// under the overlay (etc/model-tests.sh).
package overlaytests

import (
	"sync"
	"testing"
	"time"
)

// waiter starts a goroutine that locks mu, waits on c and then closes done,
// and returns once the goroutine has taken its ticket (Wait has unlocked mu).
func waiter(mu *sync.Mutex, c *sync.Cond, done chan<- struct{}) {
	started := make(chan struct{})
	go func() {
		mu.Lock()
		close(started)
		c.Wait()
		mu.Unlock()
		close(done)
	}()
	<-started
	// Wait takes its ticket before unlocking mu: once we hold mu, it has.
	mu.Lock()
	mu.Unlock()
}

// returnsWithin reports whether done is closed within d.
func returnsWithin(done <-chan struct{}, d time.Duration) bool {
	select {
	case <-done:
		return true
	case <-time.After(d):
		return false
	}
}

// Cond.Wait has no spurious wakeups: without Signal or Broadcast it does not
// return (in Go it parks; the model of runtime_notifyListWait spins).
func TestCondWaitBlocksWithoutSignal(t *testing.T) {
	var mu sync.Mutex
	c := sync.NewCond(&mu)
	done := make(chan struct{})
	waiter(&mu, c, done)
	if returnsWithin(done, 300*time.Millisecond) {
		t.Fatal("Cond.Wait returned without Signal or Broadcast")
	}
	c.Signal()
	if !returnsWithin(done, 10*time.Second) {
		t.Fatal("Cond.Wait did not return after Signal")
	}
}

// Signal wakes one waiter, not two; Broadcast wakes the rest.
func TestCondSignalWakesOne(t *testing.T) {
	var mu sync.Mutex
	c := sync.NewCond(&mu)
	d1, d2 := make(chan struct{}), make(chan struct{})
	waiter(&mu, c, d1)
	waiter(&mu, c, d2)
	c.Signal()
	if !returnsWithin(d1, 10*time.Second) {
		t.Fatal("the first waiter did not return after Signal")
	}
	if returnsWithin(d2, 300*time.Millisecond) {
		t.Fatal("Signal woke two waiters")
	}
	c.Broadcast()
	if !returnsWithin(d2, 10*time.Second) {
		t.Fatal("the second waiter did not return after Broadcast")
	}
}

// A Signal with no waiter is not remembered: a later Wait still blocks.
func TestCondSignalWithoutWaiterIsLost(t *testing.T) {
	var mu sync.Mutex
	c := sync.NewCond(&mu)
	c.Signal()
	c.Broadcast()
	done := make(chan struct{})
	waiter(&mu, c, done)
	if returnsWithin(done, 300*time.Millisecond) {
		t.Fatal("Cond.Wait returned after a Signal that preceded it")
	}
	c.Broadcast()
	if !returnsWithin(done, 10*time.Second) {
		t.Fatal("Cond.Wait did not return after Broadcast")
	}
}
