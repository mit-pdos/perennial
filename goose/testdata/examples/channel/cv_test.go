package channel_examples

import (
	"testing"
	"time"

	"github.com/mit-pdos/perennial/goose/testdata/examples/channel/lock"
)

func TestWait_BlocksUntilSignal(t *testing.T) {
	l := lock.NewLock()
	cv := NewCond(l)

	got := make(chan bool, 1)

	go func() {
		l.Lock()
		cv.Wait()
		l.Unlock()
		got <- true
	}()

	// Give waiter time to park.
	time.Sleep(30 * time.Millisecond)

	// Should still be blocked.
	select {
	case <-got:
		t.Fatalf("Wait() returned before Signal(); expected it to block")
	default:
	}

	l.Lock()
	cv.Signal()
	l.Unlock()

	select {
	case <-got:
		// ok
	case <-time.After(400 * time.Millisecond):
		t.Fatalf("Wait() did not return after Signal()")
	}
}

func TestSignal_NoWaiters_NoPanic(t *testing.T) {
	l := lock.NewLock()
	cv := NewCond(l)

	l.Lock()
	cv.Signal()
	l.Unlock()
}

func TestBroadcast_NoWaiters_NoPanic(t *testing.T) {
	l := lock.NewLock()
	cv := NewCond(l)

	l.Lock()
	cv.Broadcast()
	l.Unlock()
}

func TestWaitFor_TimesOut(t *testing.T) {
	l := lock.NewLock()
	cv := NewCond(l)

	l.Lock()
	start := time.Now()
	ok := cv.WaitFor(40 * time.Millisecond)
	elapsed := time.Since(start)
	l.Unlock()

	if ok {
		t.Fatalf("WaitFor() = true with no signal; want false (timed out)")
	}
	// Fuzzy bounds for CI jitter.
	if elapsed < 15*time.Millisecond {
		t.Fatalf("WaitFor() returned too fast (%v); expected near timeout", elapsed)
	}
	if elapsed > 400*time.Millisecond {
		t.Fatalf("WaitFor() took too long (%v); expected to time out sooner", elapsed)
	}
}

func TestWaitFor_SignalWins(t *testing.T) {
	l := lock.NewLock()
	cv := NewCond(l)

	done := make(chan struct{}, 1)

	go func() {
		l.Lock()
		ok := cv.WaitFor(500 * time.Millisecond)
		l.Unlock()
		if ok {
			done <- struct{}{}
		}
	}()

	time.Sleep(30 * time.Millisecond)

	l.Lock()
	cv.Signal()
	l.Unlock()

	select {
	case <-done:
		// ok
	case <-time.After(400 * time.Millisecond):
		t.Fatalf("WaitFor() did not return true after Signal()")
	}
}

func TestWaitUntil_DeadlineInPast_ReturnsFalseImmediately(t *testing.T) {
	l := lock.NewLock()
	cv := NewCond(l)

	l.Lock()
	start := time.Now()
	ok := cv.WaitUntil(time.Now().Add(-1 * time.Millisecond))
	elapsed := time.Since(start)
	l.Unlock()

	if ok {
		t.Fatalf("WaitUntil(past) = true; want false")
	}
	if elapsed > 50*time.Millisecond {
		t.Fatalf("WaitUntil(past) took too long (%v); expected immediate return", elapsed)
	}
}

func TestWaitUntil_TimesOutAroundDeadline(t *testing.T) {
	l := lock.NewLock()
	cv := NewCond(l)

	l.Lock()
	deadline := time.Now().Add(50 * time.Millisecond)
	start := time.Now()
	ok := cv.WaitUntil(deadline)
	elapsed := time.Since(start)
	l.Unlock()

	if ok {
		t.Fatalf("WaitUntil() = true with no signal; want false")
	}
	if elapsed < 20*time.Millisecond {
		t.Fatalf("WaitUntil() returned too fast (%v); expected near deadline", elapsed)
	}
	if elapsed > 500*time.Millisecond {
		t.Fatalf("WaitUntil() took too long (%v); expected to time out sooner", elapsed)
	}
}

func TestWaitFor_TimeoutRemovesStaleWaiter_SignalWakesNext(t *testing.T) {
	l := lock.NewLock()
	cv := NewCond(l)

	// 1) First waiter times out and must remove itself from the queue.
	timedOut := make(chan struct{}, 1)
	go func() {
		l.Lock()
		ok := cv.WaitFor(30 * time.Millisecond)
		l.Unlock()
		if !ok {
			timedOut <- struct{}{}
		}
	}()

	select {
	case <-timedOut:
		// ok
	case <-time.After(400 * time.Millisecond):
		t.Fatalf("first waiter did not time out")
	}

	// 2) Second waiter should be the one signaled (i.e., signal should not be wasted on stale entry).
	signaled := make(chan struct{}, 1)
	go func() {
		l.Lock()
		ok := cv.WaitFor(2 * time.Second)
		l.Unlock()
		if ok {
			signaled <- struct{}{}
		}
	}()

	time.Sleep(30 * time.Millisecond)

	l.Lock()
	cv.Signal()
	l.Unlock()

	select {
	case <-signaled:
		// ok
	case <-time.After(400 * time.Millisecond):
		t.Fatalf("Signal() did not wake the active waiter; stale waiter likely not removed")
	}
}

func TestBroadcast_WakesAll(t *testing.T) {
	l := lock.NewLock()
	cv := NewCond(l)

	const n = 5
	woke := make(chan struct{}, n)

	for i := 0; i < n; i++ {
		go func() {
			l.Lock()
			ok := cv.WaitFor(2 * time.Second)
			l.Unlock()
			if ok {
				woke <- struct{}{}
			}
		}()
	}

	time.Sleep(50 * time.Millisecond)

	l.Lock()
	cv.Broadcast()
	l.Unlock()

	deadline := time.After(500 * time.Millisecond)
	count := 0
	for count < n {
		select {
		case <-woke:
			count++
		case <-deadline:
			t.Fatalf("Broadcast woke %d/%d waiters", count, n)
		}
	}
}
