package channel_examples

import (
	"time"
)

type Result struct {
	value       string
	primary_won bool
}

// Toy functions that resemble search query servers.
func GetPrimary(query string) string {
	return query + "_primary.html"
}

func GetSecondary(query string) string {
	return query + "_secondary.html"
}

// First issues a request to the primary replica immediately. If the primary
// does not respond within hedgeThreshold, a secondary replica is also issued.
// The result of whichever replica responds first is returned, along with
// whether the primary won. If done is closed before any result, errStr is set
// to "cancelled" and a zero Result is returned.
//
// See https://go.dev/talks/2012/concurrency.slide#50 for discussion on replicated queries and
// https://www.barroso.org/publications/TheTailAtScale.pdf page 7 for discussion on hedging.
func CancellableHedgedRequest(query string, threshold time.Duration, errStr *string, done <-chan struct{}) Result {
	// Buffer 2 so the losing goroutine can always send without blocking,
	// preventing a goroutine leak after First returns.
	c := make(chan Result, 2)

	// Launch primary read.
	go func() { c <- Result{GetPrimary(query), true} }()

	// Wait for the primary to respond, the hedge threshold to fire, or cancellation.
	select {
	case r := <-c:
		// Primary responded before the hedge threshold — no replica needed.
		return r
	case <-time.After(threshold):
		// Primary is slow; launch the secondary to race against it.
		go func() { c <- Result{GetSecondary(query), false} }()
	// Stop short, caller cancelled
	case <-done:
		// Return error by reference
		*errStr = "cancelled"
		return Result{}
	}

	// Both primary and secondary are now in flight; take whichever arrives first.
	select {
	case r := <-c:
		// Send back the winner, user can log which won with r.primary_won
		return r
	case <-done:
		// Return error by reference
		*errStr = "cancelled"
		return Result{}
	}
}
