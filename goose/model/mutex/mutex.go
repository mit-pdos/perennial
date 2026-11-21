// Package mutex is the Go model of the state of a sync.Mutex, used by the
// trusted sync.Mutex (Perennial/TrustedCode/sync.lean): sync.Mutex's
// underlying type is Mutex's, and the trusted Lock, TryLock and Unlock
// compare-and-swap the field locked.
//
// Like Go's sync.Mutex, Mutex is a struct whose zero value is an unlocked
// mutex, so sync.Mutex{} and new(sync.Mutex) are unlocked mutexes. Go's
// sync.Mutex keeps an int32 state word and a semaphore (internal/sync.Mutex);
// the model keeps only whether the mutex is locked.
package mutex

// Mutex is the state of a sync.Mutex. Its zero value is unlocked.
type Mutex struct {
	locked bool
}
