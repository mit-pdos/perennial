package etcd_session

import (
	"errors"
	"sync"
	"time"

	"github.com/goose-lang/primitive"
)

var sessionc chan struct{} = make(chan struct{})
var mu sync.Mutex

// Mock something that might take a while, and can fail
func newSession() error {
	if primitive.RandomUint64()%2 == 0 {
		return errors.New("session failed")
	}
	return nil
}

// Mock something that might take a while.
func waitForSessionExpiration() {
}

func monitorSession() {
	for {
		waitForSessionExpiration()

		mu.Lock()
		select {
		case <-sessionc:
			sessionc = make(chan struct{})
		default:
		}
		mu.Unlock()

		err := newSession()
		if err != nil {
			continue
		}

		mu.Lock()
		close(sessionc)
		mu.Unlock()
	}
}

func waitSession[A any](cancel <-chan A) error {
	mu.Lock()
	s := sessionc
	mu.Unlock()
	select {
	case <-s:
		return nil
	case <-cancel:
		return errors.New("cancelled")
	}
}

func sessionMain() {
	go monitorSession()
	waitSession(time.After(time.Second))
}
