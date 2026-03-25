package channel_examples

import (
	"time"
)

// Fake syscall for demonstration.
func sys_hello_world() string {
	return "Hello, World!"
}

func HelloWorldAsync() chan string {
	ch := make(chan string, 1)
	go func() {
		ch <- sys_hello_world()
	}()
	return ch
}

func HelloWorldSync() string {
	return <-HelloWorldAsync()
}

// Simulates the error/done channel components of Context
func HelloWorldCancellable(done chan struct{}, err *string) string {
	future := HelloWorldAsync()
	select {
	case resolved := <-future:
		return resolved
	case <-done:
		return *err
	}
}

// Uses cancellation as a timeout mechanism.
func HelloWorldWithTimeout() string {
	done := make(chan struct{})
	errMsg := ""

	// Timeout goroutine updates errMsg only when timeout hits
	go func() {
		time.Sleep(10 * time.Millisecond) // short timeout to trigger cancellation
		errMsg = "operation timed out"    // update error message
		close(done)                       // signal cancellation
	}()

	return HelloWorldCancellable(done, &errMsg)
}

func simple_join() string {
	ch := make(chan struct{}, 1)
	var message string

	go func() {
		message = "Hello, World!"
		ch <- struct{}{}
	}()

	<-ch // Wait for goroutine to finish
	return message
}

func simple_multi_join() string {
	ch := make(chan struct{}, 2)
	var hello, world string

	go func() {
		hello = "Hello"
		ch <- struct{}{}
	}()
	go func() {
		world = "World"
		ch <- struct{}{}
	}()
	// Wait for both goroutines
	<-ch
	<-ch
	return hello + " " + world
}

func exchangePointer() {
	x := 0
	y := 0

	ch := make(chan struct{})
	go func() {
		x = 1
		ch <- struct{}{}
		if y != 2 {
			panic("bad")
		}
	}()

	y = 2
	<-ch
	if x != 1 {
		panic("bad")
	}
}

func BroadcastExample() {
	done := make(chan struct{})
	result1 := make(chan uint64)
	result2 := make(chan uint64)

	var sharedValue uint64

	go func() {
		<-done // Wait for broadcast
		val := sharedValue
		result1 <- val * 3
	}()

	go func() {
		<-done // Wait for broadcast
		val := sharedValue
		result2 <- val * 5
	}()

	sharedValue = 2

	// Broadcast that value is ready
	close(done)

	// Read results and assert
	r1 := <-result1
	r2 := <-result2

	if r1 != 6 {
		panic("receiver 1 got wrong value")
	}
	if r2 != 10 {
		panic("receiver 2 got wrong value")
	}
}
