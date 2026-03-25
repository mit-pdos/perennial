package go_channel

import (
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
)

// Tests based on interpreting the text in the Go specification (see
// https://go.dev/ref/spec#Send_statements,
// https://go.dev/ref/spec#Receive_operator, and https://go.dev/ref/spec#Close
// in particular).

func TestSpecSend(t *testing.T) {
	// A send on an unbuffered channel can proceed if a receiver is ready.
	{
		ch := NewChannel[int](0)
		go func() {
			ch.Receive()
		}()
		ch.Send(1)
		// should not block forever
	}
	// A send on a buffered channel can proceed if there is room in the buffer.
	{
		ch := NewChannel[int](1)
		ch.Send(1)
	}
}

func TestSpecSendNil(t *testing.T) {
	// A send on a nil channel blocks forever.
	var ch Channel[int]
	done := make(chan struct{})
	go func() {
		ch.Send(1)
		close(done)
	}()
	select {
	case <-done:
		panic("send should block forever")
	case <-time.After(500 * time.Millisecond):
		// good, blocked for at least 500ms
	}
}

func TestSpecReceiveNil(t *testing.T) {
	// Receiving from a nil channel blocks forever.
	var ch Channel[int]
	done := make(chan struct{})
	go func() {
		ch.Receive()
		close(done)
	}()
	select {
	case <-done:
		panic("receive should block forever")
	case <-time.After(500 * time.Millisecond):
		// good, blocked for at least 500ms
	}
}

func TestSpecClose(t *testing.T) {
	assert := assert.New(t)
	// Sending to or closing a closed channel causes a run-time panic.
	assert.Panics(func() {
		c := NewChannel[int](0)
		c.Close()
		c.Send(1)
	})
	assert.Panics(func() {
		c := NewChannel[int](0)
		c.Close()
		c.Close()
	})
	// Closing the nil channel also causes a run-time panic.
	assert.Panics(func() {
		var c Channel[bool]
		c.Close()
	})
	// After calling close, and after any previously sent values have been
	// received, receive operations will return the zero value for the channel's
	// type without blocking. The multi-valued receive operation returns a
	// received value along with an indication of whether the channel is closed.
	{
		c := NewChannel[int](2)
		c.Send(1)
		c.Close()
		v, ok := c.Receive()
		if assert.True(ok) {
			assert.Equal(1, v)
		}
		v, ok = c.Receive()
		assert.False(ok)
		assert.Equal(0, v)
	}
}
