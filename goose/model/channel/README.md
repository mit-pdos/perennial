# Go Channel Model

This directory contains a Go implementation of channels used as the execution
model for ChanLib.

The implementation provides:

- a generic Go struct representing a channel
- support for both buffered and unbuffered channels
- operations for creation, send, receive, close, length, and capacity
- nonblocking `TrySend` and `TryReceive` operations used by `select` and
  channel iteration

Because the model is written in Go, Goose can translate programs that use this
implementation directly into GooseLang code. The verification development then
reasons about this translated program.

## Tests

The file `channel_test.go` contains unit tests for the channel model.

These include tests adapted from the Go runtime channel test suite as well as
additional tests written for this model.

## Notes

This model is intended as a simple executable implementation of channel
semantics suitable for verification and empirically validating Go channel semantics.
It is not intended to match the Go runtime performance characteristics.