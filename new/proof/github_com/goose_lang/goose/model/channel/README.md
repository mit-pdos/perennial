# ChanLib

This repository contains ChanLib, a library for verifying Go code that uses channels in Perennial.  

This document provides a guide for locating the main components within Perennial.

Chanlib contains the following components:

- Channel implementation model
- Channel tests
- General logically atomic channel specification
- Idiom specifications
- Verified examples


## Channel Executable Model

The channel model's executable Go code lives in `goose/model/channel` and its Gooselang model for select lives in `new/golang/defn/chan.v`.

> NOTE: The select.go folder contains a select executable model that was used in the development of ChanLib but does not support arbitrary numbers of cases and has been replaced by a model written in Gooselang 

```
goose/model/channel/
├── README.md
├── channel.go
├── channel_spec_test.go
├── channel_test.go
└── select.go
```

### `channel.go`

This is the core Go implementation of channels.

It contains the executable channel model used throughout the development.

### `select.go`

This file contains an executable select implementation used during the
development of the select model and specifications.

It is useful as a reference for the design of select behavior, but it is not
itself the select specification interface used by ChanLib, since it is based on
a fixed-length representation.

### `new/golang/defn/chan.v`

This file contains the Goose-facing channel definitions and select-level
language support built on top of the Go model.

It includes:

- Naming wrappers such as `receive`, `send` to make specifications and code easier to read in spite of using auto-generated names from the executable model
- A definition for Go's for range loop on channels: `for_range`
- the Gooselang `try_select` definition used to model a single select attempt
- the pure-step rules that connect Go `select` statements to the executable
  channel/select model
- aliases and interface definitions used by the rest of the proof development

In particular, this is where the select behavior of the Goose model is exposed
to the logic.

## Channel Tests

The main channel tests live in

`goose/model/channel/channel_test.go`

with additional test material in

`goose/model/channel/channel_spec_test.go`.

These tests include unit tests ported from the Go runtime channel tests (https://go.dev/src/runtime/chan_test.go), along
with additional tests written to empirically validate parts of the specification not described in Go documentation nor tested in the runtime tests.

## General Channel Specification

The directory

`perennial/new/proof/github_com/goose_lang/goose/model/channel/logatom`

contains the core logically atomic channel specification for send, receive, and
close, together with the ghost state and invariants that connect the logical
specification to the channel implementation.

`perennial/new/proof/github_com/goose_lang/goose/model/channel/chan.v` contains the select specifications, for range loop specifications and naming helpers that form a public API for the channel specs. 

```
logatom/
├── chan_au_base.v
├── chan_au_new.v
├── chan_au_recv.v
├── chan_au_send.v
├── chan_init.v
└── paradox.py
```


### `chan_au_base.v`

Defines the shared foundation for the logically atomic channel specification.

This file includes:

- the logical channel state machine (`chanstate`)
- the physical ownership predicate for the channel model (`chan_phys_state`)
- offer-tracking ghost state for unbuffered handshakes
- ghost names and ownership for channel state
- the main channel invariant connecting heap state to logical state
- the public persistent channel predicate (`is_chan`)
- The atomic update definitions for various channel operations

In other words, this is the central file that ties the implementation-level
representation of channels to the logical view used in the proofs.

### `chan_au_new.v`

Defines the specification for creating a channel.

### `chan_au_recv.v`

Defines the logically atomic specifications and supporting proofs for receive
operations.

### `chan_au_send.v`

Defines the logically atomic specifications and supporting proofs for send and
close operations.

### `chan_init.v`

Shared initialization/import glue for the channel logical atomic development.

### `paradox.py`

Auxiliary script related to the logically atomic channel development.

### Public proof interface and select specifications

`perennial/new/proof/github_com/goose_lang/goose/model/channel/chan.v`

This file provides the main proof-facing interface for channel operations.

It includes:

- wrapper lemmas for channel creation, send, receive, close, and capacity
- the proof interface for `for range` over channels
- the blocking select specification
- the nonblocking select specification
- the alternate nonblocking select specification
- cleaner naming and exported interfaces built on top of the lower-level
  logically atomic development

In practice, this is the file that packages the lower-level atomic updates into
the channel proof rules used by clients.

## Idiom Specifications

The directory

`perennial/new/proof/github_com/goose_lang/goose/model/channel/idiom`

contains higher-level channel idiom specifications built on top of the general
channel specification. Each idiom corresponds to a common concurrency pattern
implemented using Go channels.

```
idiom/
├── done/
├── dsp/
├── future/
├── handoff/
├── handshake/
├── join/
├── lock/
├── mpmc/
├── spsc/
├── base.v
└── idioms.v
```

Each subdirectory defines the predicates and rules for reasoning about a
specific channel-based concurrency idiom, including helpers for complex ghost state. base.v and idioms.v contain utility rocq code such as typeclass instances and package intialization. 

### done

`idiom/done/`

Specification of cancellation and completion signaling using channels.

### dsp

`idiom/dsp/`

Session-style interaction specifications using dependent separation protocols
over pairs of channels.

### future

`idiom/future/`

Specification of future/promise channels that transfer ownership of facts about the result of a computation.

### handoff

`idiom/handoff/`

Specification of basic ownership transfer between goroutines through channel
communication.

### handshake

`idiom/handshake/`

Specification of synchronous rendezvous communication over unbuffered channels.

### join

`idiom/join/`

Specification of worker join patterns where a channel is used to wait for
completion of multiple goroutines.

### lock

`idiom/lock/`

Specification of channel-based mutual exclusion primitives.

### mpmc

`idiom/mpmc/`

Specification of multi-producer, multi-consumer pipelines that track sets of
values sent and received.

### spsc

`idiom/spsc/`

Specification of single-producer, single-consumer pipelines that track ordered
streams of values.

### Shared infrastructure

`base.v` and `idioms.v` contain shared definitions and utilities used by the
idiom specifications.

## Verified Examples

The example programs live in `goose/testdata/examples/channel`

`channel.gold.v` is used for testing translation.

```
goose/testdata/examples/channel/
├── channel.gold.v
├── cv.go
├── cv_test.go
├── elimination_stack.go
├── elimination_stack_test.go
├── examples.go
├── examples_test.go
├── examples_unverified.go
├── hedged.go
├── higher_order.go
├── leaky_buffer.go
├── lock.go
├── lock_test.go
├── muxer.go
├── muxer_test.go
├── muxer_unverified.go
├── parallel_search_replace.go
└── parallel_search_replace_test.go
```

These files contain the channel-based example programs used as client code for
the model and specifications.

### `examples.go`

Contains various smaller example programs.

TODO: split this file into one file per example so the mapping from examples to
specifications is easier to navigate.

### `examples_unverified.go`

Contains example programs that are included as implementations but are not
currently verified.

### Other example files

The remaining `.go` files in this directory contain individual channel-based
examples and case studies, with corresponding `_test.go` files where present.

These examples are intended to exercise and demonstrate the channel model,
general channel specifications, and idiom specifications on client programs.