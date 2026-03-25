package golang_test

/*
Tests to demonstrate Go's behavior on various subtle examples.
*/

import (
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
)

func modifyArray(a [5]uint64) {
	a[0] = 1
}

func TestGoPassingArrayCopies(t *testing.T) {
	var a [5]uint64
	modifyArray(a)
	// arrays are values that are copied
	assert.Equal(t, [5]uint64{}, a)
}

type S struct {
	a uint64
	b uint32
	c bool
}

func (s *S) SetA() {
	s.a = 1
}

func (s S) GetA() uint64 {
	// this never modifies the callee's value
	s.a = 2
	return s.a
}

func TestGoUseStructMethodsOnValue(t *testing.T) {
	var s S
	s.SetA() // pointer method on value
	assert.Equal(t, uint64(1), s.a)
	assert.Equal(t, uint64(2), s.GetA())
	assert.Equal(t, uint64(1), s.a)
}

func TestGoUseStructMethodsOnPointer(t *testing.T) {
	s := &S{}
	s.SetA()
	assert.Equal(t, uint64(1), s.a)
	assert.Equal(t, uint64(2), s.GetA()) // value method on pointer
	assert.Equal(t, uint64(1), s.a)
}

type IntPair struct {
	b uint64
	a uint64
}

func mkNext() func() uint64 {
	index := uint64(0)
	next := func() uint64 {
		index++
		return index
	}
	return next
}

func TestNextHelper(t *testing.T) {
	next := mkNext()
	assert.Equal(t, uint64(1), next())
	assert.Equal(t, uint64(2), next())
	assert.Equal(t, uint64(3), next())
}

func TestStructInitializedInProgramOrder(t *testing.T) {
	next := mkNext()
	s1 := IntPair{
		a: next(),
		b: next(),
	}
	assert.Equal(t, IntPair{a: 1, b: 2}, s1)
	next = mkNext()
	s2 := IntPair{
		b: next(),
		a: next(),
	}
	assert.Equal(t, IntPair{b: 1, a: 2}, s2)
}

// each defined type (types.Named) creates a distinct type at runtime,
// detectable via interface type casts or type switches
type type1 uint64
type type2 uint64

func TestInterfaceTypeIdentity(t *testing.T) {
	assert := assert.New(t)
	var isUint64 interface{} = uint64(3)
	var isType1 interface{} = type1(3)
	var ok bool
	_, ok = isUint64.(uint64)
	assert.Equal(true, ok, "uint64->uint64 check")
	_, ok = isUint64.(type1)
	assert.Equal(false, ok, "uint64 should not be type1")

	_, ok = isType1.(type1)
	assert.Equal(true, ok, "isType1->isType1 check")
	_, ok = isType1.(uint64)
	assert.Equal(false, ok, "type1 should not be uint64")
	_, ok = isType1.(type2)
	assert.Equal(false, ok, "type1 should not be type2")
}

// nil is a special slice value with a null pointer,
// unequal to any other derived slice value
func TestNilComparisons(t *testing.T) {
	assert := assert.New(t)
	var s []byte
	assert.True(s == nil)
	s = make([]byte, 0)
	assert.False(s == nil)
	s = make([]byte, 0, 10)
	assert.False(s[:0] == nil)
}

func TestSliceCapacity(t *testing.T) {
	assert := assert.New(t)
	assert.Equal(10, cap(make([]byte, 10)))
	assert.Equal(20, cap(make([]byte, 10, 20)))
	assert.Equal(20, cap(make([]byte, 10, 20)[:5]),
		"sub-slicing prefix maintains capacity")
	assert.Equal(19, cap(make([]byte, 10, 20)[1:6]),
		"sub-slicing middle maintains remaining capacity")
	assert.Equal(15, cap(make([]byte, 10, 20)[:10:15]),
		"can explicitly reduce capacity of subslice")
	assert.Panics(func() {
		_ = make([]byte, 10, 10)[:5:12]
	}, "cannot get capacity beyond what is present")
	assert.Equal(15, cap(make([]byte, 10, 20)[:10:15]),
		"can explicitly reduce capacity of subslice")
}

func TestModifyCapacity(t *testing.T) {
	assert := assert.New(t)
	s := make([]uint64, 5)
	s2 := s[:2]
	assert.Equal(5, cap(s2), "subslicing retains the original capacity")

	s2 = append(s2, 7)
	// s2 is in fact the same pointer as the original (not sure how to check
	// this)
	assert.Equal(3, len(s2))
	assert.Equal(5, cap(s2))

	assert.Equal(uint64(7), s[2],
		"appending modifies underlying slice via capacity")
}

const chanV uint64 = 7

func TestGoBasicChannel(t *testing.T) {
	c := make(chan uint64)
	go func() {
		c <- chanV
	}()
	x := <-c
	assert.Equal(t, chanV, x)
}

func TestGoSendBlocks(t *testing.T) {
	start := time.Now()
	c := make(chan uint64)
	go func() {
		c <- chanV
	}()
	time.Sleep(200 * time.Millisecond)
	x := <-c
	assert.Equal(t, chanV, x)
	assert.Greater(t, time.Since(start).Milliseconds(), int64(100))
}

func TestGoRecvBlocks(t *testing.T) {
	start := time.Now()
	c := make(chan uint64)
	go func() {
		time.Sleep(200 * time.Millisecond)
		c <- chanV
	}()
	x := <-c
	assert.Equal(t, chanV, x)
	assert.Greater(t, time.Since(start).Milliseconds(), int64(100))
}

func TestGoRecvOnNil(t *testing.T) {
	// receive on nil blocks forever
	//
	// https://golang.org/ref/spec#Receive_operator
	var c chan uint64
	select {
	case <-c:
		t.Fatalf("receiving on nil should block")
	default:
	}
}
func TestGoSendClosedPanics(t *testing.T) {
	c := make(chan uint64)
	close(c)
	assert.Panics(t, func() {
		c <- chanV
	})
}

func TestGoRecvClosedZero(t *testing.T) {
	c := make(chan uint64)
	close(c)
	x := <-c
	assert.Equal(t, uint64(0), x)
}

func TestGoRecvClosedCheck(t *testing.T) {
	c := make(chan uint64)
	close(c)
	x, ok := <-c
	assert.Equal(t, uint64(0), x)
	assert.False(t, ok, "receive should report channel closed")
}

type embedA struct {
	a uint8
}

func (e embedA) AMethod() {
	e.a += 1
}

type embedB struct {
	embedA
	b uint8
}

// XXX: this is not the same as the embedded method `B.AMethod`
func (e embedB) AMethod2() {
	e.embedA.AMethod()
}

func TestDataRace(t *testing.T) {
	p := new(embedB)
	go func() {
		for {
			p.b += 1
		}
	}()

	p.AMethod()
	(*p).AMethod()

	// XXX: this one causes a data race, but the one above does not
	// p.AMethod2()
}
