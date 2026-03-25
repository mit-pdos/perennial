package channel_examples

import (
	"strings"
	"testing"
	"time"
)

func TestHelloWorldSync(t *testing.T) {
	result := HelloWorldSync()
	if result != "Hello, World!" {
		panic("incorrect output")
	}
}

func TestHelloWorldWithTimeout(t *testing.T) {
	result := HelloWorldWithTimeout()
	if result != "operation timed out" && result != "Hello, World!" {
		panic("incorrect output")
	}
}

func TestDSPExample(t *testing.T) {
	result := DSPExample()
	if result != 42 {
		panic("incorrect output")
	}
}

func TestFibConsumer(t *testing.T) {
	result := fib_consumer()
	expected := []int{0, 1, 1, 2, 3, 5, 8, 13, 21, 34}

	if len(result) != len(expected) {
		panic("incorrect output")
	}

	for i := range expected {
		if result[i] != expected[i] {
			panic("incorrect output")
		}
	}
}

func TestSelectNbNotReady(t *testing.T) {
	iterations := 10000
	for i := 0; i < iterations; i++ {
		select_nb_not_ready()
		// Small sleep to let the goroutine finish
		time.Sleep(1 * time.Microsecond)
	}
}

func TestSelectTrickyExamples(t *testing.T) {
	iterations := 10000
	for i := 0; i < iterations; i++ {
		select_nb_not_ready()
		select_nb_guaranteed_ready()
		select_nb_full_buffer_not_ready()
	}
}

func TestHigherOrderExample(t *testing.T) {
	responses := HigherOrderExample()
	expected := []string{"hello world", "HELLO", "world"}
	if !strings.EqualFold(strings.Join(responses, ""), strings.Join(expected, "")) {
		t.Errorf("Expected %v, got %v", expected, responses)
	}
}
