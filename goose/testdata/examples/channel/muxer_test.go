package channel_examples

import (
	"fmt"
	"sync"
	"testing"
	"time"
)

func TestAsync(t *testing.T) {
	result := Async(func() string {
		return "hello"
	})

	select {
	case val := <-result:
		if val != "hello" {
			panic(fmt.Sprintf("Expected 'hello', got '%s'", val))
		}
	case <-time.After(100 * time.Millisecond):
		panic("Async timed out")
	}
}

func TestServer(t *testing.T) {
	s := Serve(func(input string) string {
		return "processed-" + input
	})

	s.req <- "test"

	select {
	case result := <-s.res:
		if result != "processed-test" {
			panic(fmt.Sprintf("Expected 'processed-test', got '%s'", result))
		}
	case <-time.After(100 * time.Millisecond):
		panic("MapServer timed out")
	}

	close(s.req)
}

func TestClient(t *testing.T) {
	if Client() != "Hello, World!" {
		panic("not wai! fix it please!")
	}
}

func TestMapServer(t *testing.T) {
	s := mkStream(func(input string) string {
		return "processed-" + input
	})

	go MapServer(s)

	s.req <- "test"

	select {
	case result := <-s.res:
		if result != "processed-test" {
			panic(fmt.Sprintf("Expected 'processed-test', got '%s'", result))
		}
	case <-time.After(100 * time.Millisecond):
		panic("MapServer timed out")
	}

	close(s.req)
}

func TestMuxer(t *testing.T) {
	streamChan := make(chan streamold)

	go Muxer(streamChan)

	// Create multiple streams
	s1 := mkStream(func(input string) string {
		return "s1-" + input
	})
	s2 := mkStream(func(input string) string {
		return "s2-" + input
	})

	streamChan <- s1
	streamChan <- s2

	// Test first stream
	s1.req <- "test1"
	select {
	case result := <-s1.res:
		if result != "s1-test1" {
			panic(fmt.Sprintf("Expected 's1-test1', got '%s'", result))
		}
	case <-time.After(100 * time.Millisecond):
		panic("Muxer stream 1 timed out")
	}

	// Test second stream
	s2.req <- "test2"
	select {
	case result := <-s2.res:
		if result != "s2-test2" {
			panic(fmt.Sprintf("Expected 's2-test2', got '%s'", result))
		}
	case <-time.After(100 * time.Millisecond):
		panic("Muxer stream 2 timed out")
	}

	close(s1.req)
	close(s2.req)
	close(streamChan)
}

func TestMuxerConcurrent(t *testing.T) {
	streamChan := make(chan streamold, 10)

	go Muxer(streamChan)

	const numStreams = 10
	streams := make([]streamold, numStreams)

	// Create and send multiple streams
	for i := 0; i < numStreams; i++ {
		idx := i
		streams[i] = mkStream(func(input string) string {
			return fmt.Sprintf("stream%d-%s", idx, input)
		})
		streamChan <- streams[i]
	}

	// Send requests to all streams concurrently
	var wg sync.WaitGroup
	wg.Add(numStreams)

	for i := 0; i < numStreams; i++ {
		go func(idx int) {
			defer wg.Done()
			streams[idx].req <- "data"

			select {
			case result := <-streams[idx].res:
				expected := fmt.Sprintf("stream%d-data", idx)
				if result != expected {
					panic(fmt.Sprintf("Stream %d: expected '%s', got '%s'", idx, expected, result))
				}
			case <-time.After(100 * time.Millisecond):
				panic(fmt.Sprintf("Stream %d timed out", idx))
			}

			close(streams[idx].req)
		}(i)
	}

	wg.Wait()
	close(streamChan)
}

func TestCancellation(t *testing.T) {
	mux := make(chan streamold)
	done := make(chan struct{})
	errMsg := ""

	result := make(chan string)
	go func() {
		result <- CancellableMuxer(mux, done, &errMsg)
	}()

	// Slow stream that takes 200ms
	slow := mkStream(func(s string) string {
		time.Sleep(200 * time.Millisecond)
		return "processed: " + s
	})

	mux <- slow
	slow.req <- "data"

	// Set error BEFORE closing done
	time.Sleep(50 * time.Millisecond)
	errMsg = "timeout: operation took too long"
	close(done)

	fmt.Println("Muxer result:", <-result)
}

func TestNormalShutdown(t *testing.T) {
	mux := make(chan streamold)
	done := make(chan struct{})
	errMsg := ""

	result := make(chan string)
	go func() {
		result <- CancellableMuxer(mux, done, &errMsg)
	}()

	// Submit and process a stream
	fast := mkStream(func(s string) string { return s + "!" })
	mux <- fast
	fast.req <- "done"
	fmt.Println(<-fast.res)

	// Close channel normally
	close(mux)

	fmt.Println("Muxer result:", <-result)
}
