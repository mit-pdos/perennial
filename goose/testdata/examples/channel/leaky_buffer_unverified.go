package channel_examples

import "strings"

// The example below is a minimal use of the
// https://go.dev/doc/effective_go#leaky_buffer pattern

// load writes the next letter into the buffer.
func load(b *[]byte, letter string) {
	*b = []byte(letter)
}

// process consumes the buffer and appends it to the output.
func process(b *[]byte, output *string) {
	*output += strings.ToUpper(string(*b))
}

func client(input []string, freeList chan []byte, serverChan chan []byte) {
	for _, letter := range input {
		var b []byte

		// Non-blocking receive from freeList.
		select {
		case b = <-freeList:
			// Reuse buffer from pool.
		default:
			// Allocate a new minimal buffer.
			b = []byte{0}
		}

		load(&b, letter) // Put one letter into the buffer.
		serverChan <- b  // Blocking send to server.
	}

	// Signal no more work.
	close(serverChan)
}

func server(output *string, freeList chan []byte, serverChan chan []byte, done chan struct{}) {
	for {
		// Blocking receive from serverChan.
		b, ok := <-serverChan
		if !ok {
			// Channel closed and drained.
			done <- struct{}{}
			return
		}

		process(&b, output)

		// Non-blocking return of buffer to freeList; drop if pool full.
		select {
		case freeList <- b:
			// Returned to pool.
		default:
			// Pool full; drop buffer.
		}
	}
}

func LeakyBufferPipeline() {
	freeList := make(chan []byte, 5) // buffer pool
	serverChan := make(chan []byte, 0)
	done := make(chan struct{}, 0)

	output := ""

	go server(&output, freeList, serverChan, done)
	client([]string{"h", "e", "l", "l", "o", ",", " ", "w", "o", "r", "l", "d"}, freeList, serverChan)
	<-done

	// At this point, server finished because client closed serverChan.
	if output != "HELLO, WORLD" {
		panic("incorrect output")
	}
}
