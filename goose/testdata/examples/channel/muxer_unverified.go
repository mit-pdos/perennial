package channel_examples

func CancellableMapServer(s streamold, done chan struct{}) {
	for {
		select {
		case in, ok := <-s.req:
			if !ok {
				return
			}
			s.res <- s.f(in)
		case <-done:
			return
		}
	}
}

// 4. CancellableMuxer - muxer with cancellation
func CancellableMuxer(c chan streamold, done chan struct{}, errMsg *string) string {
	for {
		select {
		case s, ok := <-c:
			if !ok {
				return "serviced all requests"
			}
			go CancellableMapServer(s, done)
		case <-done:
			return *errMsg
		}
	}
}
