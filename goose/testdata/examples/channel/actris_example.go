package channel_examples

// prog3 from Actris 2.0 intro: https://arxiv.org/pdf/2010.15030
func DSPExample() int {
	c, signal := make(chan any), make(chan any)

	go func() {
		ptr := (<-c).(*int)
		*ptr = *ptr + 2
		signal <- struct{}{}
	}()

	ptr := new(40)
	c <- ptr
	<-signal
	return *ptr // dereference to get 42
}
