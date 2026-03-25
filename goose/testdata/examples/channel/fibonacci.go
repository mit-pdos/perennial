package channel_examples

// https://go.dev/tour/concurrency/4
func fibonacci(n int, c chan int) {
	x, y := 0, 1
	for i := 0; i < n; i++ {
		c <- x
		x, y = y, x+y
	}
	close(c)
}

func fib_consumer() []int {
	c := make(chan int, 10)
	go fibonacci(cap(c), c)

	results := []int{}
	for i := range c {
		results = append(results, i)
	}
	return results
}
