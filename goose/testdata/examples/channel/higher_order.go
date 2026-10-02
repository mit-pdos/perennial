package channel_examples

type request struct {
	f      func() string
	result chan string
}

func mkRequest(f func() string) request {
	return request{f: f, result: make(chan string, 1)}
}

func ho_worker(c chan request) {
	for r := range c {
		r.result <- r.f()
	}
}

func HigherOrderExample() []string {
	c := make(chan request)
	go ho_worker(c)
	go ho_worker(c)

	r1 := mkRequest(func() string { return "hello" + " world" })
	r2 := mkRequest(func() string { return "HELLO" })
	r3 := mkRequest(func() string { return "w" + "o" + "rld" })

	c <- r1
	c <- r2
	c <- r3

	responses := []string{
		<-r1.result,
		<-r2.result,
		<-r3.result,
	}
	return responses
}
