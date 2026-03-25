package channel_examples

func Web(query string) string {
	return query + ".html"
}

func Image(query string) string {
	return query + ".png"
}

func Video(query string) string {
	return query + ".mp4"
}

// https://go.dev/talks/2012/concurrency.slide#46
func Google(query string) []string {
	c := make(chan string, 3)

	go func() { c <- Web(query) }()
	go func() { c <- Image(query) }()
	go func() { c <- Video(query) }()

	results := make([]string, 0, 3)
	for i := 0; i < 3; i++ {
		r := <-c
		results = append(results, r)
	}
	return results
}
