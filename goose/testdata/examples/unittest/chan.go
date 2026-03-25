package unittest

import "fmt"

func chanBasic() {
	var x chan string
	x = make(chan string, 10)
	x = make(chan string)
	go func() {
		x <- "Foo"
		x <- "Foo"
	}()
	y, ok := <-x
	y = <-x
	if ok {
		y = y + " "
	}
}

func f() int {
	return 0
}

// modified version of example from https://go.dev/ref/spec#Select_statements
func chanSelect() {
	var a []int
	var c, c1, c2, c3, c4 chan int
	var i1, i2 int
	select {
	case <-c3:
	case i1 = <-c1:
		fmt.Print("received ", i1, " from c1\n")
	case c2 <- i2:
		fmt.Print("sent ", i2, " to c2\n")
	case i3, ok := (<-c3): // same as: i3, ok := <-c3
		if ok {
			fmt.Print("received ", i3, " from c3\n")
		} else {
			fmt.Print("c3 is closed\n")
		}
	case a[f()] = <-c4:
	// same as:
	// case t := <-c4
	//	a[f()] = t
	default:
		fmt.Print("no communication\n")
	}

	for { // send random sequence of bits to c
		select {
		case c <- 0: // note: no statement, no fallthrough, no folding of cases
		case c <- 1:
		}
	}

	select {} // block forever
}

func chanDirectional() {
	var x <-chan uint64
	var y chan<- string
	<-x
	y <- ""
}

func chanRange() {
	var x chan uint64

	for y := range x {
		fmt.Print(y)
	}

	for x := range x {
		fmt.Print(x)
	}

	for range x {
	}
}
