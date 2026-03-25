package unittest

import "log"

func ToBeDebugged(x uint64) uint64 {
	log.Println("starting function")
	log.Printf("called with %d", x)
	log.Println("ending function")
	return x
}

func DoNothing() {
	log.Println("doing nothing")
}
