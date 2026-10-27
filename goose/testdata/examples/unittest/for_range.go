package unittest

import "fmt"

func forRangeNoBinding(x []string) {
	for range x {
		fmt.Print(x)
	}
}

func forRangeOldVars(x []string) {
	y := "ok"
	for _, y = range x {
		fmt.Print(y)
	}
}

func forRangeString(s string) (n int, sum rune) {
	for i, r := range s {
		n = i
		sum += r
	}
	return
}
