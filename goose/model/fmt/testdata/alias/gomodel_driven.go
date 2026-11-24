// internal/gomodel with its choices driven by a test (TestModelAlias, alias_test.go): the overlay's
// gomodel.go (goose/model/overlay/internal/gomodel), but Choose and ChooseUint64 return, in order,
// the values a test gives with Drive (Choose: whether the value is not 0), then 0 once those run
// out. etc/model-tests.sh puts it in place of gomodel.go for the fmt alias test only.
package gomodel

var script []uint64

// Drive makes the next calls of Choose and ChooseUint64 return the values of s, in order.
func Drive(s []uint64) { script = append([]uint64(nil), s...) }

func next() uint64 {
	if len(script) == 0 {
		return 0
	}
	v := script[0]
	script = script[1:]
	return v
}

// Choose is an arbitrary boolean (GooseLang: any). Here, the next driven value is not 0.
func Choose() bool { return next() != 0 }

// ChooseUint64 is an arbitrary uint64 (GooseLang: any). Here, the next driven value.
func ChooseUint64() uint64 { return next() }

// Stuck has no behaviour (GooseLang: stuck). Here, it blocks forever.
func Stuck() { select {} }

// StartRead (GooseLang: makes *p read-only). Here, it does nothing.
func StartRead[T any](p *T) {}
