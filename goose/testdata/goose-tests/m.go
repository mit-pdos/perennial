package m

import "github.com/tchajed/marshal"

func UseMarshal() bool {
	marshal.NewEnc(4096)
	return true
}
