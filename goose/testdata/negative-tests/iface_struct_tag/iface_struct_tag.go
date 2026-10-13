package iface_struct_tag

// goose drops struct tags, but they are part of type identity: Go panics on
// this assertion, and with the tags dropped the two types would be one.

func f() int {
	var e any = struct {
		X int `json:"a"`
	}{1}
	return e.(struct { // ERROR its identity is lost in translation
		X int `json:"b"`
	}).X
}
