package float_literal_iface

func f() []any {
	return []any{1.5} // ERROR contains a float, to an interface
}
