package unittest

// A struct with a field of anonymous struct type (as bbolt's DB.ops).
type withHooks struct {
	hooks struct {
		write func(x uint64) uint64
		count uint64
	}
	name string
}

func useHooks(w *withHooks, x uint64) uint64 {
	w.hooks.count += 1
	return w.hooks.write(x) + w.hooks.count
}

func setHooks(w *withHooks) {
	w.hooks.write = func(x uint64) uint64 { return x }
}
