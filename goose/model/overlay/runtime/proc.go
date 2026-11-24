// The Go model of runtime.Gosched (Perennial/Code/runtime.toml, [model]),
// spliced into proc.go in place of the real declaration.

package runtime

// MODEL: Gosched yields the processor. Go's body is checkTimeouts(), empty on
// linux (lock_futex.go), and mcall(gosched_m), which switches to the g0 stack
// (assembly, asm_amd64.s) and puts the goroutine back on the global run queue
// (the scheduler, which the semantics does not model). The model returns: a
// yield after which the same goroutine runs on is a schedule Go also has, and
// the semantics' interleaving gives every other one. Neither can panic.
func Gosched() {
}
