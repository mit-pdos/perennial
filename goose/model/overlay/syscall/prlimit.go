// The Go model of syscall.prlimit1 (Perennial/Code/syscall.toml, [model]),
// spliced into zsyscall_linux_amd64.go (amd64 linux, the platform
// Perennial translates) in place of the real declaration.

package syscall

import "internal/gomodel"

// MODEL: prlimit1 is the prlimit64 system call: Go's body is
// RawSyscall6(SYS_PRLIMIT64, uintptr(pid), uintptr(resource),
// uintptr(unsafe.Pointer(newlimit)), uintptr(unsafe.Pointer(old)), 0, 0) and,
// for a non-zero errno, errnoErr(e1). The conversions of pointers to uintptr
// and the system call (assembly) have no semantics. The kernel reads
// *newlimit if newlimit is non-nil, writes *old if old is non-nil and the call
// succeeds, and returns 0 or an errno; it cannot fault on Go's pointers and
// cannot panic. The model reads *newlimit (so a concurrent write races, as
// with the kernel's read), may write arbitrary limits to *old (a superset of
// the kernel's writes: always on success, never on failure), and returns
// errnoErr of an arbitrary errno, nil for 0, as Go's stub does with the
// kernel's. The limits themselves, the process's state, are not modelled.
func prlimit1(pid int, resource int, newlimit *Rlimit, old *Rlimit) (err error) {
	if newlimit != nil {
		_ = *newlimit
	}
	if old != nil && gomodel.Choose() {
		old.Cur = gomodel.ChooseUint64()
		old.Max = gomodel.ChooseUint64()
	}
	e1 := Errno(gomodel.ChooseUint64())
	if e1 != 0 {
		err = errnoErr(e1)
	}
	return
}
