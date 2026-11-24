// The Go models of fmt (Perennial/Code/fmt.toml, [model]): errorf, Fprintf, Printf and
// pp.doPrint, spliced into errors.go and print.go in place of the real declarations, and the
// additions they need besides the model printer (printmodel.go). Sprintf, Errorf, Fprint and the
// real printer stay Go's own, translated.
//
// Why models at all: the real print path (pp.doPrintf, pp.printArg) is translated and proved only
// on stage 1's subset (fmt.Fits, perennial#671). Elsewhere it is stuck: on floats and complex
// numbers (strconv.AppendFloat and pp.fmtComplex are not translated), on %q of an integer
// (strconv.AppendQuoteRune), on %T, %p, a bad verb and %!(EXTRA ...) (reflect.TypeOf), and on
// named integer and string types, a []string, and a value of integer kind with String or Error
// under a non-method verb (pp.printValue, which reflects). The specs of Errorf, Printf, Fprintf
// and Fprint admit those calls (fmt.argsOk, fmt.printArgOk), so these four print with the model
// printer instead: doPrintf formats exactly the common directives of inert arguments and of a
// []byte or []string, appending them to the printer's buffer p.buf as Go does, and from the first
// other directive on appends arbitrary strings, before each call of an argument's Error() or
// String() (where Go's handleMethods calls it) and at the end. The buffer is observable outside
// fmt: Fprintf and Fprint hand p.buf to w.Write, and a writer that keeps the slice aliases the
// buffer of a printer the pool (ppFree) hands out again, to a later errorf, Fprintf or Fprint, or
// to a method that the same call calls; so the model appends to p.buf what Go has appended by each
// method call (an arbitrary string covers it), and errorf reads its message back from p.buf. it is stuck (notModelled)
// where it does not follow Go: a Format or GoString method Go would call, a reflect.Value,
// reflection into a struct, pointer, map or other slice, an argument index or a '*' width with an
// argument that is not inert, a method that panics (Go's catchPanic recovers it). Its output is
// Go's, the arbitrary strings standing for any suffix, and it calls the methods Go calls in Go's
// order: model ⊇ Go, checked by goose/model/fmt/model_diff_test.go (TestModelSprintf,
// TestModelBytesExact, TestModelStringsExact, TestModelErrorf, TestModelFprintf, TestModelFprint,
// TestModelPrintf) and sprintf_test.go, and, for the buffer, by TestModelAlias (testdata/alias,
// run by etc/model-tests.sh under the overlay).

package fmt

import (
	"internal/gomodel"
	"internal/poll"
	"internal/stringslite"
	"io"
	"io/fs"
	"reflect"
	"syscall"
)

// MODEL: errorf is Go's, but for its printer: Go's p.doPrintf(format, a), with p.wrapErrs set, is
// the model printer's doPrintf(&p.buf, format, a, true), which appends the message to p.buf (Go's,
// with arbitrary strings from the first directive it does not format) and gives the indices of the
// %w arguments (or that they are unknown); errorfResult builds the error from them as Go's switch
// on len(p.wrappedErrs) does: errors.New, a *wrapError, a *wrapErrors (see the file comment for
// what the model printer covers and where it is stuck; TestModelErrorf compares the error's kind,
// message and wrapped errors with Go's). The printer is Go's own, from newPrinter and back to the
// pool with p.free(), and the message is read back from p.buf as Go reads it: the pool is
// observable outside fmt, since Fprintf hands p.buf to a writer, which may keep the slice and see
// what a later errorf writes into the same printer's buffer, or write into it itself
// (TestModelAlias, goose/model/fmt).
func errorf(format string, a ...any) error {
	if len(a) == 0 && stringslite.IndexByte(format, '%') == -1 {
		return nil
	}
	p := newPrinter()
	wrapped, unknown := doPrintf(&p.buf, format, a, true)
	s := string(p.buf)
	err := errorfResult(s, wrapped, unknown, a)
	p.free()
	return err
}

// MODEL: Fprintf is Go's, but for one line: Go's p.doPrintf(format, a) is the model printer's
// doPrintf(&p.buf, format, a, false), which appends to p.buf what Go appends up to its first
// method call or directive the model does not format, and arbitrary strings from there, before
// each method call and at the end (see the file comment for what the model printer covers and
// where it is stuck; TestModelFprintf checks the bytes Write receives and the methods called;
// TestModelAlias a method reading p.buf through a slice an earlier Write kept). The printer, its
// pool (ppFree), the one w.Write(p.buf) and p.free() are Go's own.
func Fprintf(w io.Writer, format string, a ...any) (n int, err error) {
	p := newPrinter()
	doPrintf(&p.buf, format, a, false)
	n, err = w.Write(p.buf)
	p.free()
	return
}

// MODEL: Printf is Go's Fprintf(os.Stdout, format, a...) with the writer stdout{} for os.Stdout:
// the model of os has no Stdout (os.toml: its variable is not allocated, so a program that reads
// or assigns os.Stdout is stuck), and Printf always writes to the file Go opens as os.Stdout
// (descriptor 1, "/dev/stdout"); stdout.Write has every result Go's (*os.File).Write of it has.
func Printf(format string, a ...any) (n int, err error) {
	return Fprintf(stdout{}, format, a...)
}

// stdout is the model's os.Stdout for Printf.
type stdout struct{}

// Write: what Go's (*os.File).Write of os.Stdout can return. Go writes b with poll.FD.Write
// (write(2) until all is written or an error), then wraps a failure in f.wrapErr("write", e):
//   - all of b written, no error: (len(b), nil);
//   - otherwise n bytes, 0 <= n <= len(b) (also n == len(b) == 0, when write(2) of no bytes fails),
//     and *fs.PathError{Op: "write", Path: "/dev/stdout", Err: e} (os.PathError) with e one of:
//     fs.ErrClosed (os.ErrClosed, wrapErr's for poll.ErrFileClosing: writeLock on a closed fd, or
//     the poller), poll.ErrDeadlineExceeded (os.ErrDeadlineExceeded) and poll.ErrNotPollable (the
//     poller's prepareWrite/waitWrite), io.ErrUnexpectedEOF (write(2)
//     wrote nothing, no error), or the syscall.Errno of write(2), between 1 and 4095 (Linux's
//     errno range); on EPIPE Go's epipecheck raises SIGPIPE, which kills the process unless the
//     program handles or ignores it: the model may then not return (a loop, which covers the
//     death), or return the error. (Go's io.ErrShortWrite for n != len(b) is always overwritten by
//     the wrapped error: FD.Write returns n < len(b) only with an error.) Go panics where write(2)
//     claims more bytes than asked (panic "invalid return from write"): not modelled, excluded
//     by an assumption on the environment that the write never claims that. The assumption is not
//     only that the kernel has no bug: golang/go#61060 reports the panic with VPN software
//     installed.
func (stdout) Write(b []byte) (n int, err error) {
	if gomodel.Choose() {
		return len(b), nil
	}
	n = int(gomodel.ChooseUint64() % (uint64(len(b)) + 1))
	var e error
	switch gomodel.ChooseUint64() {
	case 0:
		e = fs.ErrClosed
	case 1:
		e = poll.ErrDeadlineExceeded
	case 2:
		e = poll.ErrNotPollable
	case 3:
		e = io.ErrUnexpectedEOF
	default:
		errno := syscall.Errno(1 + gomodel.ChooseUint64()%4095)
		if errno == syscall.EPIPE && gomodel.Choose() {
			for {
			}
		}
		e = errno
	}
	return n, &fs.PathError{Op: "write", Path: "/dev/stdout", Err: e}
}

// MODEL: pp.doPrint prints the operands under %v, a space between two that are not strings. Go
// tells a string by reflect.TypeOf(arg).Kind() == reflect.String (reflection, which is stuck) and
// prints each with p.printArg, which is stuck on the operands of the file comment; Fprint's spec
// admits them (fmt.printArgOk). The model calls of each operand what Go's printArg calls under %v
// (visitArg: its Error() or String(), stuck where the model printer is), after appending arbitrary
// strings to p.buf (writeArbitrary), which stand for what Go has appended by then (a method may
// read p.buf through a slice a writer kept), and appends arbitrary strings at the end, for the
// rest of Go's output (TestModelFprint checks the calls, TestModelAlias the buffer). Fprint and
// Sprint, Go's own, print with it.
func (p *pp) doPrint(a []any) {
	for _, x := range a {
		writeArbitrary(&p.buf)
		visitArg(x, 'v', false, false)
	}
	writeArbitrary(&p.buf)
}

// chooseString is an arbitrary string, the model printer's output from where it stops following
// Go: it can return every string (and may also not terminate, which partial correctness allows).
func chooseString() string {
	var s string
	for gomodel.ChooseUint64() != 0 {
		s += string([]byte{byte(gomodel.ChooseUint64())})
	}
	return s
}

// notModelled is the model printer's stuck point, where it does not follow Go: gomodel.Stuck.
func notModelled() {
	gomodel.Stuck()
}

// underlyingAs[T](x) is x's value converted to T and true, if x's dynamic type has T's underlying
// type, and the zero T and false otherwise (also for a nil x): reflect.ValueOf(x).Kind() is T's
// kind, which plain Go cannot test without reflection. A primitive stub (fmt.toml, trusted): its
// GooseLang model is TypeAssertUnderlying2 T (Perennial/TrustedCode/fmt.lean), and this body, for
// gc builds, is the reflection, for the integer types and string that the model printer asks.
func underlyingAs[T any](x any) (T, bool) {
	var z T
	if x == nil {
		return z, false
	}
	v := reflect.ValueOf(x)
	zt := reflect.TypeOf(z)
	if v.Kind() != zt.Kind() {
		return z, false
	}
	return v.Convert(zt).Interface().(T), true
}
