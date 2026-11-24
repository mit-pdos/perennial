// The Go models of log.Printf, log.Println and log's init function
// (Perennial/Code/log.toml, [model]), spliced into log.go in place of the real
// declarations; modelDiscard is an addition.

package log

import (
	"fmt"
	"internal/gomodel"
)

// MODEL: Printf is std.output(0, 2, func(b []byte) []byte { return
// fmt.Appendf(b, format, v...) }). The standard logger std is not translated
// (its initializer is New(os.Stderr, "", LstdFlags), and os.Stderr is not a
// File in the model: perennial#663), nor is any function that changes it
// (SetOutput, SetFlags, SetPrefix, Default, Logger's setters), so in every
// execution of the model std is as New made it: flags LstdFlags, no prefix,
// output os.Stderr. Its output method then:
//   - returns at once if the output is io.Discard (l.isDiscard), which needs
//     a SetOutput no execution reaches; the model has both outcomes anyway
//     (gomodel.Choose: it formats or does nothing);
//   - reads the clock (time.Now), the prefix and the flags (atomic loads), and
//     with LstdFlags not the caller's file and line: no effect;
//   - takes a buffer from bufferPool, formats the date and time into it, and
//     calls the closure, which formats the arguments as fmt.Appendf does:
//     fmt's printer and doPrintf, which call the arguments' Error, String and
//     Format methods, the only effects on the program. The model formats them
//     with fmt.Fprintf, which runs the same newPrinter, doPrintf and free;
//   - appends a newline, takes std.outMu (held only by output, never while
//     the arguments' methods run) and writes the bytes to standard error,
//     ignoring the result: an effect outside the program, which the model
//     drops, as it drops Fprintf's bytes (modelDiscard). The write can also
//     block (a full stderr pipe, holding std.outMu) or end the process
//     (EPIPE on fd 2: os.File.Write's epipecheck raises SIGPIPE): both stop
//     the program there, so their traces are prefixes of the model's, which
//     returns (partial correctness, as for an exit).
//
// Neither can panic other than through the arguments' methods.
func Printf(format string, v ...any) {
	if gomodel.Choose() {
		fmt.Fprintf(modelDiscard{}, format, v...)
	}
}

// MODEL: Println is Printf's model (see there) with fmt.Appendln(b, v...) in
// place of Appendf: the model formats the arguments with fmt.Fprintln, which
// runs the same newPrinter, doPrintln and free.
func Println(v ...any) {
	if gomodel.Choose() {
		fmt.Fprintln(modelDiscard{}, v...)
	}
}

// modelDiscard is the writer of the models above: Write accepts every byte
// and does nothing, as io.Discard's.
type modelDiscard struct{}

func (modelDiscard) Write(p []byte) (int, error) {
	return len(p), nil
}

// MODEL: log's init function stores a closure into
// log/internal.DefaultOutput, the output of log/slog's default handler; it
// cannot panic. log/slog and log/internal are not translated, so no execution
// of the model reads that variable, and the model does nothing.
//
//gomodel:replace init.0 "internal.DefaultOutput = func(pc uintptr, data []byte) error {"
func init() {
}
