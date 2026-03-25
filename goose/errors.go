package goose

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/printer"
	"go/token"
	"runtime"
	"strings"
)

type locatable interface {
	Pos() token.Pos
}

// errorReporter groups methods for reporting errors, documenting what kind of
// issue was encountered in a uniform way.
type errorReporter struct {
	fset *token.FileSet
}

func newErrorReporter(fset *token.FileSet) errorReporter {
	return errorReporter{fset}
}

// printField implements custom printing for fields, since printer.Fprint does
// not support fields (the go syntax is somewhat context-sensitive)
func (r errorReporter) printField(f *ast.Field) string {
	var what bytes.Buffer
	var names []string
	for _, n := range f.Names {
		names = append(names, n.Name)
	}
	err := printer.Fprint(&what, r.fset, f.Type)
	if err != nil {
		panic(err.Error())
	}
	return fmt.Sprintf("%s %s",
		strings.Join(names, ", "),
		what.String())
}

func (r errorReporter) printGo(n locatable) string {
	if f, ok := n.(*ast.Field); ok {
		return r.printField(f)
	}
	if fl, ok := n.(*ast.FieldList); ok {
		var fields []string
		for _, f := range fl.List {
			fields = append(fields, r.printField(f))
		}
		return strings.Join(fields, "; ")
	}

	if s, ok := n.(fmt.Stringer); ok {
		return s.String()
	}

	var what bytes.Buffer
	err := printer.Fprint(&what, r.fset, n)
	if err != nil {
		panic(err.Error())
	}
	return what.String()
}

// getCaller returns the stack trace within goose from which an error was reported.
//
// In the long run, for an ordinary user this is more information than desired,
// but for now it's helpful to goose developers. We can eventually hide this
// information under a flag.
func getCaller(skip int) string {
	// (somewhat arbitrary) maximum number of frames of context in the goose
	// stack frame to show
	const numFrames = 4
	stackTrace := ""
	pc := make([]uintptr, numFrames)
	n := runtime.Callers(2+skip, pc)
	pc = pc[:n]
	frames := runtime.CallersFrames(pc)
	for i := range pc {
		frame, more := frames.Next()
		caller := fmt.Sprintf("%s\n  %s:%d", frame.Function, frame.File, frame.Line)
		if i == 0 {
			stackTrace += fmt.Sprintf("  %s\n", caller)
		} else {
			stackTrace += fmt.Sprintf("↻ %s\n", caller)
		}
		if !more {
			break
		}
	}
	return stackTrace
}

type gooseError struct{ err *ConversionError }

// A ConversionError is a detailed and structured error encountered while
// converting Go to Coq.
//
// Errors include a category describing the severity of the error.
//
// The category "unsupported" is the only error that should result from normal
// usage, when attempting to use a feature goose intentionally does not support.
//
// "todo" and "future" are markers for code that could be supported but is not
// currently handled.
//
// The categories "impossible(go)" and "impossible(no-examples)" indicate a bug
// in goose (at the very least these cases should be checked and result in an
// unsupported error)
type ConversionError struct {
	Category string
	// the main description of what went wrong
	Message string
	// the snippet in the source program responsible for the error
	GoCode string
	// (for internal debugging) file:lineno for the goose code that threw the
	// error
	GooseCaller string
	// (for systematic tests)
	Position token.Position
}

func (e *ConversionError) Error() string {
	lines := []string{
		fmt.Sprintf("[%s]: %s", e.Category, e.Message),
		fmt.Sprintf("%s", e.GoCode),
		"  goose call stack:",
		fmt.Sprintf("%s", e.GooseCaller),
		fmt.Sprintf("  src: %s", e.Position.String()),
	}
	return strings.Join(lines, "\n")
}

func (r errorReporter) prefixed(prefix string, n locatable, msg string, args ...interface{}) {
	where := r.fset.Position(n.Pos())
	what := r.printGo(n)
	formatted := fmt.Sprintf(msg, args...)

	err := &ConversionError{
		Category:    prefix,
		Message:     formatted,
		GoCode:      what,
		GooseCaller: getCaller(2),
		Position:    where,
	}

	panic(gooseError{err: err})
}

// nope reports a situation that believed to be impossible from reading the
// documentation.
func (r errorReporter) nope(n locatable, msg string, args ...interface{}) {
	r.prefixed("impossible(go)", n, msg, args...)
}

// noExample reports a situation believed to be impossible because I couldn't
// think of how to do it in Go.
func (r errorReporter) noExample(n locatable, msg string, args ...interface{}) {
	r.prefixed("impossible(no-examples)", n, msg, args...)
}

// todo reports a situation that is intended to be handled but we haven't gotten
// around to.
func (r errorReporter) todo(n locatable, msg string, args ...interface{}) {
	r.prefixed("todo", n, msg, args...)
}

// unsupported reports something intentionally unhandled (the code should not
// use this feature).
func (r errorReporter) unsupported(n locatable, msg string, args ...interface{}) {
	r.prefixed("unsupported", n, msg, args...)
}
