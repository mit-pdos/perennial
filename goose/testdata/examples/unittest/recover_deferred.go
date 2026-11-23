package unittest

// recover() in a function or method called by defer. fmt's handleMethods and
// catchPanic, simplified; a deferred method value, a deferred interface method
// and a direct call, which reach the ordinary catchPanic: it has no declaration
// (only catchPanic'deferred does), so these are unprovable.

type pp struct {
	buf       []byte
	panicking bool
}

func (p *pp) catchPanic(verb byte, method string) {
	if err := recover(); err != nil {
		if p.panicking {
			panic(err)
		}
		p.buf = append(p.buf, "%!"...)
		p.buf = append(p.buf, verb)
		p.buf = append(p.buf, "(PANIC="...)
		p.buf = append(p.buf, method...)
		p.buf = append(p.buf, " method)"...)
	}
}

type stringer interface {
	String() string
}

func (p *pp) handleMethods(arg any, verb byte) (handled bool) {
	if s, ok := arg.(stringer); ok {
		handled = true
		defer p.catchPanic(verb, "String")
		p.buf = append(p.buf, s.String()...)
		return
	}
	return false
}

// a value receiver, deferred through a pointer and through an addressable value
type valCatcher struct{}

func (valCatcher) catch() {
	recover()
}

func deferValueMethod(p *valCatcher) {
	var v valCatcher
	defer p.catch()
	defer v.catch()
	panic("p")
}

// a deferred method value: the callee is not known statically, so this defers
// the ordinary catchPanic, which has no declaration
func deferMethodValue(p *pp) {
	f := p.catchPanic
	defer f('v', "String")
	panic("p")
}

// a deferred interface method: also the ordinary one (*pp satisfies catcherI)
type catcherI interface {
	catchPanic(verb byte, method string)
}

func deferInterfaceMethod(c catcherI) {
	defer c.catchPanic('v', "String")
	panic("p")
}

// a direct call: the ordinary catchPanic, which has no declaration
func directCall(p *pp) {
	p.catchPanic('v', "String")
}

// an interface conversion of a type with a recovering method: the method set
// still has catchPanic
func convertToInterface(p *pp) catcherI {
	return p
}

func topCatch() {
	recover()
}

// a deferred function value of a recovering top-level function: the ordinary
// topCatch, which has no declaration
func deferFuncValue() {
	f := topCatch
	defer f()
	panic("p")
}
