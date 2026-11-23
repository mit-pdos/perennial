package unittest

// recover() in a function or method called by defer. fmt's handleMethods and
// catchPanic, simplified; a deferred method value and a direct call, where the
// recovering method is the ordinary one, which is stuck.

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
// the ordinary catchPanic, which is stuck
func deferMethodValue(p *pp) {
	f := p.catchPanic
	defer f('v', "String")
	panic("p")
}

// a deferred interface method: also the ordinary one
type catcherI interface {
	catchPanic(verb byte, method string)
}

func deferInterfaceMethod(c catcherI) {
	defer c.catchPanic('v', "String")
	panic("p")
}

// a direct call: the ordinary catchPanic, which is stuck
func directCall(p *pp) {
	p.catchPanic('v', "String")
}
