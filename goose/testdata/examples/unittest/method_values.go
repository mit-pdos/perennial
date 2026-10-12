package unittest

// Method values save their receiver when evaluated: see the semantics tests.

type mvT struct {
	x uint64
}

func (t mvT) val() {}

func (t *mvT) ptr() {}

type mvEmbed struct {
	mvT
}

type mvEmbedPtr struct {
	*mvT
}

func mvMakeEmbed() mvEmbed {
	return mvEmbed{}
}

func mvMakeEmbedPtr() mvEmbedPtr {
	return mvEmbedPtr{}
}

func methodValues(p *mvT, e mvEmbed, ep mvEmbedPtr) {
	t := mvT{}
	f1 := t.val             // copies t
	f2 := t.ptr             // (&t).ptr
	f3 := p.val             // copies *p
	f4 := p.ptr             // saves p
	f5 := e.val             // copies e.mvT
	f6 := e.ptr             // (&e.mvT).ptr
	f7 := ep.val            // copies *ep.mvT
	f8 := ep.ptr            // saves ep.mvT
	f9 := mvMakeEmbed().val // copies the result's mvT
	f10 := mvMakeEmbedPtr().ptr
	f1()
	f2()
	f3()
	f4()
	f5()
	f6()
	f7()
	f8()
	f9()
	f10()
	defer t.val()
	go t.val()
	go p.val()
	defer p.ptr()
}
