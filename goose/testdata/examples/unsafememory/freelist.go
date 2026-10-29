package unsafememory

import "unsafe"

// writeIds is internal/freelist/shared.go's Write: the ids as a []Pgid laid
// over the page after its header; count 0xFFFF means ids[0] holds the count.
func writeIds(p *Page, ids []Pgid) {
	p.flags = freelistPageFlag
	l := len(ids)
	if l == 0 {
		p.count = uint16(l)
	} else if l < 0xFFFF {
		p.count = uint16(l)
		data := unsafeAdd(unsafe.Pointer(p), unsafe.Sizeof(*p))
		dst := unsafe.Slice((*Pgid)(data), l)
		copy(dst, ids)
	} else {
		p.count = 0xFFFF
		data := unsafeAdd(unsafe.Pointer(p), unsafe.Sizeof(*p))
		dst := unsafe.Slice((*Pgid)(data), l+1)
		dst[0] = Pgid(l)
		copy(dst[1:], ids)
	}
}

// freelistPageCount is Page.FreelistPageCount.
func (p *Page) freelistPageCount() (int, int) {
	if p.count == 0xFFFF {
		c := *(*Pgid)(unsafeAdd(unsafe.Pointer(p), unsafe.Sizeof(*p)))
		return 1, int(c)
	}
	return 0, int(p.count)
}

// readIds is Page.FreelistPageIds followed by the copy freelist.Read makes.
func readIds(p *Page) []Pgid {
	idx, count := p.freelistPageCount()
	if count == 0 {
		return nil
	}
	data := unsafeIndex(unsafe.Pointer(p), unsafe.Sizeof(*p), unsafe.Sizeof(Pgid(0)), idx)
	ids := unsafe.Slice((*Pgid)(data), count)
	out := make([]Pgid, count)
	copy(out, ids)
	return out
}

// freelistSize is the bytes a freelist page with n ids needs.
func freelistSize(n int) int {
	if n >= 0xFFFF {
		n++
	}
	return int(pageHeaderSize) + int(unsafe.Sizeof(Pgid(0)))*n
}
