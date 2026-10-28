// Package bboltmini is bbolt's use of byte memory, cut down to what a proof
// has to get through: page headers and element arrays laid over a []byte, keys
// and values sliced out of a page at element-relative offsets, the meta page's
// checksum over a struct's bytes, the freelist's id array, inline buckets at
// unaligned offsets, and an atomic on a *time.Duration cast to *int64.
//
// Each construct is written the way go.etcd.io/bbolt v1.5.0 writes it, with
// the changes of docs/design/unsafe-memory.md section 6: the helpers use
// unsafe.Add and unsafe.Slice instead of uintptr arithmetic and a
// (*[MaxAllocSize]byte) view, an element's pos is computed from offsets
// instead of as a pointer difference, and whole-struct copies between two
// memory places go through a local. The original forms are in package
// stuck, with the other constructs the model must not verify.
package bboltmini

import (
	"bytes"
	"unsafe"
)

type Pgid uint64

const (
	branchPageFlag   = 0x01
	leafPageFlag     = 0x02
	metaPageFlag     = 0x04
	freelistPageFlag = 0x10
)

// Page is internal/common/page.go's Page.
type Page struct {
	id       Pgid
	flags    uint16
	count    uint16
	overflow uint32
}

type leafPageElement struct {
	flags uint32
	pos   uint32
	ksize uint32
	vsize uint32
}

type branchPageElement struct {
	pos   uint32
	ksize uint32
	pgid  Pgid
}

const (
	pageHeaderSize        = unsafe.Sizeof(Page{})
	leafPageElementSize   = unsafe.Sizeof(leafPageElement{})
	branchPageElementSize = unsafe.Sizeof(branchPageElement{})
)

// unsafeAdd, unsafeIndex and unsafeByteSlice are internal/common/unsafe.go's
// helpers in the patched forms of the design (section 6): unsafe.Add for
// uintptr(base)+offset, and unsafe.Slice for the (*[MaxAllocSize]byte) view.
func unsafeAdd(base unsafe.Pointer, offset uintptr) unsafe.Pointer {
	return unsafe.Add(base, offset)
}

func unsafeIndex(base unsafe.Pointer, offset uintptr, elemsz uintptr, n int) unsafe.Pointer {
	return unsafe.Add(base, offset+uintptr(n)*elemsz)
}

func unsafeByteSlice(base unsafe.Pointer, offset uintptr, i, j int) []byte {
	return unsafe.Slice((*byte)(unsafeAdd(base, offset)), j)[i:j:j]
}

// pageAt is db.go's pageInBuffer: the page at byte offset off of buf.
func pageAt(buf []byte, off int) *Page {
	return (*Page)(unsafe.Pointer(&buf[off]))
}

// pageBytes recovers the n bytes of the buffer p was laid over (tx.go:543,582).
func pageBytes(p *Page, n int) []byte {
	return unsafeByteSlice(unsafe.Pointer(p), 0, 0, n)
}

func (p *Page) leafPageElement(index uint16) *leafPageElement {
	return (*leafPageElement)(unsafeIndex(unsafe.Pointer(p), unsafe.Sizeof(*p),
		leafPageElementSize, int(index)))
}

func (p *Page) leafPageElements() []leafPageElement {
	if p.count == 0 {
		return nil
	}
	data := unsafeAdd(unsafe.Pointer(p), unsafe.Sizeof(*p))
	return unsafe.Slice((*leafPageElement)(data), int(p.count))
}

func (p *Page) branchPageElement(index uint16) *branchPageElement {
	return (*branchPageElement)(unsafeIndex(unsafe.Pointer(p), unsafe.Sizeof(*p),
		unsafe.Sizeof(branchPageElement{}), int(index)))
}

func (p *Page) branchPageElements() []branchPageElement {
	if p.count == 0 {
		return nil
	}
	data := unsafeAdd(unsafe.Pointer(p), unsafe.Sizeof(*p))
	return unsafe.Slice((*branchPageElement)(data), int(p.count))
}

// Keys and values are at pos bytes past their element, outside the element
// struct but inside the page.
func (n *leafPageElement) key() []byte {
	i := int(n.pos)
	j := i + int(n.ksize)
	return unsafeByteSlice(unsafe.Pointer(n), 0, i, j)
}

func (n *leafPageElement) value() []byte {
	i := int(n.pos) + int(n.ksize)
	j := i + int(n.vsize)
	return unsafeByteSlice(unsafe.Pointer(n), 0, i, j)
}

func (n *branchPageElement) key() []byte {
	return unsafeByteSlice(unsafe.Pointer(n), 0, int(n.pos), int(n.pos)+int(n.ksize))
}

func (p *Page) pageElementSize() uintptr {
	if p.flags&leafPageFlag != 0 {
		return leafPageElementSize
	}
	return branchPageElementSize
}

// searchLeaf is cursor.go's nsearch: the index of the first key >= key, by
// binary search over the element array viewed as a []leafPageElement.
func searchLeaf(p *Page, key []byte) int {
	elems := p.leafPageElements()
	lo, hi := 0, len(elems)
	for lo < hi {
		mid := lo + (hi-lo)/2
		if bytes.Compare(elems[mid].key(), key) < 0 {
			lo = mid + 1
		} else {
			hi = mid
		}
	}
	return lo
}

// inode is internal/common/inode.go's Inode.
type inode struct {
	flags uint32
	pgid  Pgid
	key   []byte
	value []byte
}

// writeInodeToPage is internal/common/inode.go's WriteInodeToPage. p's flags
// say whether it is a leaf or a branch page; it returns the bytes written.
func writeInodeToPage(inodes []inode, p *Page) uint32 {
	off := unsafe.Sizeof(*p) + p.pageElementSize()*uintptr(len(inodes))
	isLeaf := p.flags&leafPageFlag != 0
	for i, item := range inodes {
		sz := len(item.key) + len(item.value)
		b := unsafeByteSlice(unsafe.Pointer(p), off, 0, sz)
		elemOff := unsafe.Sizeof(*p) + p.pageElementSize()*uintptr(i)
		if isLeaf {
			elem := p.leafPageElement(uint16(i))
			elem.pos = uint32(off - elemOff)
			elem.flags = item.flags
			elem.ksize = uint32(len(item.key))
			elem.vsize = uint32(len(item.value))
		} else {
			elem := p.branchPageElement(uint16(i))
			elem.pos = uint32(off - elemOff)
			elem.ksize = uint32(len(item.key))
			elem.pgid = item.pgid
		}
		off += uintptr(sz)
		l := copy(b, item.key)
		copy(b[l:], item.value)
	}
	return uint32(off)
}

// readInodeFromPage is internal/common/inode.go's ReadInodeFromPage: the
// returned keys and values alias the page.
func readInodeFromPage(p *Page) []inode {
	inodes := make([]inode, int(p.count))
	isLeaf := p.flags&leafPageFlag != 0
	for i := 0; i < int(p.count); i++ {
		if isLeaf {
			elem := p.leafPageElement(uint16(i))
			inodes[i] = inode{flags: elem.flags, key: elem.key(), value: elem.value()}
		} else {
			elem := p.branchPageElement(uint16(i))
			inodes[i] = inode{pgid: elem.pgid, key: elem.key()}
		}
	}
	return inodes
}

// writeLeaf lays a leaf page with inodes over the start of buf.
func writeLeaf(buf []byte, inodes []inode) *Page {
	p := pageAt(buf, 0)
	p.flags = leafPageFlag
	p.count = uint16(len(inodes))
	writeInodeToPage(inodes, p)
	return p
}

// pageSize is the size of a leaf or branch page holding inodes (node.size).
func pageSize(inodes []inode) int {
	sz := int(pageHeaderSize) + len(inodes)*int(leafPageElementSize)
	for _, item := range inodes {
		sz += len(item.key) + len(item.value)
	}
	return sz
}
