package bboltmini

import (
	"bytes"
	"sync"
	"sync/atomic"
	"unsafe"
)

// The verification targets: each test function returns true in every
// execution, and its spec is exactly that ({{ True }} testX() {{ RET true }}).
// README.md says which part of the semantics and of the program logic each one
// exercises.

const bucketLeafFlag = 0x01

func leafInodes() []inode {
	return []inode{
		{key: []byte("apple"), value: []byte("1")},
		{key: []byte("banana"), value: []byte("22")},
		{key: []byte("cherry"), value: []byte{}},
	}
}

func inodesEqual(a, b []inode) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i].flags != b[i].flags || a[i].pgid != b[i].pgid ||
			!bytes.Equal(a[i].key, b[i].key) || !bytes.Equal(a[i].value, b[i].value) {
			return false
		}
	}
	return true
}

// Integers are little-endian bytes, at gc's field offsets.
func testEndianness() bool {
	buf := make([]byte, int(pageHeaderSize))
	buf[0] = 1
	buf[9] = 2
	p := pageAt(buf, 0)
	if p.id != 1 || p.flags != 0x0200 {
		return false
	}
	p.count = 0x0102
	p.overflow = 0x03040506
	return buf[10] == 0x02 && buf[11] == 0x01 &&
		buf[12] == 0x06 && buf[13] == 0x05 && buf[14] == 0x04 && buf[15] == 0x03
}

// A leaf page written through element views reads back the same inodes.
func testLeafRoundTrip() bool {
	in := leafInodes()
	buf := make([]byte, 4096)
	p := writeLeaf(buf, in)
	return inodesEqual(readInodeFromPage(p), in)
}

// The same for a branch page, whose element has a uint64 at offset 8.
func testBranchRoundTrip() bool {
	in := []inode{
		{pgid: 7, key: []byte("a")},
		{pgid: 1 << 40, key: []byte("m")},
	}
	buf := make([]byte, 4096)
	p := pageAt(buf, 0)
	p.flags = branchPageFlag
	p.count = uint16(len(in))
	writeInodeToPage(in, p)
	return inodesEqual(readInodeFromPage(p), in)
}

// A page at a non-zero offset of its buffer leaves the rest of the buffer alone.
func testPageAtOffset() bool {
	buf := make([]byte, 2*4096)
	p := pageAt(buf, 4096)
	p.id = 1
	p.flags = leafPageFlag
	in := leafInodes()
	p.count = uint16(len(in))
	writeInodeToPage(in, p)
	for i := 0; i < 4096; i++ {
		if buf[i] != 0 {
			return false
		}
	}
	return pageAt(buf, 4096).id == 1 && inodesEqual(readInodeFromPage(pageAt(buf, 4096)), in)
}

// Every view of a page is the same memory: the buffer, pageBytes, a value
// slice, an element pointer and the unsafe.Slice element array.
func testAliasing() bool {
	buf := make([]byte, 4096)
	p := writeLeaf(buf, leafInodes())
	// header 16, 3 elements 48; "apple1" at 64, "banana22" at 70: the value "22" at 76
	v := p.leafPageElement(1).value()
	v[0] = 'X'
	if buf[76] != 'X' || pageBytes(p, len(buf))[76] != 'X' {
		return false
	}
	elems := p.leafPageElements()
	elems[2].vsize = 1
	buf[16+2*16+4] = 0 // the third element's pos, low byte
	return p.leafPageElement(2).vsize == 1 && elems[2].pos == 0 &&
		len(pageBytes(p, len(buf))) == len(buf)
}

// Binary search over the []leafPageElement view.
func testSearch() bool {
	buf := make([]byte, 4096)
	p := writeLeaf(buf, leafInodes())
	return searchLeaf(p, []byte("")) == 0 &&
		searchLeaf(p, []byte("apple")) == 0 &&
		searchLeaf(p, []byte("b")) == 1 &&
		searchLeaf(p, []byte("banana")) == 1 &&
		searchLeaf(p, []byte("c")) == 2 &&
		searchLeaf(p, []byte("zzz")) == 3
}

// The checksum is over the bytes of a Go-allocated Meta (in write) and of a
// Meta in a page (in validate); a whole-struct copy goes into and out of the
// page; flipping any covered byte breaks the checksum.
func testMetaChecksum() bool {
	m := &Meta{
		magic: magic, version: version, pageSize: 4096,
		root: InBucket{root: 3}, freelist: 2, pgid: 4, txid: 7,
	}
	buf := make([]byte, 4096)
	p := pageAt(buf, 0)
	m.write(p)
	pm := p.meta()
	if p.id != 1 || !pm.validate() || *pm != *m {
		return false
	}
	cp := &Meta{}
	v := *pm
	*cp = v
	if !cp.validate() {
		return false
	}
	buf[int(pageHeaderSize)+8] ^= 1 // pageSize's low byte
	return !pm.validate() && cp.validate()
}

func testFreelistRoundTrip() bool {
	ids := []Pgid{5, 3, 9}
	buf := make([]byte, freelistSize(len(ids)))
	p := pageAt(buf, 0)
	writeIds(p, ids)
	out := readIds(p)
	if p.count != 3 || len(out) != 3 {
		return false
	}
	for i := range ids {
		if out[i] != ids[i] {
			return false
		}
	}
	empty := make([]byte, freelistSize(0))
	writeIds(pageAt(empty, 0), nil)
	return readIds(pageAt(empty, 0)) == nil
}

// 0xFFFF or more ids: the count moves into ids[0].
func testFreelistOverflow() bool {
	n := 0x10000
	ids := make([]Pgid, n)
	for i := range ids {
		ids[i] = Pgid(i + 2)
	}
	buf := make([]byte, freelistSize(n))
	p := pageAt(buf, 0)
	writeIds(p, ids)
	out := readIds(p)
	if p.count != 0xFFFF || len(out) != n {
		return false
	}
	for i := range ids {
		if out[i] != ids[i] {
			return false
		}
	}
	return true
}

// An inline bucket stored as a leaf value, at offsets that are and are not
// 8-aligned depending on the key's length; opened read-only and writable.
// A writable open never writes through to the stored value.
func testInlineBucket() bool {
	inner := leafInodes()
	value := writeInlineBucket(&InBucket{sequence: 42}, inner)
	for keyLen := 1; keyLen <= 8; keyLen++ {
		key := bytes.Repeat([]byte("k"), keyLen)
		outer := make([]byte, 4096)
		p := writeLeaf(outer, []inode{{flags: bucketLeafFlag, key: key, value: value}})
		v := p.leafPageElement(0).value()
		if !bytes.Equal(v, value) {
			return false
		}
		b, ip := openInlineBucket(v, true)
		if b.sequence != 42 || !inodesEqual(readInodeFromPage(ip), inner) {
			return false
		}
		b.sequence = 43
		b2, ip2 := openInlineBucket(v, false)
		if b2.sequence != 42 || !inodesEqual(readInodeFromPage(ip2), inner) {
			return false
		}
	}
	return true
}

// Atomics on a Go-allocated struct, one of them through *time.Duration cast
// to *int64.
func testStatsConcurrent() bool {
	s := &TxStats{}
	var wg sync.WaitGroup
	for i := 0; i < 2; i++ {
		wg.Add(1)
		go func() {
			s.IncWriteTime(3)
			s.IncPageCount(1)
			wg.Done()
		}()
	}
	wg.Wait()
	return s.GetWriteTime() == 6 && atomic.LoadInt64(&s.PageCount) == 2
}

// Whole-struct copies, through a local, between disjoint views of one buffer
// and onto the same place.
func testDisjointStructCopy() bool {
	buf := make([]byte, 2*int(unsafe.Sizeof(Meta{})))
	a := (*Meta)(unsafe.Pointer(&buf[0]))
	b := (*Meta)(unsafe.Pointer(&buf[unsafe.Sizeof(Meta{})]))
	a.txid = 7
	v := *a
	*b = v
	same := (*Meta)(unsafe.Pointer(&buf[0]))
	v = *a
	*same = v
	return b.txid == 7 && a.txid == 7
}

// A buffer reused at shifted offsets, as pagePool reuses page buffers: after
// a whole-struct load at offset 0 and byte stores, the same type is stored and
// loaded at offset 8.
func testBufferReuseShifted() bool {
	buf := make([]byte, 32)
	buf[0] = 1
	old := *(*InBucket)(unsafe.Pointer(&buf[0]))
	for i := range buf {
		buf[i] = 0
	}
	*(*InBucket)(unsafe.Pointer(&buf[8])) = InBucket{root: 3, sequence: 4}
	b := *(*InBucket)(unsafe.Pointer(&buf[8]))
	return old.root == 1 && b.root == 3 && b.sequence == 4 && buf[0] == 0
}

// Whole loads of one type at overlapping offsets are defined: a load is a
// plain read of the bytes (design R2).
func testOverlappingLoads() bool {
	buf := make([]byte, 24)
	buf[8] = 1
	x := *(*InBucket)(unsafe.Pointer(&buf[0]))
	y := *(*InBucket)(unsafe.Pointer(&buf[8]))
	return x.sequence == 1 && y.root == 1
}

// A float's bits through a uint64 view: floats are plain (design R1), 8 byte
// cells holding their IEEE bits.
func testFloatBits() bool {
	f := 1.0
	return *(*uint64)(unsafe.Pointer(&f)) == 0x3FF0000000000000
}

// Atomics of two widths on one word, one after the other. The concurrent case
// is outside the model (design section 5, A3).
func testMixedWidthAtomics() bool {
	var u uint64
	atomic.AddUint64(&u, 1)
	atomic.AddUint32((*uint32)(unsafe.Pointer(&u)), 1)
	return u == 2
}

// A whole-struct copy between partially overlapping views, through a local.
// gc 1.26 copies *src into a stack slot first, so the result is memmove's
// (design section 5, A2), and value semantics gives the same.
type words struct{ a, b, c, d, e, f, g, h uint64 }

//go:noinline
func copyWordsViaTemp(dst, src *words) {
	x := *src
	*dst = x
}

func testOverlappingCopyViaTemp() bool {
	buf := make([]uint64, 16)
	for i := range buf {
		buf[i] = uint64(i)
	}
	copyWordsViaTemp((*words)(unsafe.Pointer(&buf[1])), (*words)(unsafe.Pointer(&buf[0])))
	return buf[3] == 2
}

// unsafe.Add one past the end of the allocation: invalid in Go (gc's collector can stop on
// such a pointer), but the model does not check it (docs/KNOWN_LIMITATIONS.md), so this is a
// target, true in Go.
func testAddPastEnd() bool {
	buf := make([]byte, 16)
	return unsafe.Add(unsafe.Pointer(&buf[0]), len(buf)) != nil
}
