package unsafememory

import "unsafe"

// InBucket is internal/common/bucket.go's InBucket.
type InBucket struct {
	root     Pgid
	sequence uint64
}

// Meta is internal/common/meta.go's Meta (64 bytes, no padding).
type Meta struct {
	magic    uint32
	version  uint32
	pageSize uint32
	flags    uint32
	root     InBucket
	freelist Pgid
	pgid     Pgid
	txid     uint64
	checksum uint64
}

const (
	magic   uint32 = 0xED0CDAED
	version uint32 = 2
)

// meta is Page.Meta: the Meta right after the page header.
func (p *Page) meta() *Meta {
	return (*Meta)(unsafeAdd(unsafe.Pointer(p), unsafe.Sizeof(*p)))
}

// sum64 is Meta.Sum64: FNV-1a over the bytes of m before its checksum field.
// bbolt calls hash/fnv; the loop is that hash, inlined.
func (m *Meta) sum64() uint64 {
	var h uint64 = 14695981039346656037
	for _, c := range (*[unsafe.Offsetof(Meta{}.checksum)]byte)(unsafe.Pointer(m))[:] {
		h ^= uint64(c)
		h *= 1099511628211
	}
	return h
}

func (m *Meta) validate() bool {
	return m.magic == magic && m.version == version && m.checksum == m.sum64()
}

// write is Meta.Write: it sets m's checksum and copies m into the meta page p
// (m.Copy(p.Meta()), which the bbolt fork writes as v := *m; *dest = v).
func (m *Meta) write(p *Page) {
	p.id = Pgid(m.txid % 2)
	p.flags = metaPageFlag
	m.checksum = m.sum64()
	v := *m
	*p.meta() = v
}
