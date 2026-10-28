package bboltmini

import "unsafe"

const bucketHeaderSize = int(unsafe.Sizeof(InBucket{}))

func cloneBytes(v []byte) []byte {
	clone := make([]byte, len(v))
	copy(clone, v)
	return clone
}

// writeInlineBucket is Bucket.write: an inline bucket's value is its InBucket
// header followed by a leaf page holding its contents.
func writeInlineBucket(b *InBucket, inodes []inode) []byte {
	value := make([]byte, bucketHeaderSize+pageSize(inodes))
	bucket := (*InBucket)(unsafe.Pointer(&value[0]))
	ib := *b
	*bucket = ib
	p := (*Page)(unsafe.Pointer(&value[bucketHeaderSize]))
	p.flags = leafPageFlag
	p.count = uint16(len(inodes))
	writeInodeToPage(inodes, p)
	return value
}

// openInlineBucket is openBucket. value is wherever the inline bucket's bytes
// are, possibly at an unaligned offset of a page; an unaligned value is
// copied first. A writable bucket gets its own copy of the header.
func openInlineBucket(value []byte, writable bool) (*InBucket, *Page) {
	const unalignedMask = unsafe.Alignof(struct {
		InBucket
		Page
	}{}) - 1
	unaligned := uintptr(unsafe.Pointer(&value[0]))&unalignedMask != 0
	if unaligned {
		value = cloneBytes(value)
	}
	var b *InBucket
	if writable && !unaligned {
		b = &InBucket{}
		ib := *(*InBucket)(unsafe.Pointer(&value[0]))
		*b = ib
	} else {
		b = (*InBucket)(unsafe.Pointer(&value[0]))
	}
	return b, (*Page)(unsafe.Pointer(&value[bucketHeaderSize]))
}
