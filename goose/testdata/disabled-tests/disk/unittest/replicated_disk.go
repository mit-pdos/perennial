package unittest

type Block struct {
	Value uint64
}

const Disk1 uint64 = 0
const Disk2 uint64 = 0
const DiskSize uint64 = 1000

// TwoDiskWrite is a dummy function to represent the base layer's disk write
func TwoDiskWrite(diskId uint64, a uint64, v Block) bool {
	return true
}

// TwoDiskRead is a dummy function to represent the base layer's disk read
func TwoDiskRead(diskId uint64, a uint64) (Block, bool) {
	return Block{Value: 0}, true
}

// TwoDiskLock is a dummy function to represent locking an address in the
// base layer
func TwoDiskLock(a uint64) {}

// TwoDiskUnlock is a dummy function to represent unlocking an address in the
// base layer
func TwoDiskUnlock(a uint64) {}

func ReplicatedDiskRead(a uint64) Block {
	TwoDiskLock(a)
	v, ok := TwoDiskRead(Disk1, a)
	if ok {
		TwoDiskUnlock(a)
		return v
	}
	v2, _ := TwoDiskRead(Disk2, a)
	// we assume both disks cannot fail
	TwoDiskUnlock(a)
	return v2
}

func ReplicatedDiskWrite(a uint64, v Block) {
	TwoDiskLock(a)
	TwoDiskWrite(Disk1, a, v)
	TwoDiskWrite(Disk2, a, v)
	TwoDiskUnlock(a)
}

func ReplicatedDiskRecover() {
	for a := uint64(0); ; {
		if a > DiskSize {
			break
		}
		v, ok := TwoDiskRead(Disk1, a)
		if ok {
			TwoDiskWrite(Disk2, a, v)
		}
		a = a + 1
		continue
	}
}
