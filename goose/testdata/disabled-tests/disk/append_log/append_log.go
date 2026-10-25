// Append-only, sequential, crash-safe log.
//
// The main interesting feature is that the log supports multi-block atomic
// appends, which are implemented by atomically updating an on-disk header with
// the number of valid blocks in the log.
package append_log

import (
	"sync"

	"github.com/tchajed/marshal"

	"github.com/goose-lang/primitive/disk"
)

type Log struct {
	m      *sync.Mutex
	sz     uint64
	diskSz uint64
}

func (log *Log) mkHdr() disk.Block {
	enc := marshal.NewEnc(disk.BlockSize)
	enc.PutInt(log.sz)
	enc.PutInt(log.diskSz)
	return enc.Finish()
}

func (log *Log) writeHdr() {
	disk.Write(0, log.mkHdr())
}

func Init(diskSz uint64) (*Log, bool) {
	if diskSz < 1 {
		return &Log{m: new(sync.Mutex), sz: 0, diskSz: 0}, false
	}
	log := &Log{m: new(sync.Mutex), sz: 0, diskSz: diskSz}
	log.writeHdr()
	return log, true
}

func Open() *Log {
	hdr := disk.Read(0)
	dec := marshal.NewDec(hdr)
	sz := dec.GetInt()
	diskSz := dec.GetInt()
	return &Log{m: new(sync.Mutex), sz: sz, diskSz: diskSz}
}

func (log *Log) get(i uint64) (disk.Block, bool) {
	sz := log.sz
	if i < sz {
		return disk.Read(1 + i), true
	}
	return nil, false
}

func (log *Log) Get(i uint64) (disk.Block, bool) {
	log.m.Lock()
	v, b := log.get(i)
	log.m.Unlock()
	return v, b
}

func writeAll(bks []disk.Block, off uint64) {
	for i, bk := range bks {
		disk.Write(off+uint64(i), bk)
	}
}

func (log *Log) append(bks []disk.Block) bool {
	sz := log.sz
	if uint64(len(bks)) >= log.diskSz-1-sz {
		return false
	}
	writeAll(bks, 1+sz)
	log.sz += uint64(len(bks))
	log.writeHdr()
	return true
}

func (log *Log) Append(bks []disk.Block) bool {
	log.m.Lock()
	b := log.append(bks)
	log.m.Unlock()
	return b
}

func (log *Log) reset() {
	log.sz = 0
	log.writeHdr()
}

func (log *Log) Reset() {
	log.m.Lock()
	log.reset()
	log.m.Unlock()
}
