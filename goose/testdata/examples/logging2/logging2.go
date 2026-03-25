package logging2

import (
	"encoding/binary"

	"github.com/goose-lang/primitive/disk"

	"sync"
)

const LOGCOMMIT = uint64(0)
const LOGSTART = uint64(1)
const LOGMAXBLK = uint64(510)
const LOGEND = LOGMAXBLK + LOGSTART

type Log struct {
	logLock   *sync.Mutex // protects on disk log
	memLock   *sync.Mutex // protects in-memory state
	logSz     uint64
	memLog    *[]disk.Block // in-memory log
	memLen    *uint64       // length of in-memory log
	memTxnNxt *uint64       // next in-memory transaction number
	logTxnNxt *uint64       // next log transaction number
}

func (log Log) writeHdr(len uint64) {
	hdr := make([]byte, 4096)
	binary.LittleEndian.PutUint64(hdr, len)
	disk.Write(LOGCOMMIT, hdr)
}

func Init(logSz uint64) Log {
	log := Log{
		logLock:   new(sync.Mutex),
		memLock:   new(sync.Mutex),
		logSz:     logSz,
		memLog:    new([]disk.Block),
		memLen:    new(uint64),
		memTxnNxt: new(uint64),
		logTxnNxt: new(uint64),
	}
	log.writeHdr(0)
	return log
}

func (log Log) readHdr() uint64 {
	hdr := disk.Read(LOGCOMMIT)
	disklen := binary.LittleEndian.Uint64(hdr)
	return disklen
}

func (log Log) readBlocks(len uint64) []disk.Block {
	var blks = make([]disk.Block, 0)
	for i := uint64(0); i < len; i++ {
		blk := disk.Read(LOGSTART + i)
		blks = append(blks, blk)
	}
	return blks
}

func (log Log) Read() []disk.Block {
	log.logLock.Lock()
	disklen := log.readHdr()
	blks := log.readBlocks(disklen)
	log.logLock.Unlock()
	return blks
}

func (log Log) memWrite(l []disk.Block) {
	n := uint64(len(l))
	for i := uint64(0); i < n; i++ {
		*log.memLog = append(*log.memLog, l[i])
	}
}

func (log Log) memAppend(l []disk.Block) (bool, uint64) {
	log.memLock.Lock()
	if *log.memLen+uint64(len(l)) >= log.logSz {
		log.memLock.Unlock()
		return false, uint64(0)
	}
	txn := *log.memTxnNxt
	n := *log.memLen + uint64(len(l))
	*log.memLen = n
	*log.memTxnNxt = *log.memTxnNxt + 1
	log.memLock.Unlock()
	return true, txn
}

// XXX just an atomic read?
func (log Log) readLogTxnNxt() uint64 {
	log.memLock.Lock()
	n := *log.logTxnNxt
	log.memLock.Unlock()
	return n
}

func (log Log) diskAppendWait(txn uint64) {
	for {
		logtxn := log.readLogTxnNxt()
		if txn < logtxn {
			break
		}
		continue
	}
}

func (log Log) Append(l []disk.Block) bool {
	ok, txn := log.memAppend(l)
	if ok {
		log.diskAppendWait(txn)
	}
	return ok
}

func (log Log) writeBlocks(l []disk.Block, pos uint64) {
	n := uint64(len(l))
	for i := uint64(0); i < n; i++ {
		bk := l[i]
		disk.Write(pos+i, bk)
	}
}

func (log Log) diskAppend() {
	log.logLock.Lock()
	disklen := log.readHdr()

	log.memLock.Lock()
	memlen := *log.memLen
	allblks := *log.memLog
	blks := allblks[disklen:]
	memnxt := *log.memTxnNxt
	log.memLock.Unlock()

	log.writeBlocks(blks, disklen)
	log.writeHdr(memlen)

	*log.logTxnNxt = memnxt // XXX updating wo holding lock, atomic write?

	log.logLock.Unlock()
}

func (log Log) Logger() {
	for {
		log.diskAppend()
	}
}
