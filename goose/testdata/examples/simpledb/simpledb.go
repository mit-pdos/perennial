/*
Package simpledb implements a one-table version of LevelDB

It buffers all writes in memory; to make data durable, call Compact().
This operation re-writes all of the data in the database
(including in-memory writes) in a crash-safe manner.
Keys in the table are cached for efficient reads.
*/
package simpledb

import (
	"encoding/binary"
	"sync"

	"github.com/goose-lang/primitive/filesys"

	"github.com/tchajed/marshal" // to test these imports
)

func UseMarshal() {
	marshal.NewEnc(0)
}

// A Table provides access to an immutable copy of data on the filesystem,
// along with an index for fast random access.
type Table struct {
	Index map[uint64]uint64
	File  filesys.File
}

// CreateTable creates a new, empty table.
func CreateTable(p string) Table {
	index := make(map[uint64]uint64)
	f, _ := filesys.Create("db", p)
	filesys.Close(f)
	f2 := filesys.Open("db", p)
	return Table{Index: index, File: f2}
}

// Entry represents a (key, value) pair.
type Entry struct {
	Key   uint64
	Value []byte
}

// DecodeUInt64 is a Decoder(uint64)
//
// All decoders have the shape func(p []byte) (T, uint64)
//
// The uint64 represents the number of bytes consumed; if 0,
// then decoding failed, and the value of type T should be ignored.
func DecodeUInt64(p []byte) (uint64, uint64) {
	if len(p) < 8 {
		return 0, 0
	}
	n := binary.LittleEndian.Uint64(p)
	return n, 8
}

// DecodeEntry is a Decoder(Entry)
func DecodeEntry(data []byte) (Entry, uint64) {
	key, l1 := DecodeUInt64(data)
	if l1 == 0 {
		return Entry{Key: 0, Value: nil}, 0
	}
	valueLen, l2 := DecodeUInt64(data[l1:])
	if l2 == 0 {
		return Entry{Key: 0, Value: nil}, 0
	}
	if uint64(len(data)) < l1+l2+valueLen {
		return Entry{Key: 0, Value: nil}, 0
	}
	value := data[l1+l2 : l1+l2+valueLen]
	return Entry{
		Key:   key,
		Value: value,
	}, l1 + l2 + valueLen
}

type lazyFileBuf struct {
	offset uint64
	next   []byte
}

// readTableIndex parses a complete table on disk into a key->offset index
func readTableIndex(f filesys.File, index map[uint64]uint64) {
	for buf := (lazyFileBuf{offset: 0, next: nil}); ; {
		e, l := DecodeEntry(buf.next)
		if l > 0 {
			index[e.Key] = 8 + buf.offset
			buf = lazyFileBuf{offset: buf.offset + l, next: buf.next[l:]}
			continue
		} else {
			p := filesys.ReadAt(f,
				buf.offset+uint64(len(buf.next)), 4096)
			if len(p) == 0 {
				break
			} else {
				newBuf := append(buf.next, p...)
				buf = lazyFileBuf{
					offset: buf.offset,
					next:   newBuf,
				}
				continue
			}
		}
	}
}

// RecoverTable restores a table from disk on startup.
func RecoverTable(p string) Table {
	index := make(map[uint64]uint64)
	f := filesys.Open("db", p)
	readTableIndex(f, index)
	return Table{Index: index, File: f}
}

// CloseTable frees up the fd held by a table.
func CloseTable(t Table) {
	filesys.Close(t.File)
}

func readValue(f filesys.File, off uint64) []byte {
	startBuf := filesys.ReadAt(f, off, 512)
	totalBytes := binary.LittleEndian.Uint64(startBuf)
	// should have enough data for the key if the file is a proper encoding
	buf := startBuf[8:]
	haveBytes := uint64(len(buf))
	if haveBytes < totalBytes {
		buf2 := filesys.ReadAt(f, off+512, totalBytes-haveBytes)
		newBuf := append(buf, buf2...)
		return newBuf
	}
	return buf[:totalBytes]
}

func tableRead(t Table, k uint64) ([]byte, bool) {
	off, ok := t.Index[k]
	if !ok {
		return nil, false
	}
	p := readValue(t.File, off)
	return p, true
}

type bufFile struct {
	file filesys.File
	buf  *[]byte
}

func newBuf(f filesys.File) bufFile {
	buf := new([]byte)
	return bufFile{
		file: f,
		buf:  buf,
	}
}

func bufFlush(f bufFile) {
	buf := *f.buf
	if len(buf) == 0 {
		return
	}
	filesys.Append(f.file, buf)
	*f.buf = nil
}

func bufAppend(f bufFile, p []byte) {
	buf := *f.buf
	buf2 := append(buf, p...)
	*f.buf = buf2
}

func bufClose(f bufFile) {
	bufFlush(f)
	filesys.Close(f.file)
}

type tableWriter struct {
	index  map[uint64]uint64
	name   string
	file   bufFile
	offset *uint64
}

func newTableWriter(p string) tableWriter {
	index := make(map[uint64]uint64)
	f, _ := filesys.Create("db", p)
	buf := newBuf(f)
	off := new(uint64)
	return tableWriter{
		index:  index,
		name:   p,
		file:   buf,
		offset: off,
	}
}

func tableWriterAppend(w tableWriter, p []byte) {
	bufAppend(w.file, p)
	off := *w.offset
	*w.offset = off + uint64(len(p))
}

func tableWriterClose(w tableWriter) Table {
	bufClose(w.file)
	f := filesys.Open("db", w.name)
	return Table{
		Index: w.index,
		File:  f,
	}
}

// EncodeUInt64 is an Encoder(uint64)
func EncodeUInt64(x uint64, p []byte) []byte {
	tmp := make([]byte, 8)
	binary.LittleEndian.PutUint64(tmp, x)
	p2 := append(p, tmp...)
	return p2
}

// EncodeSlice is an Encoder([]byte)
func EncodeSlice(data []byte, p []byte) []byte {
	p2 := EncodeUInt64(uint64(len(data)), p)
	p3 := append(p2, data...)
	return p3
}

func tablePut(w tableWriter, k uint64, v []byte) {
	tmp := make([]byte, 0)
	tmp2 := EncodeUInt64(k, tmp)
	tmp3 := EncodeSlice(v, tmp2)

	off := *w.offset
	// index points to encoded value
	w.index[k] = off + uint64(len(tmp2))

	// write to table
	tableWriterAppend(w, tmp3)
}

// Database is a handle to an open database.
type Database struct {
	wbuffer *map[uint64][]byte
	rbuffer *map[uint64][]byte
	bufferL *sync.Mutex
	table   *Table
	// the manifest
	tableName *string
	// protects both table and tableName
	tableL *sync.Mutex
	// protects constructing shadow tables
	compactionL *sync.Mutex
}

func makeValueBuffer() *map[uint64][]byte {
	buf := make(map[uint64][]byte)
	bufPtr := new(map[uint64][]byte)
	*bufPtr = buf
	return bufPtr
}

// NewDb initializes a new database on top of an empty filesys.
func NewDb() Database {
	wbuf := makeValueBuffer()
	rbuf := makeValueBuffer()
	bufferL := new(sync.Mutex)
	tableName := "table.0"
	tableNameRef := new(string)
	*tableNameRef = tableName
	table := CreateTable(tableName)
	tableRef := new(Table)
	*tableRef = table
	tableL := new(sync.Mutex)
	compactionL := new(sync.Mutex)
	return Database{
		wbuffer:     wbuf,
		rbuffer:     rbuf,
		bufferL:     bufferL,
		table:       tableRef,
		tableName:   tableNameRef,
		tableL:      tableL,
		compactionL: compactionL,
	}
}

// Read gets a key from the database.
//
// Returns a boolean indicating if the k was found and a non-nil slice with
// the value if k was in the database.
//
// Reflects any completed in-memory writes.
func Read(db Database, k uint64) ([]byte, bool) {
	// NOTE: these should be read-only locks,
	//  but we've dropped support for them in goose
	db.bufferL.Lock()
	// first try write buffer
	buf := *db.wbuffer
	v, ok := buf[k]
	if ok {
		db.bufferL.Unlock()
		return v, true
	}
	// ...then try read buffer
	rbuf := *db.rbuffer
	v2, ok := rbuf[k]
	if ok {
		db.bufferL.Unlock()
		return v2, true
	}
	// ...and finally go to the table
	db.tableL.Lock()
	tbl := *db.table
	v3, ok := tableRead(tbl, k)
	db.tableL.Unlock()
	db.bufferL.Unlock()
	return v3, ok
}

// Write sets a key to a new value.
//
// Creates a new key-value mapping if k is not in the database and overwrites
// the previous value if k is present.
//
// The new value is buffered in memory. To persist it, call db.Compact().
func Write(db Database, k uint64, v []byte) {
	db.bufferL.Lock()
	buf := *db.wbuffer
	buf[k] = v
	db.bufferL.Unlock()
}

func freshTable(p string) string {
	if p == "table.0" {
		return "table.1"
	}
	if p == "table.1" {
		return "table.0"
	}
	// note that this only works if we guarantee the table is always
	// either table.0 or table.1
	return p
}

func tablePutBuffer(w tableWriter, buf map[uint64][]byte) {
	for k, v := range buf {
		tablePut(w, k, v)
	}
}

// add all of table t to the table w being created; skip any keys in the (read)
// buffer b since those writes overwrite old ones
func tablePutOldTable(w tableWriter, t Table, b map[uint64][]byte) {
	for buf := (lazyFileBuf{offset: 0, next: nil}); ; {
		e, l := DecodeEntry(buf.next)
		if l > 0 {
			_, ok := b[e.Key]
			// only copy the key if it wasn't overwritten in the buffer
			// (this compacts overall storage when keys are overwritten)
			if !ok {
				tablePut(w, e.Key, e.Value)
			}
			buf = lazyFileBuf{offset: buf.offset + l, next: buf.next[l:]}
			continue
		} else {
			p := filesys.ReadAt(t.File,
				buf.offset+uint64(len(buf.next)), 4096)
			if len(p) == 0 {
				break
			} else {
				newBuf := append(buf.next, p...)
				buf = lazyFileBuf{
					offset: buf.offset,
					next:   newBuf,
				}
				continue
			}
		}
	}
}

// Build a new shadow table that incorporates the current table and a
// (write) buffer wbuf.
//
// Assumes all the appropriate locks have been taken.
//
// Returns the old table and new table.
func constructNewTable(db Database, wbuf map[uint64][]byte) (Table, Table) {
	oldName := *db.tableName
	name := freshTable(oldName)
	w := newTableWriter(name)
	oldTable := *db.table
	// add old writes (using the buffer to skip new writes)
	tablePutOldTable(w, oldTable, wbuf)
	// add buffered writes
	tablePutBuffer(w, wbuf)
	newTable := tableWriterClose(w)
	return oldTable, newTable
}

// Compact persists in-memory writes to a new table.
//
// This simple database design must re-write all data to combine in-memory
// writes with existing writes.
func Compact(db Database) {
	db.compactionL.Lock()

	// first, snapshot the buffered writes that will go into this table.
	db.bufferL.Lock()
	buf := *db.wbuffer
	emptyWbuffer := make(map[uint64][]byte)
	*db.wbuffer = emptyWbuffer
	*db.rbuffer = buf
	db.bufferL.Unlock()

	// next, construct the new table
	// NOTE: it's weird to acquire this table lock:
	//
	//	- what happens between tableL.RUnlock() and tableL.Lock()? a reader
	// would be fine since the old table is still valid, and the compaction
	// log prevents another writer from suddenly installing a new table
	//
	// - given this reasoning, why lock the tableL at all? it feels like the
	// compactionL also implicitly acquires a read-lock on the tableL, since it
	// guarantees only the compaction itself could be messing with the table,
	// which it won't do till later in this function
	//
	// NOTE: this doesn't come up now that we've dropped sync.RWMutex support
	db.tableL.Lock()
	oldTableName := *db.tableName
	oldTable, t := constructNewTable(db, buf)
	newTable := freshTable(oldTableName)
	// db.tableL.RUnlock()

	// next, install it (persistently and in-memory)
	// db.tableL.Lock()
	*db.table = t
	*db.tableName = newTable
	manifestData := []byte(newTable)
	filesys.AtomicCreate("db", "manifest", manifestData)
	CloseTable(oldTable)
	filesys.Delete("db", oldTableName)
	// note that we don't need to remove the rbuffer (it's just a cache for
	// the part of the table we just persisted)
	db.tableL.Unlock()

	db.compactionL.Unlock()
}

func recoverManifest() string {
	f := filesys.Open("db", "manifest")
	// need to know that table names are less than 4096 bytes
	// (eventually we'll probably restrict ReadAt to read at most 4096 bytes
	//  at a time due to it being atomic,
	//  so checking the size of the file won't help,
	//  and there's really no need for a loop here)
	manifestData := filesys.ReadAt(f, 0, 4096)
	tableName := string(manifestData)
	filesys.Close(f)
	return tableName
}

// delete 'name' if it isn't tableName or "manifest"
func deleteOtherFile(name string, tableName string) {
	if name == tableName {
		return
	}
	if name == "manifest" {
		return
	}
	filesys.Delete("db", name)
}

func deleteOtherFiles(tableName string) {
	files := filesys.List("db")
	nfiles := uint64(len(files))
	for i := uint64(0); ; {
		if i == nfiles {
			break
		}
		name := files[i]
		deleteOtherFile(name, tableName)
		i = i + 1
		continue
	}
}

// Recover restores a previously created database after a crash or shutdown.
func Recover() Database {
	tableName := recoverManifest()
	table := RecoverTable(tableName)
	tableRef := new(Table)
	*tableRef = table
	tableNameRef := new(string)
	*tableNameRef = tableName

	deleteOtherFiles(tableName)

	wbuffer := makeValueBuffer()
	rbuffer := makeValueBuffer()
	bufferL := new(sync.Mutex)
	tableL := new(sync.Mutex)
	compactionL := new(sync.Mutex)

	return Database{
		wbuffer:     wbuffer,
		rbuffer:     rbuffer,
		bufferL:     bufferL,
		table:       tableRef,
		tableName:   tableNameRef,
		tableL:      tableL,
		compactionL: compactionL,
	}
}

// Shutdown immediately closes the database.
//
// Discards any uncommitted in-memory writes; similar to a crash except for
// cleanly closing any open files.
func Shutdown(db Database) {
	db.bufferL.Lock()
	db.compactionL.Lock()

	t := *db.table
	CloseTable(t)

	db.compactionL.Unlock()
	db.bufferL.Unlock()
}

// Close closes an open database cleanly, flushing any in-memory writes.
//
// db should not be used afterward
func Close(db Database) {
	Compact(db)
	Shutdown(db)
}
