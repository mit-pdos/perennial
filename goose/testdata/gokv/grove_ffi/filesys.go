package grove_ffi

import (
	"fmt"
	"io/ioutil"
	"log"
	"os"
	"path/filepath"
)

// filesystem+network library
const DataDir = "durable"

func panic_if_err(err error) {
	if err != nil {
		log.Fatal(err)
	}
}

// crash-atomically writes content to the file with name filename
func FileWrite(filename string, content []byte) {
	_ = os.Mkdir("tmp", 0755)
	tmpfile, err := ioutil.TempFile("tmp", filename+"_*")
	panic_if_err(err)
	// defer tmpfile.Close()
	defer os.Remove(tmpfile.Name())

	for i := 0; i < len(content); {
		bytesWritten, err := tmpfile.Write(content[i:])
		panic_if_err(err)
		i += bytesWritten
	}
	err = tmpfile.Sync()
	panic_if_err(err)

	_ = os.Mkdir(DataDir, 0755)
	panic_if_err(os.Rename(tmpfile.Name(), filepath.Join(DataDir, filename)))
	// FIXME: how to make sure the os.Rename completes?
}

// reads the contents of the file filename; an empty slice if it cannot be read
func FileRead(filename string) []byte {
	content, err := os.ReadFile(filepath.Join(DataDir, filename))
	if err != nil {
		return []byte{}
	}
	return content
}

func FileAppend(filename string, data []byte) {
	filename = filepath.Join(DataDir, filename)
	f, err := os.OpenFile(filename, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0666)
	if err != nil {
		panic(err)
	}
	f.Write(data)
	err = f.Sync()
	panic_if_err(err)
	// time.Sleep(10 * time.Millisecond)
	err = f.Close()
	if err != nil {
		panic(err)
	}
}

// injective function u64 -> str
func U64ToString(i uint64) string {
	return fmt.Sprint(i)
}
