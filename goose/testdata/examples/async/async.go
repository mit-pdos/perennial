// async just uses the async disk FFI
package async

import "github.com/goose-lang/primitive/async_disk"

func TakesDisk(d async_disk.Disk) {}

func UseDisk(d async_disk.Disk) {
	v := make([]byte, 4096)
	d.Write(0, v)
	d.Barrier()
}
