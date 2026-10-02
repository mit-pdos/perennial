package unittest

import "github.com/goose-lang/primitive/disk"

type diskWrapper struct {
	d disk.Disk
}

func diskArgument(d disk.Disk) {
	b := d.Read(0)
	d.Write(1, b)
}
