# Disabled: goose tests that use the disk FFI

The disk FFI (`github.com/goose-lang/primitive/disk`, Perennial's
`GooseLang/Ffi/DiskFfi`) was removed until FFIs are redesigned. These tests
used it and are kept here, unchanged, for when an FFI for disks exists again:

- `append_log`, `logging2`, `wal`: examples (with their gold files as of the
  removal);
- `semantics/wal.go`: the semantics tests that wrote to a disk (package
  `semantics`, from `testdata/examples/semantics`);
- `unittest/disk.go`, `unittest/replicated_disk.go`: from
  `testdata/examples/unittest`;
- `use_disk`: the package of `cmd/goose`'s integration test that checked FFI
  detection.
