# gokv's grove_ffi, vendored

`grove_ffi/` is `github.com/mit-pdos/gokv/grove_ffi` of gokv v0.1.1 with one change:
`FileRead` returns `[]byte{}` (non-nil, empty) when `os.ReadFile` fails, where v0.1.1 returned
`ioutil.ReadFile`'s result (nil, or a prefix of the file) and ignored the error. A missing
file thus reads as an empty slice, which Perennial's model of `FileRead` gives
(`IsGroveStep` "FileRead", `Perennial/GooseLang/Ext/Grove/Impl.lean`). The module keeps
gokv's import path; `goose/testdata/examples` and `goose/testdata/goose-tests` use it with a
`replace` directive, and `etc/update-goose-new.py` translates it.
