#!/usr/bin/env bash
# Runs the standard library's own tests of each package that has a Go model
# overlay (goose/model/overlay/<pkg>, the [model] table of
# Perennial/Code/<pkg>.toml) against the package with its models spliced in:
# evidence that each model has the real package's behaviour where the tests
# reach it. Needs the pinned go (etc/update-goose-new.py's GO_VERSION) first on
# PATH, with GOTOOLCHAIN=local: go1.26.0 does not find the overlay-added
# internal/gomodel.
#
# The tests left out are the ones a model fails by design (each MODEL: comment
# says why):
#   strings  TestSplit, ExampleSplit  an empty separator: Split's model is stuck
#                                     there (gomodel.Stuck, which blocks in gc)
#            TestBuilderGrow, TestBuilderAllocs, TestBuilderGrowSizeclasses,
#            TestReplace              allocation counts: Builder.String's model
#                                     copies the buffer, and copyCheck's stores
#                                     b in b.addr, so b escapes
#            TestBuilderCopyPanic     copyCheck's model is stuck (gomodel.Stuck,
#                                     which blocks in gc) where Go's check
#                                     fails, and Reset's model keeps b.addr
#   errors   TestIs                   its uncomparable target (#13): Is's model
#                                     compares it, which panics in gc (and is
#                                     stuck in GooseLang)
# internal/stringslite has no tests; bytes and internal/bytealg run in full.
# runtime, syscall, log: models that are choices (gomodel.Choose/ChooseUint64/ChooseString),
# whose Go bodies take one value (false, 0, ""): Frames.Next's frames are empty (no function,
# file or line), Gosched does not yield, log.Printf/Println print nothing, and prlimit1 neither
# reads nor sets a limit. Run with their overlay (every package above runs with runtime's too):
#   syscall  TestPrlimitFileLimit     prlimit1's model leaves the limit unchanged
#   log      TestAll                  Printf/Println's model prints nothing
#            TestCallDepth, ExampleLogger, ExampleLogger_Output
#                                     the file and line of Lshortfile come from
#                                     Frames.Next's model (empty)
#   os, sort, runtime/debug           in full
# runtime's own tests are not run. (os.runtime_args, syscall.runtime_envs, runtime.callers and
# internal/synctest are not models: trusted, with the runtime's real bodies under gc.)
#
# usage: etc/model-tests.sh
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
cd "$ROOT/goose"
go build -o "$OUT/goose" ./cmd/goose
"$OUT/goose" model-overlay -configdir "$ROOT/Perennial/Code" -dir . -tags purego -o "$OUT/ov" \
  strings bytes errors internal/stringslite internal/bytealg
# the choice models, in an overlay of their own
"$OUT/goose" model-overlay -configdir "$ROOT/Perennial/Code" -dir . -tags purego -o "$OUT/ovc" \
  runtime syscall log
# go vet does not find the overlay-added internal/gomodel (it changes into the package's directory)
run() { go test -vet=off -timeout 300s -overlay "$OUT/ov/overlay.json" -tags purego,goose "$@"; }
run strings -skip '^(TestSplit|ExampleSplit|TestBuilderGrow|TestBuilderAllocs|TestBuilderGrowSizeclasses|TestReplace|TestBuilderCopyPanic)$'
run errors -skip '^TestIs$'
run bytes internal/stringslite internal/bytealg
runc() { go test -vet=off -timeout 300s -overlay "$OUT/ovc/overlay.json" -tags purego,goose "$@"; }
runc syscall -skip '^TestPrlimitFileLimit$'
runc log -skip '^(TestAll|TestCallDepth|ExampleLogger|ExampleLogger_Output)$'
runc os sort runtime/debug
go build -overlay "$OUT/ovc/overlay.json" -tags purego,goose runtime internal/synctest
echo "model-tests: ok"
