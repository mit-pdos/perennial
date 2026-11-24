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
#   time     TestAfterStop, TestTimerStopStress, TestChan, TestTicker,
#            TestReset, TestTimerModifiedEarlier, TestAdjustTimers
#                                     Stop and Reset: their models do not
#                                     cancel the firings already armed (each
#                                     is a schedule of Go's in which Stop or
#                                     Reset came later), so stopped timers
#                                     fire, reset tickers keep their old
#                                     period, and a reset timer's old firing
#                                     blocks on its unbuffered channel (the
#                                     last three hang)
#            TestTimerGC              allocation counts: a model timer's
#                                     goroutine keeps it alive until it fires
# internal/stringslite has no tests; bytes and internal/bytealg run in full.
#
# usage: etc/model-tests.sh
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
cd "$ROOT/goose"
go build -o "$OUT/goose" ./cmd/goose
"$OUT/goose" model-overlay -configdir "$ROOT/Perennial/Code" -dir . -tags purego -o "$OUT/ov" \
  strings bytes errors internal/stringslite internal/bytealg time
# go vet does not find the overlay-added internal/gomodel (it changes into the package's directory)
run() { go test -vet=off -timeout 300s -overlay "$OUT/ov/overlay.json" -tags purego,goose "$@"; }
run strings -skip '^(TestSplit|ExampleSplit|TestBuilderGrow|TestBuilderAllocs|TestBuilderGrowSizeclasses|TestReplace|TestBuilderCopyPanic)$'
run errors -skip '^TestIs$'
run bytes internal/stringslite internal/bytealg
run time -skip '^(TestAfterStop|TestTimerStopStress|TestChan|TestTicker|TestReset|TestTimerModifiedEarlier|TestAdjustTimers|TestTimerGC)$'
echo "model-tests: ok"
