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
#                                     b in b.addr, so b escapes; and
#                                     internal/bytealg.MakeNoZero's Go body
#                                     allocates exactly the length asked for,
#                                     not gc's size class
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
#   sync     TestMutexMisuse          an Unlock of an unlocked Mutex: fatal's
#                                     model is stuck (gomodel.Stuck, which
#                                     blocks in gc) where Go ends the program
#            TestPool, TestPoolGC, TestPoolRelease
#                                     the GC clearing pools: the model of
#                                     Pool has no GC, its Get may return a
#                                     value Go's GC would have dropped
# internal/stringslite has no tests; bytes, internal/bytealg and internal/sync
# run in full.
# runtime: its model (Frames.Next, a choice: gomodel's Go bodies take one value, so
# its frames are empty: no function, file or line) is spliced into every overlay
# above as a dependency's; runtime's own tests are not run. (runtime.callers is
# not a model: trusted, with the runtime's real stack walk under gc.)
#
# usage: etc/model-tests.sh
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
cd "$ROOT/goose"
go build -o "$OUT/goose" ./cmd/goose
"$OUT/goose" model-overlay -configdir "$ROOT/Perennial/Code" -dir . -tags purego -o "$OUT/ov" \
  strings bytes errors internal/stringslite internal/bytealg internal/sync sync time
# go vet does not find the overlay-added internal/gomodel (it changes into the package's directory)
run() { go test -vet=off -timeout 600s -overlay "$OUT/ov/overlay.json" -tags purego,goose "$@"; }
run strings -skip '^(TestSplit|ExampleSplit|TestBuilderGrow|TestBuilderAllocs|TestBuilderGrowSizeclasses|TestReplace|TestBuilderCopyPanic)$'
run errors -skip '^TestIs$'
run sync -skip '^(TestMutexMisuse|TestPool|TestPoolGC|TestPoolRelease)$'
# the models' own tests (goose/model/overlaytests: Cond.Wait without a signal blocks, ...)
run ./model/overlaytests/
run bytes internal/stringslite internal/bytealg internal/sync
run time -skip '^(TestAfterStop|TestTimerStopStress|TestChan|TestTicker|TestReset|TestTimerModifiedEarlier|TestAdjustTimers|TestTimerGC)$'
echo "model-tests: ok"
