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
# internal/stringslite has no tests; bytes, internal/bytealg and math/big run in full.
# runtime, os, syscall, log, internal/synctest, crypto/internal/rand: built only, not tested. Their
# models are choices (gomodel.Choose/ChooseUint64/ChooseString), whose Go bodies take one value
# (false, 0, ""): os.Args is empty, runtime.Callers writes nothing, log prints nothing, the random
# bytes are zero (so crypto/rand's tests, which check randomness, fail by design), and Gosched does
# not yield; internal/synctest.Run blocks (gomodel.Stuck).
#
# usage: etc/model-tests.sh
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
cd "$ROOT/goose"
go build -o "$OUT/goose" ./cmd/goose
"$OUT/goose" model-overlay -configdir "$ROOT/Perennial/Code" -dir . -tags purego -o "$OUT/ov" \
  strings bytes errors internal/stringslite internal/bytealg math/big
# the choice models, in an overlay of their own (os's model would empty the tests' os.Args)
"$OUT/goose" model-overlay -configdir "$ROOT/Perennial/Code" -dir . -tags purego -o "$OUT/ovc" \
  runtime os syscall log internal/synctest crypto/internal/rand crypto/rand
# go vet does not find the overlay-added internal/gomodel (it changes into the package's directory)
run() { go test -vet=off -timeout 300s -overlay "$OUT/ov/overlay.json" -tags purego,goose "$@"; }
run strings -skip '^(TestSplit|ExampleSplit|TestBuilderGrow|TestBuilderAllocs|TestBuilderGrowSizeclasses|TestReplace|TestBuilderCopyPanic)$'
run errors -skip '^TestIs$'
run bytes internal/stringslite internal/bytealg math/big
go build -overlay "$OUT/ovc/overlay.json" -tags purego,goose \
  runtime os syscall log internal/synctest crypto/internal/rand crypto/rand
echo "model-tests: ok"
