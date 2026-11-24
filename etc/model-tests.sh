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
#            TestBuilderCopyPanic     its Reset case: Reset's model keeps
#                                     b.addr, so a copy of a reset Builder
#                                     panics in the model
#   errors   TestIs                   its uncomparable target (#13): Is's model
#                                     compares it, which panics in gc (and is
#                                     stuck in GooseLang)
# internal/stringslite has no tests; bytes runs in full.
#
# usage: etc/model-tests.sh
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
cd "$ROOT/goose"
go build -o "$OUT/goose" ./cmd/goose
"$OUT/goose" model-overlay -configdir "$ROOT/Perennial/Code" -dir . -tags purego -o "$OUT/ov" \
  strings bytes errors internal/stringslite
# go vet does not find the overlay-added internal/gomodel (it changes into the package's directory)
run() { go test -vet=off -timeout 300s -overlay "$OUT/ov/overlay.json" -tags purego,goose "$@"; }
run strings -skip '^(TestSplit|ExampleSplit|TestBuilderGrow|TestBuilderAllocs|TestBuilderGrowSizeclasses|TestReplace|TestBuilderCopyPanic)$'
run errors -skip '^TestIs$'
run bytes internal/stringslite
# the left-out tests' other cases
out=$(run strings -run '^TestBuilderCopyPanic$' -v 2>&1 || true)
fails=$(grep -c 'panicked = ' <<<"$out" || true)
if [ "$fails" != 1 ] || ! grep -q 'Reset: panicked = true; want false' <<<"$out"; then
  echo "model-tests: TestBuilderCopyPanic: expected only its Reset case to fail" >&2
  echo "$out" >&2
  exit 1
fi
echo "model-tests: ok"
