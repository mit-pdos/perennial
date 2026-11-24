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
#   fmt      only TestModelAlias (goose/model/fmt/testdata/alias): its models
#            (errorf, Fprintf, Printf, pp.doPrint) print an empty string where
#            the model printer's output is arbitrary (gomodel's Go bodies
#            choose 0) and block where it is stuck, so fmt's own tests of
#            Errorf, Fprint(f), Printf and Sprint fail by design (and time
#            out). The model's evidence is the differential tests of
#            goose/model/fmt (go test ./model/fmt, run by go test
#            ./goose/...), which compare it with the real fmt, and
#            TestModelAlias, run here on the real fmt and on the models with
#            gomodel's choices driven (testdata/alias/gomodel_driven.go): the
#            printer's buffer seen through a slice a writer kept.
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
# go vet does not find the overlay-added internal/gomodel (it changes into the package's directory)
run() { go test -vet=off -timeout 300s -overlay "$OUT/ov/overlay.json" -tags purego,goose "$@"; }
run strings -skip '^(TestSplit|ExampleSplit|TestBuilderGrow|TestBuilderAllocs|TestBuilderGrowSizeclasses|TestReplace|TestBuilderCopyPanic)$'
run errors -skip '^TestIs$'
run bytes internal/stringslite internal/bytealg
# fmt: TestModelAlias, on the real fmt, then on its models with the driven gomodel
"$OUT/goose" model-overlay -configdir "$ROOT/Perennial/Code" -dir . -tags purego -o "$OUT/ovfmt" fmt
ALIAS="$ROOT/goose/model/fmt/testdata/alias"
python3 - "$(go env GOROOT)/src" "$ALIAS" "$OUT/ovfmt/overlay.json" "$OUT" <<'PY'
import json, sys
src, alias, ov, out = sys.argv[1:]
tests = {src + "/fmt/zz_alias_test.go": alias + "/alias_test.go",
         src + "/fmt/zz_alias_goose_test.go": alias + "/alias_goose_test.go"}
json.dump({"Replace": tests}, open(out + "/alias-real.json", "w"))
m = json.load(open(ov))["Replace"]
gm = src + "/internal/gomodel/zz_gomodel_gomodel.go"
assert gm in m, gm
m[gm] = alias + "/gomodel_driven.go"
m.update(tests)
json.dump({"Replace": m}, open(out + "/alias-model.json", "w"))
PY
go test -vet=off -timeout 300s -overlay "$OUT/alias-real.json" -run '^TestModelAlias$' fmt
run_alias() { go test -vet=off -timeout 300s -overlay "$OUT/alias-model.json" -tags purego,goose -run '^TestModelAlias$' fmt; }
run_alias
echo "model-tests: ok"
