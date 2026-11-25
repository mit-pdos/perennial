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
# runtime, syscall, log: models that are choices (gomodel.Choose/ChooseUint64/ChooseString),
# whose Go bodies take one value (false, 0, ""): Frames.Next's frames are empty (no function,
# file or line), log.Printf/Println print nothing, and prlimit1 neither
# reads nor sets a limit. Run with their overlay (every package above runs with runtime's too):
#   syscall  TestPrlimitFileLimit     prlimit1's model leaves the limit unchanged
#   log      TestAll                  Printf/Println's model prints nothing
#            TestCallDepth, ExampleLogger, ExampleLogger_Output
#                                     the file and line of Lshortfile come from
#                                     Frames.Next's model (empty)
#            TestFlagAndPrefixSetting, TestUTCFlag, TestOutput
#                                     a Logger's Print (Println) formats through
#                                     fmt.Append (Appendln), whose model
#                                     (pp.doPrint, pp.doPrintln; the overlay
#                                     includes log's dependencies' models)
#                                     prints an empty string in gc
#   os       TestReadAtNegativeOffset, TestWriteAtNegativeOffset (fmt.Sprint of the error),
#            TestExecutable, TestGetppid (the child prints with fmt.Print), Example*
#            (their output is fmt.Print*'s; testing reports them with fmt too), TestStatStdin
#            (the child prints with fmt.Println): fmt's models, included as os's
#            dependency's, print an empty string in gc; TestChown, TestFileChown,
#            TestLchown (t.Log of a []int: testing formats it with fmt.Sprintln, whose
#            model, pp.doPrintln, is stuck on a []int and blocks in gc)
#   sort     Example* (fmt.Print* output; one hangs where fmt's model is stuck)
#   runtime/debug TestSetCrashOutput (the child's output is fmt's)
# runtime's own tests are not run. (os.runtime_args, syscall.runtime_envs, runtime.callers and
# internal/synctest are not models: trusted, with the runtime's real bodies under gc.)
#   fmt      only TestModelAlias (goose/model/fmt/testdata/alias): its models
#            (errorf, Fprintf, pp.doPrint, pp.doPrintln; Printf runs Fprintf) print an empty string where
#            the model printer's output is arbitrary (gomodel's Go bodies
#            choose 0) and block where it is stuck, so fmt's own tests of
#            Errorf, Fprint(f/ln), Printf and Sprint(ln) fail by design (and time
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
  strings bytes errors internal/stringslite internal/bytealg internal/sync sync time
# the choice models, in an overlay of their own
"$OUT/goose" model-overlay -configdir "$ROOT/Perennial/Code" -dir . -tags purego -o "$OUT/ovc" \
  runtime syscall log
# go vet does not find the overlay-added internal/gomodel (it changes into the package's directory)
run() { go test -vet=off -timeout 600s -overlay "$OUT/ov/overlay.json" -tags purego,goose "$@"; }
run strings -skip '^(TestSplit|ExampleSplit|TestBuilderGrow|TestBuilderAllocs|TestBuilderGrowSizeclasses|TestReplace|TestBuilderCopyPanic)$'
run errors -skip '^TestIs$'
run sync -skip '^(TestMutexMisuse|TestPool|TestPoolGC|TestPoolRelease)$'
# the models' own tests (goose/model/overlaytests: Cond.Wait without a signal blocks, ...)
run ./model/overlaytests/
run bytes internal/stringslite internal/bytealg internal/sync
run time -skip '^(TestAfterStop|TestTimerStopStress|TestChan|TestTicker|TestReset|TestTimerModifiedEarlier|TestAdjustTimers|TestTimerGC)$'
runc() { go test -vet=off -timeout 600s -overlay "$OUT/ovc/overlay.json" -tags purego,goose "$@"; }
runc syscall -skip '^TestPrlimitFileLimit$'
runc log -skip '^(TestAll|TestCallDepth|ExampleLogger|ExampleLogger_Output|TestFlagAndPrefixSetting|TestUTCFlag|TestOutput)$'
runc os -skip '^(TestReadAtNegativeOffset|TestWriteAtNegativeOffset|TestExecutable|TestGetppid|TestStatStdin|TestChown|TestFileChown|TestLchown|Example.*)$'
runc sort -skip '^Example.*$'
runcdebug() { runc runtime/debug -skip '^TestSetCrashOutput$'; }
runcdebug
go build -overlay "$OUT/ovc/overlay.json" -tags purego,goose runtime internal/synctest
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
# fmt's models only: the overlay also splices the models of fmt's dependencies (sync.Pool's and
# internal/sync's consume gomodel choices too), which this test leaves real
m = {k: v for k, v in m.items()
     if k.startswith(src + "/fmt/") or k.startswith(src + "/internal/gomodel/")}
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
