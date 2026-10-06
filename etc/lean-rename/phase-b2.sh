#!/usr/bin/env bash
# Phase B2 of the Lean rename: Rocq-style name encodings of generated code
# («Xⁱᵐᵖˡ» -> X.impl / X.underlying, «T__Mⁱᵐᵖˡ» -> T.M.impl, X'fds -> X.fields,
# X'init -> X.init, X_Assumptions -> X.TypeAssumptions).
# Usage: etc/lean-rename/phase-b2.sh INVENTORY ILEAN_DIR
# Run from a clean, fully built tree (with a copy of its .ilean files).
set -eu
cd "$(dirname "$0")/../.."
R=etc/lean-rename
INV=$1; ILEAN=$2
before=$(wc -l < $R/renames.tsv)
python3 $R/rename.py "$INV" --ilean "$ILEAN" --include-generated --encodings --apply
tail -n +$((before + 1)) $R/renames.tsv > /tmp/lean-renames-b2.$$
python3 $R/qualified.py /tmp/lean-renames-b2.$$
# wp_auto/wp_func_call recognize implementation constants by name
python3 - <<'EOF'
p = "Perennial/Golang/Theory/ProofMode.lean"
s = open(p, encoding="utf-8").read()
old = '''      -- `onlyImpl`: only implementation constants `«Fooⁱᵐᵖˡ»` (as produced by
      -- `wp_func_call`/`wp_method_call`)
      if onlyImpl then
        let some n := (← instantiateMVars fv).getAppFn.constName? | throwError "not a constant"
        unless (n.toString.endsWith "ⁱᵐᵖˡ") || (n.toString.endsWith "ⁱᵐᵖˡ»") do
          throwError "not an implementation constant"'''
new = '''      -- `onlyImpl`: only implementation constants `Foo.impl`/`T.M.impl` (as produced by
      -- `wp_func_call`/`wp_method_call`)
      if onlyImpl then
        let some n := (← instantiateMVars fv).getAppFn.constName? | throwError "not a constant"
        unless n matches .str _ "impl" do
          throwError "not an implementation constant"'''
assert s.count(old) == 1
s = s.replace(old, new)
s = s.replace("(e.g. a generated `«Fooⁱᵐᵖˡ»` constant)", "(e.g. a generated `Foo.impl` constant)")
open(p, "w", encoding="utf-8").write(s)
p = "Perennial/Golang/Theory/Test.lean"
s = open(p, encoding="utf-8").read()
s = s.replace("implementation constant `«Fooⁱᵐᵖˡ»`", "implementation constant `Foo.impl`")
open(p, "w", encoding="utf-8").write(s)
EOF
rm -f /tmp/lean-renames-b2.$$
