#!/usr/bin/env bash
set -euo pipefail

supplement_dir="peony-code"
out=$(mktemp -d -t peony-code)
src=$(mktemp -d -t perennial-clean)
dst="$out/$supplement_dir"
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
PERENNIAL="$SCRIPT_DIR/../.."

GREP="grep"
if which ggrep 1>/dev/null; then
    GREP="ggrep"
fi

SED="sed"
if which gsed 1>/dev/null; then
    SED="gsed"
fi

copy() {
    top_dir="$1"
    shift
    for file in "$@"; do
        dir=$(dirname "$file")
        mkdir -p "$dst/$top_dir/$dir"
        cp -r "$src/$file" "$dst/$top_dir/$dir/"
    done
}

cp -r "$PERENNIAL/" "$src"
cd "$src"
git clean -fxd 1>/dev/null
rm -rf .git

mkdir -p "$dst/peony"
cp "$src"/etc/popl21-supplement/Makefile "$dst"/peony/
cp "$src"/etc/popl21-supplement/README.md "$dst"/peony/
copy peony _CoqProject.in
copy peony .gitignore
libs="coq-tactical coqutil record-update"
libs+=" iris stdpp string-ident string-ident-v8.11"
for lib in $libs; do
    copy peony "external/$lib"
done
rm -rf "$dst"/peony/external/*/vendor
make --dry-run src/program_proof/examples/print_assumptions.vo |\
    sed -E -n -e '/.* ([^ ]*).v$/s//\1.v/p' | $GREP -P -v '^external/(?!Goose)' |\
    sort > "$src/deps.txt"
# see https://github.com/koalaman/shellcheck/wiki/SC2013
while read -r file; do
    copy peony "$file"
done <"$src"/deps.txt

# TODO: clone tchajed/marshal and mit-pdos/perennial-examples (with anonymized
# directory name) into the supplement code

# TODO: anonymize
for file in "$out"/**; do
    if test -f "$file"; then
        $SED -i -e 's/perennial/peony/g' -e 's/Perennial/Peony/g' "$file"
    fi
done

# TODO: will need to anonymize directories in such a way that at least the Coq
# code compiles (we can give up on getting the Go to compile as well)

cd "$out"
tar -czf "$supplement_dir.tar.gz" "$supplement_dir"
mv "$supplement_dir.tar.gz" "$PERENNIAL/"

# for debugging
echo "$dst"
