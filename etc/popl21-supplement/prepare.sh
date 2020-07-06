#!/usr/bin/env bash
set -euo pipefail

supplement_dir="peony-code"
out=$(mktemp -d -t "peony-code.XXXXXX")
src=$(mktemp -d -t "perennial-clean.XXXXXX")
dst="$out/$supplement_dir"
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
PERENNIAL="$SCRIPT_DIR/../.."

GREP="grep"
if which ggrep >/dev/null 2>&1; then
    GREP="ggrep"
fi

SED="sed"
if which gsed >/dev/null 2>&1; then
    SED="gsed"
fi

# copy a Perennial source file into the archive
copy() {
    for file in "$@"; do
        dir=$(dirname "$file")
        mkdir -p "$dst/peony/$dir"
        cp -r "$src/$file" "$dst/peony/$dir/"
    done
}

cp -r "$PERENNIAL/" "$src"
cd "$src"
git clean -fxd 1>/dev/null
rm -rf .git

mkdir -p "$dst/peony"
cp "$src"/etc/popl21-supplement/README.md "$dst"/
cp "$src"/etc/popl21-supplement/Makefile "$dst"/peony/
copy _CoqProject.in
copy .gitignore
copy LICENSE
libs="coq-tactical coqutil record-update"
libs+=" iris stdpp string-ident string-ident-v8.11"
for lib in $libs; do
    copy "external/$lib"
done
rm -rf "$dst"/peony/external/*/vendor
make --dry-run src/program_proof/examples/print_assumptions.vo |\
    sed -E -n -e '/.* ([^ ]*).v$/s//\1.v/p' | $GREP -P -v '^external/(?!Goose)' |\
    sort > "$src/deps.txt"
# see https://github.com/koalaman/shellcheck/wiki/SC2013
while read -r file; do
    copy "$file"
done <"$src"/deps.txt

# TODO: clone tchajed/marshal and mit-pdos/perennial-examples (with anonymized
# directory name) into the supplement code

# TODO: anonymize more
# TODO: should not anonymize in external/iris, external/stdpp,
# external/string-ident (only external/Goose)
find "$out" -type f |\
    while read -r file; do
        $SED -E -i \
            -e 's/perennial/peony/g' \
            -e 's/Perennial/Peony/g' \
            -e 's/(tchajed|ralf)/anonymous/gi' \
            "$file"
    done
find "$out" -type d |\
    while read -r dir; do
        anonymous="$dir"
        anonymous=${anonymous//perennial/peony}
        anonymous=${anonymous//tchajed/anonymous}
        if [[ "$anonymous" != "$dir" ]]; then
            mv "$dir" "$anonymous"
        fi
    done

cd "$out"
tar -czf "$supplement_dir.tar.gz" "$supplement_dir"
mv "$supplement_dir.tar.gz" "$PERENNIAL/"

rm -rf "$src"

# for debugging leave directory around
echo "$dst"
