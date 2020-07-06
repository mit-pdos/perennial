#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
PERENNIAL="$SCRIPT_DIR/../.."

# Set up a copy of the Perennial source tree at $src, using only git-tracked
# files. This ensures that copying from this tree only copies source files and not build outputs.
src=$(mktemp -d -t "perennial-clean.XXXXXX")
cp -r "$PERENNIAL/" "$src"
cd "$src"
git clean -fxd --quiet
git submodule --quiet foreach git clean -fxd --quiet
rm -rf .git
cd "$PERENNIAL"

# Set up the contents of the supplement at $out/$supplement_dir. We'll
# eventually tar this directory from $out, producing a tar file that contains a
# single directory peony-code, and everything will be in that directory.
#
# There's an extra level of hierarchy since the supplement contains a subset of
# the perennial tree (in peony) as well as the source for tchajed/marshal (in
# marshal) and mit-pdos/perennial-examples (in examples). There's also a
# README.md (the one at etc/popl21-supplement) to explain all of this.
out=$(mktemp -d -t "peony-code.XXXXXX")
supplement_dir="peony-code"
dst="$out/$supplement_dir"

# use gnu variants on macOS
GREP="grep"
if which ggrep >/dev/null 2>&1; then
    GREP="ggrep"
fi

SED="sed"
if which gsed >/dev/null 2>&1; then
    SED="gsed"
fi

# copy a Perennial source file into the archive under peony/
copy() {
    for file in "$@"; do
        dir=$(dirname "$file")
        mkdir -p "$dst/peony/$dir"
        cp -r "$src/$file" "$dst/peony/$dir/"
    done
}

# copy everything for perennial
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
rm -rf "$src"
# done with Perennial source

# clone tchajed/marshal and mit-pdos/perennial-examples (with anonymized directory name) into the supplement code
mkdir -p "$dst/marshal"
git clone git@github.com:tchajed/marshal.git "$dst/marshal"
rm -rf "$dst/marshal/.git"
mkdir -p "$dst/peony-examples"
git clone git@github.com:mit-pdos/perennial-examples.git "$dst/peony-examples"
rm -rf "$dst/peony-examples/.git"

## Anonymize
# TODO: anonymize more
find "$out" -type f |\
    while read -r file; do
        # do not anonymize in external/iris, external/stdpp,
        # external/string-ident (only external/Goose)
        ([[ $file = *"external/iris"* ]] &&\
        [[ $file = *"external/stdpp"* ]] &&\
        [[ $file = *"external/string-ident"* ]]) ||\
        $SED -E -i \
            -e 's/perennial/peony/g' \
            -e 's/Perennial/Peony/g' \
            -e 's/(tchajed|ralf)/anonymous/gi' \
            -e 's/(mit-pdos)/anonymous/gi' \
            -e 's/(pdos)/anonymous/gi' \
            -e 's/(mit)/anonymous/gi' \
            "$file"
    done

# anonymize directories
# NOTE: this probably doesn't work if a path needs two renames, no idea how to
# do this recursively and safely
find "$out" -type d |\
    while read -r dir; do
        anonymous="$dir"
        anonymous=${anonymous//perennial/peony}
        anonymous=${anonymous//tchajed/anonymous}
        anonymous=${anonymous//mit-pdos/anonymous}
        if [[ "$anonymous" != "$dir" ]]; then
            mv "$dir" "$anonymous"
        fi
    done

# tar the result
tar -czf "$PERENNIAL/$supplement_dir.tar.gz" -C "$out" "$supplement_dir"

# for debugging leave directory around
echo "$dst"
