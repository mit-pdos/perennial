#!/bin/bash

set -e

## Put together artifact tarball

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
src="$DIR"
out="/tmp/armada-artifact"
out_dir="$PWD"

rm -rf "$out"
mkdir "$out"

# build the artifact HTML
make -C "$src"

src=$(realpath "$src")
pushd "$out" || exit 1

# package up the rest of the artifact
mkdir -p armada-paper
cp "$src"/{README,EXPERIMENTS}.html ./
cp "$src/paper-scripts/"* ./armada-paper
popd || exit 1

# Note that the uploaded artifact needs to be a zip file because HotCRP
# doesn't preserve the tar part of the filename for compressed tarballs.
pushd "$out/.." || exit 1
rm -f "$out_dir/armada-artifact.zip"
zip -r "$out_dir/armada-artifact.zip" "$(basename "$out")"
popd || exit 1
rm -r "$out"
