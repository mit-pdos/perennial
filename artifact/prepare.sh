#!/bin/bash

## Put together artifact tarball

src="$1"
out="/tmp/armada-artifact"
out_dir="$PWD"

if [ -z "$src" ]; then
  echo "Usage: $0 <path to armada src>"
  exit 1
fi

rm -rf "$out"
mkdir "$out"

make -C "$src/artifact"

src=$(realpath "$src")
pushd "$out" || exit 1
# package up armada.tar.gz
"$src"/release.sh "$src" >/dev/null
tar -xf armada.tar.gz
rm armada.tar.gz

# package up the rest of the artifact
cp "$src/artifact/README.html" ./
cp "$src/artifact/loc.sh" ./
popd || exit 1
find "$out" -type f -name '._*' -delete

# Note that the uploaded artifact needs to be a zip file because HotCRP
# doesn't preserve the tar part of the filename for compressed tarballs.
pushd "$out/.." || exit 1
rm -f "$out_dir/armada-artifact.zip"
zip -r "$out_dir/armada-artifact.zip" $(basename "$out")
popd || exit 1
rm -r "$out"
