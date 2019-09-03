#!/bin/bash

# Prepare a release tarball

set -e

src="$1"
output_dir=/tmp/perennial

if [ -z "$src" ]; then
  echo "Usage: $0 <perennial src>"
  exit 1
fi

rm -rf "$output_dir"
mkdir "$output_dir"
cp -r "$src/" "$output_dir/"

rm "$output_dir/.travis.yml"
rm -r "$output_dir/etc/ci"
rm -r "$output_dir/.github"
rm "$output_dir/src/.dir-locals.el"

# clean build outputs and untracked files
make -C "$output_dir" clean-all
git -C "$output_dir" clean -ffxd

# remove git repo
rm -rf $(find "$output_dir" -name '.git')
rm "$output_dir/.gitmodules"
find "$output_dir" -name '.gitignore' -exec rm {} \;

# package
find "$output_dir" -type f -name '._*' -delete
tar -czvf perennial.tar.gz -C "$(dirname "$output_dir")" "$(basename "$output_dir")"
rm -r "$output_dir"
