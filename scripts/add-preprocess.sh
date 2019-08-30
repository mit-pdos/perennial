#!/bin/bash
set -e

# cross-platform sed (because macOS only has BSD sed):
# see http://stackoverflow.com/questions/5694228/sed-in-place-flag-that-works-both-on-mac-bsd-and-linux

for file in "$@"; do
    sed -i.bak $'1s|^|{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}\\\n|' "$file"
    rm "$file.bak"
done
