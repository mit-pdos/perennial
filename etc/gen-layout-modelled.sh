#!/usr/bin/env bash
# Writes Perennial/Golang/Defn/LayoutModelled.lean (go.layoutModelled): the types whose layout a
# Go model changes, the list goose's unsafe.Sizeof refusal uses (goose/util.Models.LayoutModelled),
# over the packages Perennial translates: the standard library, this repository's modules
# (go.work) and goose-lang/primitive. goose checks that every config of Perennial/Code with a
# [model] table or a trusted declaration belongs to one of them, except:
#   github_com/mit_pdos/gokv/grove_ffi.toml   gokv is not a dependency here; its trusted entries
#                                             are functions (its types are translated).
# Needs the pinned go (etc/update-goose-new.py's GO_VERSION) first on PATH, with
# GOTOOLCHAIN=local.
#
# usage: etc/gen-layout-modelled.sh [--check]
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
cd "$ROOT"
go build -o "$OUT/goose" ./goose/cmd/goose
target=Perennial/Golang/Defn/LayoutModelled.lean
dest=$target
if [ "${1:-}" = "--check" ]; then
	dest=$OUT/LayoutModelled.lean
fi
"$OUT/goose" layout-modelled -configdir Perennial/Code -dir . -o "$dest" \
	-uncovered github_com/mit_pdos/gokv/grove_ffi.toml \
	std github.com/mit-pdos/perennial/... github.com/goose-lang/primitive/...
if [ "${1:-}" = "--check" ]; then
	diff -u "$target" "$dest"
	echo "gen-layout-modelled: $target is current"
fi
