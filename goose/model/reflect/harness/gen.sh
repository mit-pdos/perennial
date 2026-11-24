#!/usr/bin/env bash
# Writes the generated (gitignored) parts of the harness from the overlay:
#   reflectcore/helpers.go  the translated generic helpers, copied;
#   reflectmodel/           the reflect model (overlay reflect/*.go) as package reflectmodel, its
#                           imports of internal/reflectcore and internal/gomodel rewritten to the
#                           harness's (core_harness.go over the real reflect; a Stuck that panics);
#   reflectlitemodel/       the reflectlite model (overlay internal/reflectlite/*.go) likewise, and
#                           its import of internal/abi rewritten to the harness's abi (Kind);
#   errorsmodel/            the real errors/wrap.go (of the go on PATH) over reflectlitemodel.
# and checks that the harness declares every stub of the overlay's reflectcore and gomodel.
#
# Usage: gen.sh [overlay dir]   (default: this checkout's goose/model/overlay)
# Then:  cd goose/model/reflect/harness && GOWORK=off go test ./...
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
overlay=$(cd "${1:-$here/../../overlay}" && pwd)
mod=github.com/mit-pdos/perennial/goose/model/reflect/harness

cp "$overlay/internal/reflectcore/helpers.go" "$here/reflectcore/helpers.go"
rm -rf "$here/reflectmodel"
mkdir "$here/reflectmodel"
for f in "$overlay"/reflect/*.go; do
	case "$f" in *_test.go) continue ;; esac
	sed -e 's/^package reflect$/package reflectmodel/' \
		-e "s#\"internal/reflectcore\"#\"$mod/reflectcore\"#" \
		-e "s#\"internal/gomodel\"#\"$mod/gomodel\"#" \
		"$f" >"$here/reflectmodel/$(basename "$f")"
done

rm -rf "$here/reflectlitemodel"
mkdir "$here/reflectlitemodel"
for f in "$overlay"/internal/reflectlite/*.go; do
	case "$f" in *_test.go) continue ;; esac
	sed -e 's/^package reflectlite$/package reflectlitemodel/' \
		-e "s#\"internal/reflectcore\"#\"$mod/reflectcore\"#" \
		-e "s#\"internal/gomodel\"#\"$mod/gomodel\"#" \
		-e "s#\"internal/abi\"#\"$mod/abi\"#" \
		"$f" >"$here/reflectlitemodel/$(basename "$f")"
done

# the real errors/wrap.go of the Go on PATH, over the reflectlite model, as package errorsmodel
rm -rf "$here/errorsmodel"
mkdir "$here/errorsmodel"
sed -e 's/^package errors$/package errorsmodel/' \
	-e "s#\"internal/reflectlite\"#reflectlite \"$mod/reflectlitemodel\"#" \
	"$(go env GOROOT)/src/errors/wrap.go" >"$here/errorsmodel/wrap.go"

# signatures: `func Name(params) results`, without the body
sigs() { grep -o '^func [A-Z][^{]*' "$1" | sed 's/ *$//'; }
missing=0
check() {
	while IFS= read -r sig; do
		if ! sigs "$2" | grep -qxF "$sig"; then
			echo "gen.sh: $(basename "$2") lacks: $sig" >&2
			missing=1
		fi
	done < <(sigs "$1")
}
check "$overlay/internal/reflectcore/core.go" "$here/reflectcore/core_harness.go"
check "$overlay/internal/gomodel/gomodel.go" "$here/gomodel/gomodel.go"
exit $missing
