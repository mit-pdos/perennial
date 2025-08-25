#!/usr/bin/env bash
# Skip Qed commands by changing them to Admitted.
#
# This speeds up the build by about 10% at the cost of not checking universe
# constraints.
#
# This script toggles between Qed and Unshelve. Fail idtac. Admitted. in source
# code. `Fail idtac` is a trick to check that there are no goals remaining.

set -eu

SED="sed"

if command -v gsed >/dev/null ; then
    SED=gsed
fi

inplace_edit() {
    $SED -r -i~ "$@"
}

forward_repl() {
    local search='([[:space:]]*)(Time )?Qed\.'
    local repl="\1Unshelve. Fail idtac. \2Admitted."
    inplace_edit "s/^${search}$/${repl}/" "$@"
}

backward_repl() {
    local search="([[:space:]]*)"
    search="${search}Unshelve\. Fail idtac\. "
    search="${search}(Time )?Admitted\.$"
    local repl='\1\2Qed.'
    inplace_edit "s/^${search}$/${repl}/" "$@"
}


reverse=false

usage() {
    echo "Usage: disable-qed.sh [--undo] <files>"
}

case "$1" in
    "--help" )
        usage
        exit
        ;;
    "--undo" )
        reverse=true
        shift
        ;;
    *)
        echo "unknown option $1" 1>&2
        exit 1
        ;;
esac

if [ $reverse = true ]; then
    backward_repl "$@"
else
    forward_repl "$@"
fi
