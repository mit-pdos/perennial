#!/usr/bin/env bash
#
# Toggle between Qed and Admitted in source code.
# To be safer than Admitted, we actually add some extra commands that ensure
# there are no remaining goals.

SED=sed

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
    "--undo" )
        reverse=true
        shift
        ;;
esac

if [ $reverse = true ]; then
    backward_repl "$@"
else
    forward_repl "$@"
fi
