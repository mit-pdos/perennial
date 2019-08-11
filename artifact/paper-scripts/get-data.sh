#!/bin/bash
#
# Runs run-{mailboat,gomail,mailserver}.sh and filters the results.

usage() {
    echo "Usage: $0 <path to run-{mailboat,gomail,mailserver}.sh> <threads>" 1>&2
}

script="$1"
num_cores="$2"

if [ ! -f "$script" ]; then
    usage
    exit 1
fi

if [ -z "$num_cores" ]; then
    usage
    exit 1
fi

script_name=$(basename "$script")
echo "# $script_name $num_cores"
echo
GOGC=200 "$script" "$num_cores" 2>&1 | sed -r -n -e '/^real/s/real ([0-9.]*).*/\1/p' | awk '{print NR " " $0}'
