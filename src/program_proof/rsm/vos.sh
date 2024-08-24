#!/bin/bash

dir='./src/program_proof/rsm'

cd "$(dirname $0)"/../../../
files=`find ${dir} -name "${1}*.v" ! -name "print_assumptions.v" | sed "s/\.v/\.vos/"`
if [[ -z ${files} ]]; then
    echo "No target files."
    exit 1
fi

echo "Checking:"
echo "`basename ${files}`"
make -j8 ${files}
