#!/bin/bash

dir='./src/program_proof/tulip'

cd ../../../
files=`find ${dir} -name "${1}*.v" ! -name "print_assumptions.v" | sed "s/\.v/\.vok/"`
if [[ -z ${files} ]]; then
    echo "No target files."
    exit 1
fi

echo "Checking:"
echo "`basename ${files}`"
make --ignore-errors -j8 ${files}
