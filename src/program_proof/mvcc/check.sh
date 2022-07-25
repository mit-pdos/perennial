#!/bin/bash

dir='./src/program_proof/mvcc'

cd ../../../
files=`find ${dir} -name "${1}*.v" | sed 's/\.v/\.vok/'`
if [[ -z ${files} ]]; then
    echo "No target files."
    exit 1
fi

echo "Checking:"
echo "`basename ${files}`"
make -j4 ${files}
