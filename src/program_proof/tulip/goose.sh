#!/bin/bash

cd "$(dirname $0)"/../../../
./etc/update-goose.py --compile --goose ../goose/ --tulip ../tulip/
