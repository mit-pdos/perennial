#!/bin/bash

cd "$(dirname $0)"/../../../../
./etc/update-goose-new.py --compile --goose ../../goose/ --tulip ../../tulip/
