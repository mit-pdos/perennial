#!/usr/bin/env python3

# preprocessor: add extra imports
# preprocessor: ghc -F -pgmF

import re
import sys

import_modules = {
    "import qualified Lib":
    [
        "MachinePrimitives",
        "DataStructures",
        "Filesys",
        "ExtractionExamples",
    ],
}

module_imports = {}
for imp, modules in import_modules.items():
    for module in modules:
        if module not in module_imports:
            module_imports[module] = ""
        module_imports[module] += imp + "\n"

import argparse

parser = argparse.ArgumentParser()
parser.add_argument("fs_filename")
parser.add_argument("input", type=argparse.FileType())
parser.add_argument("output", type=argparse.FileType("w"))

args = parser.parse_args()
out = args.output

module_name = None
MODULE_RE = re.compile("module (?P<module>.*) where\n")

out.write("{-# LINE 1 \"%s\" #-}\n" % (args.input.name))
for n, line in enumerate(args.input, 1):
    m = MODULE_RE.match(line)
    if m:
        module_name = m.group("module")
    if line.strip() == "import qualified Prelude":
        mod_imports = module_imports.get(module_name)
        if mod_imports:
            out.write(mod_imports)
            out.write("{-# LINE %d \"%s\" #-}\n" % (n, args.input.name))
    line = line.replace('__FILE__', '"%s"' % args.input.name)
    line = line.replace('__LINE__', '%d' % n)
    out.write(line)
out.close()
