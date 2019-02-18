#!/usr/bin/env python3

# preprocessor: add extra imports
# preprocessor: ghc -F -pgmF

import re
import sys

import_modules = {
    "import qualified Lib":
    [
        "BinaryEncoding",
        "Common",
        "DataStructureTests",
        "DataStructures",
        "ExtractionExamples",
        "Filesys",
        "MachinePrimitives",
        "SimpleDb",
    ],
    "import qualified Data.Char":
    [
        "EqualDec",
    ],
    "import qualified Data.Bits":
    [
        "EqualDec",
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
MODULE_RE = re.compile(r"""module (?P<module>.*) where\n""")
MODULE_REPLACE = r"""module Coq.\1 where\n"""
IMPORT_RE = re.compile(r"""import qualified (?P<import>.*)""")
IMPORT_REPLACE = r"""import qualified Coq.\1 as \1"""

def is_ghc_import(mod):
    return (mod == "Prelude"
            or mod.startswith("GHC."))

out.write("{-# LINE 1 \"%s\" #-}\n" % (args.input.name))
for n, line in enumerate(args.input, 1):
    m = MODULE_RE.match(line)
    if m:
        module_name = m.group("module")
        line = MODULE_RE.sub(MODULE_REPLACE, line)
    if line.strip() == "import qualified Prelude":
        mod_imports = module_imports.get(module_name)
        if mod_imports:
            out.write(mod_imports)
            out.write("{-# LINE %d \"%s\" #-}\n" % (n, args.input.name))
    else:
        m = IMPORT_RE.match(line)
        if m and not is_ghc_import(m.group("import")):
            line = IMPORT_RE.sub(IMPORT_REPLACE, line)
    line = line.replace('__FILE__', '"%s"' % args.input.name)
    line = line.replace('__LINE__', '%d' % n)
    out.write(line)
out.close()
