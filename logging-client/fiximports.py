#!/usr/bin/env python

# preprocessor: add extra imports
# preprocessor: ghc -F -pgmF

import re
import os, sys

import_modules = {
    "import qualified Data.ByteString":
    [
        "Disk",
    ],

    "import qualified Replication.TwoDiskOps":
    [
        "TwoDiskBaseImpl",
    ],

    "import Replication.TwoDiskEnvironment":
    [
        "ReplicatedDiskImpl",
        "NbdImpl",
        "NbdServer",
        "ReplicatedServer",
        "TwoDiskBaseImpl",
        "Abstraction",
    ],

    "import qualified Data.Word":
    [
        "NbdAPI",
    ],

    "import qualified Network.ServerOps":
    [
        "NbdImpl",
    ],
}

module_imports = {}
for imp, modules in import_modules.items():
    for module in modules:
        if module not in module_imports:
            module_imports[module] = ""
        module_imports[module] += imp + "\n"

fs_filename = sys.argv[1]
filename = sys.argv[2]
out = open(sys.argv[3], "w")

module_name = None

MODULE_RE = re.compile("module (?P<module>.*) where\n")

out.write("{-# LINE 1 \"%s\" #-}\n" % (filename))
for n, line in enumerate(open(filename), 1):
    m = MODULE_RE.match(line)
    if m:
        module_name = m.group("module")
    if line.strip() == "import qualified Prelude":
        mod_imports = module_imports.get(module_name)
        if mod_imports:
            out.write(mod_imports)
            out.write("{-# LINE %d \"%s\" #-}\n" % (n, filename))
    line = line.replace('__FILE__', '"%s"' % sys.argv[2])
    line = line.replace('__LINE__', '%d' % n)
    out.write(line)
out.close()
