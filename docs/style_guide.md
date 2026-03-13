# Perennial style guide

**Warning:** this document is in its very early stages of development.
there are many missing hints, and some hints may be incorrect.

## Naming
Names for general-purpose specs (predicate definitions, file names, library names) should represent what they inherently are (the abstraction and their intrinsic properties) rather than how a specific caller happens to use them (their application and their extrinsic purpose). E.g. prefer `bag` for a general purpose unordered channel specification rather than `handoff` (the latter is the verb referring to what applications might do, whereas the former summarizes the abstraction provided by the spec.)

## iris-named-props

- low-level funcs (e.g., `bytes.Equal`) shouldn't provide names in their postcond.
context is almost always lost higher-up.
this adds more work for the caller to contextualize or remove the names.
- refrain from referring to auto-generated hypothesis names (e.g., `H10`) in proofs.
these are brittle.
if the proof changes even slightly (e.g., by adding a new premise),
the names need to be changed.
