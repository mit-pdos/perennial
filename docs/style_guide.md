# Perennial style guide

**Warning:** this document is in its very early stages of development.
there are many missing hints, and some hints may be incorrect.

## iris-named-props

- low-level funcs (e.g., `bytes.Equal`) shouldn't provide names in their postcond.
context is almost always lost higher-up.
this adds more work for the caller to contextualize or remove the names.
- refrain from referring to auto-generated hypothesis names (e.g., `H10`) in proofs.
these are brittle.
if the proof changes even slightly (e.g., by adding a new premise),
the names need to be changed.
