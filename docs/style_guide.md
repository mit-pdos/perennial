# Perennial style guide

**Warning:** this document is in its very early stages of development.
there are many missing hints here, and some hints may be incorrect.

## iris-named-props

- low-level funcs (e.g., `bytes.Equal`) shouldn't provide names in their postcond.
context is almost always lost higher-up.
this adds more work for the caller to contextualize or remove the names.
