# Overview of files:

- `op_wrappers.v` -- these are wrappers around implementations of the various
  twophase and alloc operations. The wrappers either enforce a pure interface
  (e.g. converting slice arguments/return values to and from lists), or are used
  to obtain a certain order of execution of arguments to the operations.
  
- `typed_translate.v` -- definition of typed translation rules for atomically
  blocks, as well as definitions of translations of the jrnl operations that are
  used outside of atomically blocks.

- `twophase_proof.v` -- this is a proof of correctness for the twophase locking
  code that is "generic", in the sense that it is not specific to the refinement
  proof. Rather, most assertions are parameterized by an `ex_mapsto` predicate
  that is required to hold on the contents of an addr/object assertion coming
  from the sep_buftxn interface.
  
- `wrapper_proof.v` -- proofs of triples for the code from `op_wrappers.v`,
   specializing the generic interface from `twophase_proof.v` to talk about
   refinement resources.

- `twophase_refinement_defs.v`, `twophase_sub_logical_reln_defs.v`, `twophase_refinement_proof.v` --
   intermediary lemmas/definitions needed to prove refinement using `the goose_lang` generic 
   refinement infrastructure.
   
- `twophase_refinment_thm.v` -- the statement and proof of the final refinement theorem

# TCB

What's trusted:

1) The usual things for any Goose/Perennial project: Coq, Goose translator, the Goose semantics, etc.
2) The Goose-generic definitions of typed translations (e.g. for code outside atomically blocks)
   (see `../../goose_lang/typed_translate.v`)
3) More or less all of `op_wrappers.v`, `typed_translate.v`
4) The jrnl_ffi semantics (see `../../goose_lang/ffi/jrnl_ffi_spec.v`)
5) The definitions and meaning of the statement in `twophase_refinement_thm.v` (e.g. `trace_refines`)

