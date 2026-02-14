From New.golang.defn Require Export pre chan string.

Module go.
(** [go.Semantics] is the top-level typeclass covering all of Go language
    semantics guarantees. *)
Class Semantics {ext : ffi_syntax} {go_lctx : GoLocalContext}
  {go_gctx : GoGlobalContext} : Type :=
  {
    #[global] sem_fn :: GoSemanticsFunctions;
    #[global] core_sem :: go.PreSemantics;
    #[global] chan_sem :: go.ChanSemantics;
    #[global] string_sem :: go.StringSemantics;
  }.

End go.
