From New.golang.defn Require Export exception pkg loop array slice map predeclared defer.
Export RecordSet RecordSetNotations.

Module go.
(** [go.PreSemantics] has the parts of Gooses's Go semantics that do not rely on
   code written in Go itself. For instance, Goose has a channel model
   implemented in Go so channel semantics are not present here. Instead, the
   channel model proof actually uses the below semantics. *)
Class PreSemantics {ext : ffi_syntax} {go_lctx : GoLocalContext}
  {go_gctx : GoGlobalContext} `{!GoSemanticsFunctions} : Prop :=
  {
    #[global] core_sem :: go.CoreSemantics;
    #[global] array_sem :: go.ArraySemantics;
    #[global] map_sem :: go.MapSemantics;
    #[global] slice_sem :: go.SliceSemantics;
    #[global] predeclared_sem :: go.PredeclaredSemantics;
  }.

End go.
