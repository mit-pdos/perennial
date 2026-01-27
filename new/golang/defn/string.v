From New.golang.defn Require Export loop assume predeclared.
From New.code.github_com.goose_lang.goose.model Require Import strings.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

Class StringSemantics `{!GoSemanticsFunctions} :=
{
  #[global] package_sem :: strings.Assumptions;

  #[global] string_len_unfold `{!t ↓u go.string} :: FuncUnfold go.len [t]
    (λ: "s", if: IsNoStringOverflow "s" then StringLength "s"
             else AngelicExit #())%V;

  #[global] string_index (s : go_string) (i : w64) `{!t ↓u go.string} ::
    ⟦Index t, (#s, #i)⟧ ⤳
    (match (s !! (sint.nat i)) with Some b => #b | _ => Panic "index out of bounds" end);

  #[global] convert_byte_to_string (c : w8) ::
    ⟦Convert go.byte go.string, #c⟧ ⤳[under] #([c]);

  #[global] convert_bytes_to_string (v : val)
    `{!from ↓u go.SliceType elem_type} `{!elem_type ↓u go.byte} `{!to ↓u go.string} ::
    ⟦Convert from to, v⟧ ⤳[internal] (@! strings.ByteSliceToString v);

  #[global] convert_string_to_bytes (v : val)
    `{!from ↓u go.string} `{!to ↓u go.SliceType elem_type} `{!to ↓u go.byte} ::
    ⟦Convert from to, v⟧ ⤳[internal] (@! strings.StringToByteSlice v);
}.
End defs.
End go.
