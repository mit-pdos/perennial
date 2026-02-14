From New.golang.defn Require Export loop assume predeclared.
From New.code.github_com.goose_lang.goose.model Require Import strings.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

Class StringSemantics `{!GoSemanticsFunctions} :=
{
  #[global] package_sem :: strings.Assumptions;

  #[global] internal_string_len_step (s : go_string) ::
    ⟦InternalStringLen, #s⟧ ⤳ (if decide (length s < 2^63) then
                                  (Val #(W64 (length s)))
                                else AngelicExit #());

  #[global] string_len_unfold `{!t ↓u go.string} :: FuncUnfold go.len [t]
    (λ: "s", InternalStringLen "s")%V;

  #[global] string_index (s : go_string) (i : w64) `{!t ↓u go.string} ::
    ⟦Index t, (#s, #i)⟧ ⤳
    (match (s !! (sint.nat i)) with Some b => #b | _ => Panic "index out of bounds" end);

  #[global] convert_byte_to_string (c : w8) ::
    ⟦Convert go.byte go.string, #c⟧ ⤳[under] #([c]);

  #[global] convert_bytes_to_string
    `[!from ↓u go.SliceType elem_type] `[!elem_type ↓u go.byte] `[!to ↓u go.string] (v : val) ::
    ⟦Convert from to, v⟧ ⤳[internal] (@! strings.ByteSliceToString v);

  #[global] convert_string_to_bytes
    `[!from ↓u go.string] `[!to ↓u go.SliceType elem_type] `[!elem_type ↓u go.byte] (v : val) ::
    ⟦Convert from to, v⟧ ⤳[internal] (@! strings.StringToByteSlice v);
}.
End defs.
End go.
