From New.golang.defn Require Export mem typing.

Module globals.
Section defns.
Context `{ffi_syntax}.

Definition get : val :=
  λ: "x", match: GlobalGet "x" with
            SOME "x" => "x"
          | NONE => #() #()
          end.

Definition put: val :=
  λ: "x" "y", GlobalPut "x" "y".

Definition is_uninitialized : val :=
  λ: "pkgId",
    match: GlobalGet "pkgId" with
      SOME <> => #false
    | NONE => #true
    end.

End defns.
End globals.
