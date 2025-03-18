From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import struct typing globals.
From Perennial Require Import base.

Module interface.
Section goose_lang.
Context `{ffi_syntax}.

Definition get_def : val :=
  λ: "method_name" "v",
    let: (("pkg_name", "type_name"), "val") := globals.unwrap "v" in
    method_call "pkg_name" "type_name" "method_name" "val".

Program Definition get := sealed @get_def.
Definition get_unseal : get = _ := seal_eq _.

Local Definition make_def : val :=
  λ: "pkg_name" "type_name" "v", SOME ("pkg_name", "type_name", "v").
Program Definition make := sealed @make_def.
Definition make_unseal : make = _ := seal_eq _.

Definition eq : val :=
  (* XXX: this is a "short-circuiting" comparison that first checks if the type
     names are equal before possibly checking if the values are equal. *)
  λ: "v1" "v2",
    match: "v1" with
      NONE => match: "v2" with
               NONE => #true
             | SOME <> => #false
             end
    | SOME "i1" => match: "v2" with
                    NONE => #false
                  | SOME "i1" =>
                      let: ("pkg_type1", "v1") := "i1" in
                      let: ("pkg_type2", "v2") := "i2" in
                      if: "pkg_type1" = "pkg_type2" then
                        "v1" = "v2"
                      else
                        #false
                  end
    end.

End goose_lang.
End interface.
