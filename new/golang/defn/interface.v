From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import struct dynamic_typing globals.
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
  λ: "type_id" "v", SOME ("type_id", "v").
Program Definition make := sealed @make_def.
Definition make_unseal : make = _ := seal_eq _.

(* our representation of dynamic type identity for interfaces is a tuple of (pkg
name, type string) *)
Definition type_id_eq : val :=
  λ: "type_id1" "type_id2",
    let: ("pkg1", "type1") := "type_id1" in
    let: ("pkg2", "type2") := "type_id2" in
    ("pkg1" = "pkg2") && ("type1" = "type2").

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
                      (type_id_eq (Fst "i1") (Fst "i2")) &&
                      (Snd "i1" = Snd "i2")
                  end
    end.

(* Models x.(T) - this checks the type of the value stored in interface object x
and also returns it. *)
Definition type_assert : val :=
  λ: "v" "expected_type_id",
    let: "v" := globals.unwrap "v" in
    let: ("type_id", "underlying_v") := "v" in
    if: type_id_eq "type_id" "expected_type_id" then
    "underlying_v"
    else Panic "coerce failed: wrong type".

(* Models v, ok := x.(T) - this checks the type and returns a boolean on
success. The type "T" is used to return the correct default value if the type
assertion fails. *)
Definition checked_type_assert : val :=
  λ: "T" "v" "expected_type_id",
    match: "v" with
      SOME "v" =>
        (let: ("type_id", "underlying_v") := "v" in
        if: type_id_eq "type_id" "expected_type_id"
        then ("underlying_v", #true)
        else (type.zero_val "T", #false))
     (* if the interface is nil, checked type assertions just return false *)
     | NONE => (type.zero_val "T", #false)
     end.

End goose_lang.
End interface.
