From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import struct dynamic_typing pkg.
From Perennial Require Import base.

Module interface.
Section goose_lang.
Context `{ffi_syntax}.

Definition get_def : val :=
  λ: "method_name" "v",
    let: ("type_id", "val") := option.unwrap "v" in
    method_call "type_id" "method_name" "val".

Program Definition get := sealed @get_def.
Definition get_unseal : get = _ := seal_eq _.

Local Definition make_def : val :=
  λ: "type_id" "v", SOME ("type_id", "v").
Program Definition make := sealed @make_def.
Definition make_unseal : make = _ := seal_eq _.

Definition eq : val :=
  (* This is a "short-circuiting" comparison that first checks if the type
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
                      ((Fst "i1") = (Fst "i2")) &&
                      (Snd "i1" = Snd "i2")
                  end
    end.

(* Models v.(T) - this checks the type of the value stored in interface object x
and also returns it. *)
Definition type_assert : val :=
  λ: "v" "expected_type_id",
    let: "v" := option.unwrap "v" in
    let: ("type_id", "underlying_v") := "v" in
    if: "type_id" = "expected_type_id" then
    "underlying_v"
    else Panic "coerce failed: wrong type".

(* Try converting interface value v to expected_type_id. Returns unit if the type mismatches.

This low-level primitive does not require knowing the type of
expected_type_id. *)
Definition try_type_coerce : val :=
  λ: "v" "expected_type_id",
    match: "v" with
      SOME "v" =>
        (let: ("type_id", "underlying_v") := "v" in
        if: "type_id" = "expected_type_id"
        then ("underlying_v", #true)
        else (#(), #false))
     | NONE =>
        (* if the interface is nil, checked type assertions just return false *)
         (#(), #false)
     end.

(* Models x, ok := v.(T) - this checks the type and returns a boolean on
success. The type "T" is used to return the correct default value if the type
assertion fails. *)
Definition checked_type_assert : val :=
  λ: "T" "v" "expected_type_id",
    let: ("x", "ok") := try_type_coerce "v" "expected_type_id" in
    if: "ok" then ("x", #true) else (type.zero_val "T", #false).

End goose_lang.
End interface.
