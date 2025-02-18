From stdpp Require Import strings.
From stdpp Require Export pretty.
From Perennial.program_logic Require Import language ectx_language ectxi_language.
From Perennial.Helpers Require Import Integers Transitions ByteString.
From Perennial.goose_lang Require Import locations lang.

Set Default Proof Using "Type".

#[global]
Instance pretty_u64 : Pretty Integers.u64 :=
  fun x => pretty (word.unsigned x).

#[global]
Instance pretty_u32 : Pretty Integers.u32 :=
  fun x => pretty (word.unsigned x).

#[global]
Instance pretty_loc : Pretty loc :=
  fun x => pretty x.(loc_car).

Definition quoted (s:byte_string) : string :=
  ("""" ++ String.string_of_list_byte (w8_to_byte <$> s) ++ """")%string.

#[global]
Instance pretty_lit : Pretty base_lit :=
  fun x => match x with
        | LitInt n => "#" ++ pretty n
        | LitInt32 n => "#(W32 " ++ pretty n ++ ")"
        | LitBool b => if b then "#t" else "#f"
        | LitByte b => "LitByte"
        | LitString s => "str" ++ quoted s
        | LitUnit => "#()"
        | LitPoison => "LitPoison"
        | LitLoc l => "#(loc " ++ pretty l ++ ")"
        | LitProphecy p => "LitProphecy"
        end%string.

#[global]
Instance pretty_un_op : Pretty un_op :=
  fun x => match x with
        | NegOp => "NegOp"
        | MinusUnOp => "MinusUnOp"
        | UToW64Op => "u_to_w64"
        | UToW32Op => "u_to_w32"
        | UToW8Op => "u_to_w8"
        | SToW64Op => "s_to_w64"
        | SToW32Op => "s_to_w32"
        | SToW8Op => "s_to_w8"
        | ToStringOp => "to_string"
        | StringLenOp => "StringLength"
        | IsNoStringOverflowOp => "IsNoStringOverflow"
        end.

#[global]
Instance pretty_bin_op : Pretty bin_op :=
  fun x => match x with
        | PlusOp => "PlusOp"
        | MinusOp => "MinusOp"
        | MultOp => "MultOp"
        | QuotOp => "QuotOp"
        | RemOp => "RemOp"
        | AndOp => "AndOp"
        | OrOp => "OrOp"
        | XorOp => "XorOp"
        | ShiftLOp => "ShiftLOp"
        | ShiftROp => "ShiftROp"
        | LeOp => "LeOp"
        | LtOp => "LtOp"
        | EqOp => "EqOp"
        | StringGetOp => "StringGetOp"
        | OffsetOp k => ("OffsetOp(" ++ pretty k ++ ")")%string
        end.
