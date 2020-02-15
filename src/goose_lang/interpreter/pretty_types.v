From stdpp Require Export binders strings pretty.
From iris.program_logic Require Export language ectx_language ectxi_language.
From Perennial.Helpers Require Import Integers Transitions.
From Perennial.goose_lang Require Export locations lang prelude.

Require Import Program.

Set Default Proof Using "Type".

Instance pretty_u64 : Pretty Integers.u64 :=
  fun x => pretty (word.unsigned x).

Instance pretty_u32 : Pretty Integers.u32 :=
  fun x => pretty (word.unsigned x).

Instance pretty_loc : Pretty loc :=
  fun x => pretty x.(loc_car).

Definition single_quote: string := String (Ascii.ascii_of_N 34%N) EmptyString.
Definition quoted (s:string) : string := (single_quote ++ s ++ single_quote)%string.

Instance pretty_lit : Pretty base_lit :=
  fun x => match x with
        | LitInt n => "#" ++ pretty n
        | LitInt32 n => "#(U32 " ++ pretty n ++ ")"
        | LitBool b => if b then "#t" else "f"
        | LitByte b => "LitByte"
        | LitString s => "str" ++ quoted s
        | LitUnit => "#()"
        | LitPoison => "LitPoison"
        | LitLoc l => "#(loc " ++ pretty l ++ ")"
        | LitProphecy p => "LitProphecy"
        end%string.

Instance pretty_un_op : Pretty un_op :=
  fun x => match x with
        | NegOp => "NegOp"
        | MinusUnOp => "MinusUnOp"
        | ToUInt64Op => "to_u64"
        | ToUInt32Op => "to_u32"
        | ToUInt8Op => "to_u8"
        | ToStringOp => "to_string"
        end.

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
        | OffsetOp k => ("OffsetOp(" ++ pretty k ++ ")")%string
        end.
