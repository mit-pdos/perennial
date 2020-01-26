From stdpp Require Export binders strings pretty.
From iris.program_logic Require Export language ectx_language ectxi_language.
From Perennial.Helpers Require Import Integers Transitions.
From Perennial.go_lang Require Export locations lang prelude.

Require Import Program.

Set Default Proof Using "Type".

Instance pretty_u64 : Pretty Integers.u64 :=
  fun x => pretty (word.unsigned x).

Instance pretty_u32 : Pretty Integers.u32 :=
  fun x => pretty (word.unsigned x).

Instance pretty_loc : Pretty loc :=
  fun x => pretty x.(loc_car).

Instance pretty_lit : Pretty base_lit :=
  fun x => match x with
        | LitInt n => ("LitInt(" ++ pretty n ++ ")")%string
        | LitInt32 n => ("LitInt32" ++ pretty n ++ ")")%string
        | LitBool true => "LitBool #t"
        | LitBool false => "LitBool #f"
        | LitByte b => "LitByte"
        | LitString s => "LitString"
        | LitUnit => "LitUnit"
        | LitPoison => "LitPoison"
        | LitLoc l => ("LitLoc" ++ pretty l ++ ")")%string
        | LitProphecy p => "LitProphecy"
        end.

Instance pretty_un_op : Pretty un_op :=
  fun x => match x with
        | NegOp => "NegOp"
        | MinusUnOp => "MinusUnOp"
        | ToUInt64Op => "ToUInt64Op"
        | ToUInt32Op => "ToUInt32Op"
        | ToUInt8Op => "ToUInt8Op"
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
