From Perennial.goose_lang Require Export lang.
Set Default Proof Using "Type".
Import goose_lang.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  (* Note that the current context is spread into a list of fully-constructed
     items [K], and a list of pairs of values [vs] (prophecy identifier and
     resolution value) that is only non-empty if a [ResolveLCtx] item (maybe
     having several levels) is in the process of being constructed. Note that
     a fully-constructed item is inserted into [K] by calling [add_item], and
     that is only the case when a non-[ResolveLCtx] item is built. When [vs]
     is non-empty, [add_item] also wraps the item under several [ResolveLCtx]
     constructors: one for each pair in [vs]. *)
  let rec go K e :=
    match e with
    | _                               => tac K e
    | App ?e (Val ?v)                 => add_item (@AppLCtx _ v) K e
    | App ?e1 ?e2                     => add_item (@AppRCtx _ e1) K e2
    | UnOp ?op ?e                     => add_item (@UnOpCtx _ op) K e
    | BinOp ?op (Val ?v) ?e           => add_item (@BinOpRCtx _ op v) K e
    | BinOp ?op ?e1 ?e2               => add_item (@BinOpLCtx _ op e2) K e1
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) K e0
    | Pair (Val ?v) ?e                => add_item (PairRCtx v) K e
    | Pair ?e1 ?e2                    => add_item (PairLCtx e2) K e1
    | Fst ?e                          => add_item (@FstCtx _) K e
    | Snd ?e                          => add_item (@SndCtx _) K e
    | InjL ?e                         => add_item (@InjLCtx _) K e
    | InjR ?e                         => add_item (@InjRCtx _) K e
    | Case ?e0 ?e1 ?e2                => add_item (CaseCtx e1 e2) K e0
    | Primitive2 ?op (Val ?v) ?e      => add_item (@Primitive2RCtx _ op v) K e
    | Primitive2 ?op ?e1 ?e2          => add_item (@Primitive2LCtx _ op e2) K e1
    | Primitive1 ?op ?e               => add_item (@Primitive1Ctx _ op) K e
    | ExternalOp ?op ?e               => add_item (@ExternalOpCtx _ op) K e
    (* | Primitive3 ?op (Val ?v0) (Val ?v1) ?e2 => add_item (Primitive3RCtx op v0 v1) K e2
    | Primitive3 ?op (Val ?v0) ?e1 ?e2     => add_item (Primitive3MCtx op v0 e2) K e1
    | Primitive3 ?op ?e0 ?e1 ?e2           => add_item (Primitive3LCtx op e1 e2) K e0 *)
    | CmpXchg (Val ?v0) (Val ?v1) ?e2 => add_item (CmpXchgRCtx v0 v1) K e2
    | CmpXchg (Val ?v0) ?e1 ?e2       => add_item (CmpXchgMCtx v0 e2) K e1
    | CmpXchg ?e0 ?e1 ?e2             => add_item (CmpXchgLCtx e1 e2) K e0
    end
  with add_item Ki K e :=
    go (Ki :: K) e
  in
  go (@nil ectx_item) e.
