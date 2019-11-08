From Perennial.go_lang Require Export lang.
Set Default Proof Using "Type".
Import heap_lang.

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
  let rec go K vs e :=
    match e with
    | _                               => lazymatch vs with [] => tac K e | _ => fail end
    | App ?e (Val ?v)                 => add_item (AppLCtx v) vs K e
    | App ?e1 ?e2                     => add_item (AppRCtx e1) vs K e2
    | UnOp ?op ?e                     => add_item (UnOpCtx op) vs K e
    | BinOp ?op ?e (Val ?v)           => add_item (BinOpLCtx op v) vs K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpRCtx op e1) vs K e2
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) vs K e0
    | Pair (Val ?v) ?e                => add_item (PairRCtx v) vs K e
    | Pair ?e1 ?e2                    => add_item (PairLCtx e2) vs K e1
    | Fst ?e                          => add_item (@FstCtx _) vs K e
    | Snd ?e                          => add_item (@SndCtx _) vs K e
    | InjL ?e                         => add_item (@InjLCtx _) vs K e
    | InjR ?e                         => add_item (@InjRCtx _) vs K e
    | Case ?e0 ?e1 ?e2                => add_item (CaseCtx e1 e2) vs K e0
    | AllocN ?e (Val ?v)              => add_item (AllocNLCtx v) vs K e
    | AllocN ?e1 ?e2                  => add_item (AllocNRCtx e1) vs K e2
    | Load ?e                         => add_item (@LoadCtx _) vs K e
    | Store ?e (Val ?v)               => add_item (StoreLCtx v) vs K e
    | Store ?e1 ?e2                   => add_item (StoreRCtx e1) vs K e2
    | MapGet (Val ?v) ?e              => add_item (MapGetLCtx v) vs K e
    | MapGet ?e1 ?e2                  => add_item (MapGetRCtx e1) vs K e2
    | MapInsert (Val ?v0) (Val ?v1) ?e2 => add_item (MapInsertRCtx v0 v1) vs K e2
    | MapInsert (Val ?v0) ?e1 ?e2     => add_item (MapInsertMCtx v0 e2) vs K e1
    | MapInsert ?e0 ?e1 ?e2           => add_item (MapInsertLCtx e1 e2) vs K e0
    | CmpXchg (Val ?v0) (Val ?v1) ?e2 => add_item (CmpXchgRCtx v0 v1) vs K e2
    | CmpXchg (Val ?v0) ?e1 ?e2       => add_item (CmpXchgMCtx v0 e2) vs K e1
    | CmpXchg ?e0 ?e1 ?e2             => add_item (CmpXchgLCtx e1 e2) vs K e0
    (* TODO: fix for left-to-right evaluation order *)
    | Resolve ?ex (Val ?v1) (Val ?v2) => go K ((v1,v2) :: vs) ex
    | Resolve ?ex ?e1 (Val ?v2)       => add_item (ResolveMCtx ex v2) vs K e1
    | Resolve ?ex ?e1 ?e2             => add_item (ResolveRCtx ex e1) vs K e2
    end
  with add_item Ki vs K e :=
    lazymatch vs with
    | []               => go (Ki :: K) (@nil (val * val)) e
    | (?v1,?v2) :: ?vs => add_item (ResolveLCtx Ki v1 v2) vs K e
    end
  in
  go (@nil ectx_item) (@nil (val * val)) e.
