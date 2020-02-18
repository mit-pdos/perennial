(* Warning: Extraction inside an opened module is experimental.In case of problem, close it first.
[extraction-inside-module,extraction]
Warning: The following axioms must be realized in the extracted
code: resize_buf writeverf eq_dec_fh buf fh len_buf EqDec_time createverf eq_dec_inode_state
      countable_inode_state countable_fh.
 [extraction-axiom-to-realize,extraction] *)


type __ = Obj.t

type unit0 =
| Tt

type bool =
| True
| False

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type decision = sumbool

(** val decide : decision -> sumbool **)

let decide decision0 =
  decision0

type ('a, 'b) relDecision = 'a -> 'b -> decision

(** val decide_rel : ('a1, 'a2) relDecision -> 'a1 -> 'a2 -> decision **)

let decide_rel relDecision0 =
  relDecision0

type ('k, 'a, 'm) lookup = 'k -> 'm -> 'a option

(** val lookup0 : ('a1, 'a2, 'a3) lookup -> 'a1 -> 'a3 -> 'a2 option **)

let lookup0 lookup1 =
  lookup1

type ('k, 'a, 'm) insert = 'k -> 'a -> 'm -> 'm

(** val insert0 : ('a1, 'a2, 'a3) insert -> 'a1 -> 'a2 -> 'a3 -> 'a3 **)

let insert0 insert1 =
  insert1

type ('k, 'a, 'm) partialAlter = ('a option -> 'a option) -> 'k -> 'm -> 'm

(** val partial_alter :
    ('a1, 'a2, 'a3) partialAlter -> ('a2 option -> 'a2 option) -> 'a1 -> 'a3 -> 'a3 **)

let partial_alter partialAlter0 =
  partialAlter0

(** val bool_decide : decision -> bool **)

let bool_decide = function
| Left -> True
| Right -> False

(** val true_dec : decision **)

let true_dec =
  Left

(** val false_dec : decision **)

let false_dec =
  Right

(** val is_true_dec : bool -> decision **)

let is_true_dec = function
| True -> true_dec
| False -> false_dec

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p -> (match y with
               | XI q -> XO (add_carry p q)
               | XO q -> XI (add p q)
               | XH -> XO (succ p))
    | XO p -> (match y with
               | XI q -> XI (add p q)
               | XO q -> XO (add p q)
               | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p -> (match y with
               | XI q -> XO (add_carry p q)
               | XO q -> XI (add p q)
               | XH -> XO (succ p))
    | XH -> (match y with
             | XI q -> XI (succ q)
             | XO q -> XO (succ q)
             | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p -> (match y with
               | XI q -> compare_cont r p q
               | XO q -> compare_cont Gt p q
               | XH -> Gt)
    | XO p -> (match y with
               | XI q -> compare_cont Lt p q
               | XO q -> compare_cont r p q
               | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> False)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> False)
    | XH -> (match q with
             | XH -> True
             | _ -> False)

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> XI (coq_lor p0 q0)
                | XO q0 -> XI (coq_lor p0 q0)
                | XH -> p)
    | XO p0 -> (match q with
                | XI q0 -> XI (coq_lor p0 q0)
                | XO q0 -> XO (coq_lor p0 q0)
                | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH -> (match q with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH -> (match q with
             | XO _ -> Npos XH
             | _ -> N0)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH -> (match q with
             | XI q0 -> Npos (XO q0)
             | XO q0 -> Npos (XI q0)
             | XH -> N0)
 end

module N =
 struct
  (** val succ_double : n -> n **)

  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val double : n -> n **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val succ_pos : n -> positive **)

  let succ_pos = function
  | N0 -> XH
  | Npos p -> Coq_Pos.succ p

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' -> (match Coq_Pos.sub_mask n' m' with
                     | Coq_Pos.IsPos p -> Npos p
                     | _ -> N0))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Coq_Pos.compare n' m')

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val pos_div_eucl : positive -> n -> (n, n) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XH ->
      (match b with
       | N0 -> Pair (N0, (Npos XH))
       | Npos p -> (match p with
                    | XH -> Pair ((Npos XH), N0)
                    | _ -> Pair (N0, (Npos XH))))

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Coq_Pos.coq_land p q)

  (** val ldiff : n -> n -> n **)

  let rec ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Coq_Pos.ldiff p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Coq_Pos.coq_lxor p q)
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH -> (match y with
             | XI q -> Zneg (XO q)
             | XO q -> Zneg (Coq_Pos.pred_double q)
             | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val pred : z -> z **)

  let pred x =
    add x (Zneg XH)

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 =
    Coq_Pos.iter (mul z0) (Zpos XH)

  (** val pow : z -> z -> z **)

  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' -> (match y with
                  | Zneg y' -> compOpp (Coq_Pos.compare x' y')
                  | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val gtb : z -> z -> bool **)

  let gtb x y =
    match compare x y with
    | Gt -> True
    | _ -> False

  (** val eqb : z -> z -> bool **)

  let rec eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> True
             | _ -> False)
    | Zpos p -> (match y with
                 | Zpos q -> Coq_Pos.eqb p q
                 | _ -> False)
    | Zneg p -> (match y with
                 | Zneg q -> Coq_Pos.eqb p q
                 | _ -> False)

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XH ->
      (match leb (Zpos (XO XH)) b with
       | True -> Pair (Z0, (Zpos XH))
       | False -> Pair ((Zpos XH), Z0))

  (** val div_eucl : z -> z -> (z, z) prod **)

  let div_eucl a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> Pair (Z0, Z0)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, Z0)
       | Zpos _ ->
         let Pair (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' -> let Pair (q, r) = pos_div_eucl a' (Zpos b') in Pair (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let Pair (q, _) = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let Pair (_, r) = div_eucl a b in r

  (** val quotrem : z -> z -> (z, z) prod **)

  let quotrem a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 -> let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in Pair ((of_N q), (of_N r))
       | Zneg b0 -> let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in Pair ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in Pair ((opp (of_N q)), (opp (of_N r)))
       | Zneg b0 -> let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in Pair ((of_N q), (opp (of_N r))))

  (** val quot : z -> z -> z **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : z -> z -> z **)

  let rem a b =
    snd (quotrem a b)

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | XH -> Z0
               | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p -> Zneg (Coq_Pos.div2_up p)

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Coq_Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Coq_Pos.iter div2 a p

  (** val shiftr : z -> z -> z **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_lor : z -> z -> z **)

  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Coq_Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))

  (** val coq_land : z -> z -> z **)

  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Coq_Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Coq_Pos.pred_N a0))
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))

  (** val ldiff : z -> z -> z **)

  let ldiff a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.ldiff a0 b0)
       | Zneg b0 -> of_N (N.coq_land (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.ldiff (Coq_Pos.pred_N b0) (Coq_Pos.pred_N a0)))

  (** val coq_lxor : z -> z -> z **)

  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.coq_lxor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Coq_Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))

  (** val lnot : z -> z **)

  let lnot a =
    pred (opp a)
 end

(** val z_le_dec : z -> z -> sumbool **)

let z_le_dec x y =
  match Z.compare x y with
  | Gt -> Right
  | _ -> Left

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

(** val z_le_dec0 : (z, z) relDecision **)

let z_le_dec0 =
  z_le_dec

type 'a countable = { encode : ('a -> positive); decode : (positive -> 'a option) }

(** val map_insert : ('a1, 'a2, 'a3) partialAlter -> ('a1, 'a2, 'a3) insert **)

let map_insert h i x =
  partial_alter h (fun _ -> Some x) i

type 'a pmap_raw =
| PLeaf
| PNode of 'a option * 'a pmap_raw * 'a pmap_raw

(** val pNode' : 'a1 option -> 'a1 pmap_raw -> 'a1 pmap_raw -> 'a1 pmap_raw **)

let pNode' o l r =
  match l with
  | PLeaf ->
    (match o with
     | Some _ -> PNode (o, l, r)
     | None -> (match r with
                | PLeaf -> PLeaf
                | PNode (_, _, _) -> PNode (o, l, r)))
  | PNode (_, _, _) -> PNode (o, l, r)

(** val plookup_raw : (positive, 'a1, 'a1 pmap_raw) lookup **)

let rec plookup_raw i = function
| PLeaf -> None
| PNode (o, l, r) ->
  (match i with
   | XI i0 -> lookup0 plookup_raw i0 r
   | XO i0 -> lookup0 plookup_raw i0 l
   | XH -> o)

(** val psingleton_raw : positive -> 'a1 -> 'a1 pmap_raw **)

let rec psingleton_raw i x =
  match i with
  | XI i0 -> PNode (None, PLeaf, (psingleton_raw i0 x))
  | XO i0 -> PNode (None, (psingleton_raw i0 x), PLeaf)
  | XH -> PNode ((Some x), PLeaf, PLeaf)

(** val ppartial_alter_raw :
    ('a1 option -> 'a1 option) -> positive -> 'a1 pmap_raw -> 'a1 pmap_raw **)

let rec ppartial_alter_raw f i = function
| PLeaf -> (match f None with
            | Some x -> psingleton_raw i x
            | None -> PLeaf)
| PNode (o, l, r) ->
  (match i with
   | XI i0 -> pNode' o l (ppartial_alter_raw f i0 r)
   | XO i0 -> pNode' o (ppartial_alter_raw f i0 l) r
   | XH -> pNode' (f o) l r)

type 'a pmap = 'a pmap_raw
  (* singleton inductive, whose constructor was PMap *)

(** val pmap_car : 'a1 pmap -> 'a1 pmap_raw **)

let pmap_car p =
  p

(** val plookup : (positive, 'a1, 'a1 pmap) lookup **)

let plookup i m =
  lookup0 plookup_raw i (pmap_car m)

(** val ppartial_alter : (positive, 'a1, 'a1 pmap) partialAlter **)

let ppartial_alter f i m =
  partial_alter ppartial_alter_raw f i m

type ('k, 'a) gmap = 'a pmap
  (* singleton inductive, whose constructor was GMap *)

(** val gmap_lookup :
    ('a1, 'a1) relDecision -> 'a1 countable -> ('a1, 'a2, ('a1, 'a2) gmap) lookup **)

let gmap_lookup _ h i pat =
  lookup0 plookup (h.encode i) pat

(** val gmap_partial_alter :
    ('a1, 'a1) relDecision -> 'a1 countable -> ('a1, 'a2, ('a1, 'a2) gmap) partialAlter **)

let gmap_partial_alter _ h f i pat =
  partial_alter ppartial_alter f (h.encode i) pat

type ('e, 't) reader = 'e -> 't

(** val constructor : 'a2 -> ('a1, 'a2) reader **)

let constructor x _ =
  x

type ('r, 't) setter = ('t -> 't) -> 'r -> 'r

(** val set : ('a1 -> 'a2) -> ('a1, 'a2) setter -> ('a2 -> 'a2) -> 'a1 -> 'a1 **)

let set _ setter0 =
  setter0

type ('t, 'x) genPred = z -> 'x -> 't option

type ('t, 'x) genBool = z -> 'x -> 't option

(** val fallback_genBool : ('a2 -> 'a1 -> bool) -> ('a1, 'a2) genBool **)

let fallback_genBool _ _ _ =
  None

type ('x0, 'x) transition =
| RunF of ('x0 -> ('x0, 'x) prod)
| SuchThat of ('x, 'x0) genPred
| SuchThatBool of ('x0 -> 'x -> bool) * ('x, 'x0) genBool
| Bind of ('x0, __) transition * (__ -> ('x0, 'x) transition)

(** val ret : 'a2 -> ('a1, 'a2) transition **)

let ret v =
  RunF (fun s -> Pair (s, v))

(** val reads : ('a1 -> 'a2) -> ('a1, 'a2) transition **)

let reads f =
  RunF (fun s -> Pair (s, (f s)))

(** val modify : ('a1 -> 'a1) -> ('a1, unit0) transition **)

let modify f =
  RunF (fun s -> Pair ((f s), Tt))

(** val undefined : ('a1, 'a2) transition **)

let undefined =
  SuchThat (fun _ _ -> None)

(** val ifThenElse :
    decision -> ('a1, 'a2) transition -> ('a1, 'a2) transition -> ('a1, 'a2) transition **)

let ifThenElse decision0 tr1 tr2 =
  match decide decision0 with
  | Left -> tr1
  | Right -> tr2

(** val check : decision -> ('a1, unit0) transition **)

let check decision0 =
  ifThenElse decision0 (ret Tt) undefined

module Coq_word =
 struct
  type word = { unsigned : (__ -> z); signed : (__ -> z); of_Z : (z -> __); add : (__ -> __ -> __);
                sub : (__ -> __ -> __); opp : (__ -> __); coq_or : (__ -> __ -> __);
                coq_and : (__ -> __ -> __); xor : (__ -> __ -> __); not : (__ -> __);
                ndn : (__ -> __ -> __); mul : (__ -> __ -> __); mulhss : (__ -> __ -> __);
                mulhsu : (__ -> __ -> __); mulhuu : (__ -> __ -> __); divu : (__ -> __ -> __);
                divs : (__ -> __ -> __); modu : (__ -> __ -> __); mods : (__ -> __ -> __);
                slu : (__ -> __ -> __); sru : (__ -> __ -> __); srs : (__ -> __ -> __);
                eqb : (__ -> __ -> bool); ltu : (__ -> __ -> bool); lts : (__ -> __ -> bool);
                sextend : (z -> __ -> __) }

  type rep = __

  (** val unsigned : z -> word -> rep -> z **)

  let unsigned _ word1 =
    word1.unsigned

  (** val signed : z -> word -> rep -> z **)

  let signed _ word1 =
    word1.signed

  (** val of_Z : z -> word -> z -> rep **)

  let of_Z _ word1 =
    word1.of_Z

  (** val add : z -> word -> rep -> rep -> rep **)

  let add _ word1 =
    word1.add

  (** val sub : z -> word -> rep -> rep -> rep **)

  let sub _ word1 =
    word1.sub

  (** val opp : z -> word -> rep -> rep **)

  let opp _ word1 =
    word1.opp

  (** val coq_or : z -> word -> rep -> rep -> rep **)

  let coq_or _ word1 =
    word1.coq_or

  (** val coq_and : z -> word -> rep -> rep -> rep **)

  let coq_and _ word1 =
    word1.coq_and

  (** val xor : z -> word -> rep -> rep -> rep **)

  let xor _ word1 =
    word1.xor

  (** val not : z -> word -> rep -> rep **)

  let not _ word1 =
    word1.not

  (** val ndn : z -> word -> rep -> rep -> rep **)

  let ndn _ word1 =
    word1.ndn

  (** val mul : z -> word -> rep -> rep -> rep **)

  let mul _ word1 =
    word1.mul

  (** val mulhss : z -> word -> rep -> rep -> rep **)

  let mulhss _ word1 =
    word1.mulhss

  (** val mulhsu : z -> word -> rep -> rep -> rep **)

  let mulhsu _ word1 =
    word1.mulhsu

  (** val mulhuu : z -> word -> rep -> rep -> rep **)

  let mulhuu _ word1 =
    word1.mulhuu

  (** val divu : z -> word -> rep -> rep -> rep **)

  let divu _ word1 =
    word1.divu

  (** val divs : z -> word -> rep -> rep -> rep **)

  let divs _ word1 =
    word1.divs

  (** val modu : z -> word -> rep -> rep -> rep **)

  let modu _ word1 =
    word1.modu

  (** val mods : z -> word -> rep -> rep -> rep **)

  let mods _ word1 =
    word1.mods

  (** val slu : z -> word -> rep -> rep -> rep **)

  let slu _ word1 =
    word1.slu

  (** val sru : z -> word -> rep -> rep -> rep **)

  let sru _ word1 =
    word1.sru

  (** val srs : z -> word -> rep -> rep -> rep **)

  let srs _ word1 =
    word1.srs

  (** val eqb : z -> word -> rep -> rep -> bool **)

  let eqb _ word1 =
    word1.eqb

  (** val ltu : z -> word -> rep -> rep -> bool **)

  let ltu _ word1 =
    word1.ltu

  (** val lts : z -> word -> rep -> rep -> bool **)

  let lts _ word1 =
    word1.lts

  (** val sextend : z -> word -> z -> rep -> rep **)

  let sextend _ word1 =
    word1.sextend
 end

type rep0 = z
  (* singleton inductive, whose constructor was mk *)

(** val unsigned0 : z -> rep0 -> z **)

let unsigned0 _ r =
  r

(** val wrap : z -> z -> rep0 **)

let wrap width z0 =
  Z.modulo z0 (Z.pow (Zpos (XO XH)) width)

(** val signed0 : z -> rep0 -> z **)

let signed0 width =
  let wrap_value = fun z0 -> Z.modulo z0 (Z.pow (Zpos (XO XH)) width) in
  let swrap_value = fun z0 ->
    Z.sub (wrap_value (Z.add z0 (Z.pow (Zpos (XO XH)) (Z.sub width (Zpos XH)))))
      (Z.pow (Zpos (XO XH)) (Z.sub width (Zpos XH)))
  in
  (fun w -> swrap_value (unsigned0 width w))

(** val word0 : z -> Coq_word.word **)

let word0 width =
  { Coq_word.unsigned = (Obj.magic unsigned0 width); Coq_word.signed = (Obj.magic signed0 width);
    Coq_word.of_Z = (Obj.magic wrap width); Coq_word.add = (fun x y ->
    Obj.magic wrap width (Z.add (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y))));
    Coq_word.sub = (fun x y ->
    Obj.magic wrap width (Z.sub (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y))));
    Coq_word.opp = (fun x -> Obj.magic wrap width (Z.opp (unsigned0 width (Obj.magic x))));
    Coq_word.coq_or = (fun x y ->
    Obj.magic wrap width (Z.coq_lor (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y))));
    Coq_word.coq_and = (fun x y ->
    Obj.magic wrap width (Z.coq_land (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y))));
    Coq_word.xor = (fun x y ->
    Obj.magic wrap width (Z.coq_lxor (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y))));
    Coq_word.not = (fun x -> Obj.magic wrap width (Z.lnot (unsigned0 width (Obj.magic x))));
    Coq_word.ndn = (fun x y ->
    Obj.magic wrap width (Z.ldiff (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y))));
    Coq_word.mul = (fun x y ->
    Obj.magic wrap width (Z.mul (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y))));
    Coq_word.mulhss = (fun x y ->
    Obj.magic wrap width
      (Z.div (Z.mul (signed0 width (Obj.magic x)) (signed0 width (Obj.magic y)))
        (Z.pow (Zpos (XO XH)) width))); Coq_word.mulhsu = (fun x y ->
    Obj.magic wrap width
      (Z.div (Z.mul (signed0 width (Obj.magic x)) (unsigned0 width (Obj.magic y)))
        (Z.pow (Zpos (XO XH)) width))); Coq_word.mulhuu = (fun x y ->
    Obj.magic wrap width
      (Z.div (Z.mul (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y)))
        (Z.pow (Zpos (XO XH)) width))); Coq_word.divu = (fun x y ->
    Obj.magic wrap width (Z.div (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y))));
    Coq_word.divs = (fun x y ->
    Obj.magic wrap width (Z.quot (signed0 width (Obj.magic x)) (signed0 width (Obj.magic y))));
    Coq_word.modu = (fun x y ->
    Obj.magic wrap width (Z.modulo (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y))));
    Coq_word.mods = (fun x y ->
    Obj.magic wrap width (Z.rem (signed0 width (Obj.magic x)) (signed0 width (Obj.magic y))));
    Coq_word.slu = (fun x y ->
    Obj.magic wrap width (Z.shiftl (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y))));
    Coq_word.sru = (fun x y ->
    Obj.magic wrap width (Z.shiftr (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y))));
    Coq_word.srs = (fun x y ->
    Obj.magic wrap width (Z.shiftr (signed0 width (Obj.magic x)) (unsigned0 width (Obj.magic y))));
    Coq_word.eqb = (fun x y ->
    Z.eqb (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y))); Coq_word.ltu =
    (fun x y -> Z.ltb (unsigned0 width (Obj.magic x)) (unsigned0 width (Obj.magic y)));
    Coq_word.lts = (fun x y -> Z.ltb (signed0 width (Obj.magic x)) (signed0 width (Obj.magic y)));
    Coq_word.sextend = (fun oldwidth z0 ->
    Obj.magic wrap width
      (Z.sub
        (Z.modulo
          (Z.add (unsigned0 width (Obj.magic z0)) (Z.pow (Zpos (XO XH)) (Z.sub oldwidth (Zpos XH))))
          (Z.pow (Zpos (XO XH)) oldwidth)) (Z.pow (Zpos (XO XH)) (Z.sub oldwidth (Zpos XH))))) }

type u64_rep = Coq_word.rep
  (* singleton inductive, whose constructor was Word64 *)

(** val u64_car : u64_rep -> Coq_word.rep **)

let u64_car u =
  u

type u32_rep = Coq_word.rep
  (* singleton inductive, whose constructor was Word32 *)

(** val u32_car : u32_rep -> Coq_word.rep **)

let u32_car u =
  u

module Coq_u64_instance =
 struct
  (** val u64 : Coq_word.word **)

  let u64 =
    { Coq_word.unsigned = (fun w ->
      (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.unsigned (u64_car (Obj.magic w)));
      Coq_word.signed = (fun w ->
      (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.signed (u64_car (Obj.magic w)));
      Coq_word.of_Z = (fun z0 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.of_Z z0); Coq_word.add =
      (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.add
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.sub = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.sub
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.opp = (fun w ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.opp (u64_car (Obj.magic w)));
      Coq_word.coq_or = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.coq_or
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.coq_and = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.coq_and
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.xor = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.xor
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.not = (fun w ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.not (u64_car (Obj.magic w)));
      Coq_word.ndn = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.ndn
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.mul = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.mul
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.mulhss = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.mulhss
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.mulhsu = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.mulhsu
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.mulhuu = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.mulhuu
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.divu = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.divu
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.divs = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.divs
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.modu = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.modu
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.mods = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.mods
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.slu = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.slu
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.sru = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.sru
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.srs = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.srs
        (u64_car (Obj.magic w1)) (u64_car (Obj.magic w2))); Coq_word.eqb = (fun w1 w2 ->
      (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.eqb (u64_car (Obj.magic w1))
        (u64_car (Obj.magic w2))); Coq_word.ltu = (fun w1 w2 ->
      (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.ltu (u64_car (Obj.magic w1))
        (u64_car (Obj.magic w2))); Coq_word.lts = (fun w1 w2 ->
      (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.lts (u64_car (Obj.magic w1))
        (u64_car (Obj.magic w2))); Coq_word.sextend = (fun width' w ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO (XO XH)))))))).Coq_word.sextend width'
        (u64_car (Obj.magic w))) }
 end

module Coq_u32_instance =
 struct
  (** val u32 : Coq_word.word **)

  let u32 =
    { Coq_word.unsigned = (fun w ->
      (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.unsigned (u32_car (Obj.magic w)));
      Coq_word.signed = (fun w ->
      (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.signed (u32_car (Obj.magic w)));
      Coq_word.of_Z = (fun z0 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.of_Z z0); Coq_word.add =
      (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.add (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.sub = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.sub (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.opp = (fun w ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.opp (u32_car (Obj.magic w)));
      Coq_word.coq_or = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.coq_or (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.coq_and = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.coq_and (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.xor = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.xor (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.not = (fun w ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.not (u32_car (Obj.magic w)));
      Coq_word.ndn = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.ndn (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.mul = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.mul (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.mulhss = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.mulhss (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.mulhsu = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.mulhsu (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.mulhuu = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.mulhuu (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.divu = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.divu (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.divs = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.divs (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.modu = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.modu (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.mods = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.mods (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.slu = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.slu (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.sru = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.sru (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.srs = (fun w1 w2 ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.srs (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.eqb = (fun w1 w2 ->
      (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.eqb (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.ltu = (fun w1 w2 ->
      (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.ltu (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.lts = (fun w1 w2 ->
      (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.lts (u32_car (Obj.magic w1))
        (u32_car (Obj.magic w2))); Coq_word.sextend = (fun width' w ->
      Obj.magic (word0 (Zpos (XO (XO (XO (XO (XO XH))))))).Coq_word.sextend width'
        (u32_car (Obj.magic w))) }
 end

type u0 = Coq_word.rep

type u1 = Coq_word.rep

(** val u2 : z -> u0 **)

let u2 x =
  Coq_u64_instance.u64.Coq_word.of_Z x

(** val u3 : z -> u1 **)

let u3 x =
  Coq_u32_instance.u32.Coq_word.of_Z x

(** val word_eq_dec : z -> Coq_word.word -> (Coq_word.rep, Coq_word.rep) relDecision **)

let word_eq_dec _ word1 x y =
  let b = word1.Coq_word.eqb x y in (match b with
                                     | True -> Left
                                     | False -> Right)

(** val u32_eq_dec : (u1, u1) relDecision **)

let u32_eq_dec =
  word_eq_dec (Zpos (XO (XO (XO (XO (XO XH)))))) Coq_u32_instance.u32

type err =
| ERR_PERM
| ERR_NOENT
| ERR_IO
| ERR_NXIO
| ERR_ACCES
| ERR_EXIST
| ERR_XDEV
| ERR_NODEV
| ERR_NOTDIR
| ERR_ISDIR
| ERR_INVAL
| ERR_FBIG
| ERR_NOSPC
| ERR_ROFS
| ERR_MLINK
| ERR_NAMETOOLONG
| ERR_NOTEMPTY
| ERR_DQUOT
| ERR_STALE
| ERR_REMOTE
| ERR_BADHANDLE
| ERR_NOT_SYNC
| ERR_BAD_COOKIE
| ERR_NOTSUPP
| ERR_TOOSMALL
| ERR_SERVERFAULT
| ERR_BADTYPE
| ERR_JUKEBOX

type ftype =
| NF3REG
| NF3DIR
| NF3BLK
| NF3CHR
| NF3LNK
| NF3SOCK
| NF3FIFO

type fh (* AXIOM TO BE REALIZED *)

type writeverf (* AXIOM TO BE REALIZED *)

type createverf (* AXIOM TO BE REALIZED *)

type filename = string

type fileid = u0

type time = { time_sec : u1; time_nsec : u1 }

(** val eqDec_time : (time, time) relDecision **)

let eqDec_time =
  failwith "AXIOM TO BE REALIZED"

type major_minor = { major : u1; minor : u1 }

type fattr = { fattr_type : ftype; fattr_mode : u1; fattr_nlink : u1; fattr_uid : u1;
               fattr_gid : u1; fattr_size : u0; fattr_used : u0; fattr_rdev : major_minor;
               fattr_fsid : u0; fattr_fileid : fileid; fattr_atime : time; fattr_mtime : time;
               fattr_ctime : time }

type wcc_attr = { wcc_size : u0; wcc_mtime : time; wcc_ctime : time }

type wcc_data = { wcc_before : wcc_attr option; wcc_after : wcc_attr option }

(** val wcc_data_none : wcc_data **)

let wcc_data_none =
  { wcc_before = None; wcc_after = None }

type set_time =
| SET_TO_CLIENT_TIME of time
| SET_TO_SERVER_TIME

type sattr = { sattr_mode : u1 option; sattr_uid : u1 option; sattr_gid : u1 option;
               sattr_size : u0 option; sattr_atime : set_time option; sattr_mtime : set_time option }

type buf (* AXIOM TO BE REALIZED *)

(** val len_buf : buf -> u0 **)

let len_buf =
  failwith "AXIOM TO BE REALIZED"

(** val resize_buf : u0 -> buf -> buf **)

let resize_buf =
  failwith "AXIOM TO BE REALIZED"

type 't async = { latest : 't; pending : 't list }

(** val sync : ('a1, 'a1) relDecision -> 'a1 countable -> 'a1 -> 'a1 async **)

let sync _ _ v =
  { latest = v; pending = Nil }

type ('a, 't) res =
| OK of 'a * 't
| Err of 'a * err

type inode_type_state =
| Ifile of buf * createverf
| Idir of (filename, fh) gmap
| Iblk of major_minor
| Ichr of major_minor
| Isymlink of filename
| Isock
| Ififo

type inode_meta = { inode_meta_nlink : u1; inode_meta_mode : u1; inode_meta_uid : u1;
                    inode_meta_gid : u1; inode_meta_fileid : fileid; inode_meta_atime : time;
                    inode_meta_mtime : time; inode_meta_ctime : time }

type inode_state = { inode_state_meta : inode_meta; inode_state_type : inode_type_state; ctr : z }

(** val eq_dec_inode_state : (inode_state, inode_state) relDecision **)

let eq_dec_inode_state =
  failwith "AXIOM TO BE REALIZED"

(** val countable_inode_state : inode_state countable **)

let countable_inode_state =
  failwith "AXIOM TO BE REALIZED"

(** val eq_dec_fh : (fh, fh) relDecision **)

let eq_dec_fh =
  failwith "AXIOM TO BE REALIZED"

(** val countable_fh : fh countable **)

let countable_fh =
  failwith "AXIOM TO BE REALIZED"

type state = { fhs : (fh, inode_state async) gmap; verf : writeverf; clock : time; global_ctr : z }

(** val inode_wcc : inode_state -> wcc_attr **)

let inode_wcc i =
  let m = i.inode_state_meta in
  { wcc_size = (match i.inode_state_type with
                | Ifile (b, _) -> len_buf b
                | _ -> u2 Z0); wcc_mtime = m.inode_meta_mtime; wcc_ctime = m.inode_meta_ctime }

(** val result_bind :
    (state, ('a1, 'a2) res) transition -> ('a2 -> (state, 'a3) transition) -> (state, 'a3) transition **)

let result_bind x fx =
  Bind ((Obj.magic x), (fun r -> match Obj.magic r with
                                 | OK (_, v) -> fx v
                                 | Err (_, _) -> undefined))

(** val symBool : (state, bool) transition **)

let symBool =
  SuchThatBool ((fun _ _ -> True), (fallback_genBool (fun _ _ -> True)))

(** val symU32 : (state, u1) transition **)

let symU32 =
  SuchThatBool ((fun _ _ -> True), (fallback_genBool (fun _ _ -> True)))

(** val symU64 : (state, u0) transition **)

let symU64 =
  SuchThatBool ((fun _ _ -> True), (fallback_genBool (fun _ _ -> True)))

(** val symAssert : bool -> (state, unit0) transition **)

let symAssert b =
  check (is_true_dec b)

(** val call_reads : (state -> 'a1) -> (state, 'a1) transition **)

let call_reads read_f =
  Bind ((reads (fun s -> Obj.magic s)), (fun s -> ret (Obj.magic read_f s)))

(** val call_puts : (state -> state) -> (state, unit0) transition **)

let call_puts put_f =
  Bind ((reads (fun s -> Obj.magic s)), (fun s -> modify (fun _ -> Obj.magic put_f s)))

(** val symTime : (state, time) transition **)

let symTime =
  Bind (symU32, (fun ts -> Bind (symU32, (fun tn -> ret { time_sec = ts; time_nsec = tn }))))

(** val get_fh : fh -> 'a1 -> (state, ('a1, inode_state) res) transition **)

let get_fh f a =
  Bind ((call_reads (fun s -> Obj.magic lookup0 (gmap_lookup eq_dec_fh countable_fh) f s.fhs)),
    (fun i ->
    match Obj.magic i with
    | Some i0 -> ret (OK (a, i0.latest))
    | None ->
      Bind ((Obj.magic symBool), (fun z0 ->
        match Obj.magic z0 with
        | True -> ret (Err (a, ERR_STALE))
        | False -> ret (Err (a, ERR_BADHANDLE))))))

(** val inode_attrs : inode_state -> (state, fattr) transition **)

let inode_attrs i =
  Bind (symU64, (fun used -> Bind (symU64, (fun fsid -> Bind (symU64, (fun non_file_len ->
    let m = i.inode_state_meta in
    let res0 = { fattr_type =
      (match i.inode_state_type with
       | Ifile (_, _) -> NF3REG
       | Idir _ -> NF3DIR
       | Iblk _ -> NF3BLK
       | Ichr _ -> NF3CHR
       | Isymlink _ -> NF3LNK
       | Isock -> NF3SOCK
       | Ififo -> NF3FIFO); fattr_mode = m.inode_meta_mode; fattr_nlink = m.inode_meta_nlink;
      fattr_uid = m.inode_meta_uid; fattr_gid = m.inode_meta_gid; fattr_size =
      (match i.inode_state_type with
       | Ifile (b, _) -> len_buf b
       | _ -> non_file_len); fattr_used = used; fattr_rdev =
      (match i.inode_state_type with
       | Iblk mm -> mm
       | Ichr mm -> mm
       | _ -> { major = (u3 Z0); minor = (u3 Z0) }); fattr_fsid = fsid; fattr_fileid =
      m.inode_meta_fileid; fattr_atime = m.inode_meta_atime; fattr_mtime = m.inode_meta_mtime;
      fattr_ctime = m.inode_meta_ctime }
    in
    ret res0))))))

(** val getattr_step : fh -> (state, (unit0, fattr) res) transition **)

let getattr_step f =
  result_bind (get_fh f None) (fun i -> Bind ((Obj.magic inode_attrs i), (fun attrs ->
    ret (OK (Tt, (Obj.magic attrs))))))

(** val check_ctime_guard :
    inode_state -> time option -> 'a1 -> (state, ('a1, unit0) res) transition **)

let check_ctime_guard i ctime_guard a =
  match ctime_guard with
  | Some ct ->
    (match decide (decide_rel eqDec_time ct i.inode_state_meta.inode_meta_ctime) with
     | Left -> ret (OK (a, Tt))
     | Right -> ret (Err (a, ERR_NOT_SYNC)))
  | None -> ret (OK (a, Tt))

(** val time_ge : time -> time -> bool **)

let time_ge t t' =
  match bool_decide
          (decide_rel z_le_dec0 (Coq_u32_instance.u32.Coq_word.unsigned t.time_sec)
            (Coq_u32_instance.u32.Coq_word.unsigned t'.time_sec)) with
  | True -> True
  | False ->
    (match bool_decide (decide_rel u32_eq_dec t'.time_sec t.time_sec) with
     | True ->
       (match bool_decide (decide_rel u32_eq_dec t'.time_nsec t.time_nsec) with
        | True -> True
        | False ->
          bool_decide
            (decide_rel z_le_dec0 (Coq_u32_instance.u32.Coq_word.unsigned t.time_nsec)
              (Coq_u32_instance.u32.Coq_word.unsigned t'.time_nsec)))
     | False -> False)

(** val get_time : (state, time) transition **)

let get_time =
  Bind ((call_reads (Obj.magic (fun s -> s.clock))), (fun t -> Bind ((Obj.magic symTime), (fun t' ->
    Bind ((Obj.magic symAssert (time_ge (Obj.magic t) (Obj.magic t'))), (fun _ -> Bind
    ((Obj.magic call_puts
       (set (Obj.magic (fun s -> s.clock)) (fun f e -> { fhs = e.fhs; verf = e.verf; clock =
         (Obj.magic f e.clock); global_ctr = e.global_ctr }) (constructor t'))), (fun _ ->
    ret (Obj.magic t')))))))))

(** val get_ctr : (state, z) transition **)

let get_ctr =
  Bind ((call_reads (Obj.magic (fun s -> s.global_ctr))), (fun ctr0 -> Bind
    ((Obj.magic call_puts
       (set (fun s -> s.global_ctr) (fun f e -> { fhs = e.fhs; verf = e.verf; clock = e.clock;
         global_ctr = (f e.global_ctr) }) (fun _ -> Z.add (Obj.magic ctr0) (Zpos XH)))), (fun _ ->
    ret (Z.add (Obj.magic ctr0) (Zpos XH))))))

(** val set_attr_one :
    inode_state -> time -> (inode_meta -> 'a1) -> (inode_meta, 'a1) setter -> 'a1 option ->
    inode_state **)

let set_attr_one i now f setter0 = function
| Some v ->
  set (fun i0 -> i0.inode_state_meta) (fun f0 e -> { inode_state_meta = (f0 e.inode_state_meta);
    inode_state_type = e.inode_state_type; ctr = e.ctr }) (fun m ->
    set f setter0 (constructor v)
      (set (fun i0 -> i0.inode_meta_ctime) (fun f0 e -> { inode_meta_nlink = e.inode_meta_nlink;
        inode_meta_mode = e.inode_meta_mode; inode_meta_uid = e.inode_meta_uid; inode_meta_gid =
        e.inode_meta_gid; inode_meta_fileid = e.inode_meta_fileid; inode_meta_atime =
        e.inode_meta_atime; inode_meta_mtime = e.inode_meta_mtime; inode_meta_ctime =
        (f0 e.inode_meta_ctime) }) (constructor now) m)) i
| None -> i

(** val set_attr_time :
    inode_state -> time -> (inode_meta -> time) -> (inode_meta, time) setter -> set_time option ->
    inode_state **)

let set_attr_time i now f setter0 = function
| Some v ->
  let newtime = match v with
                | SET_TO_CLIENT_TIME t -> t
                | SET_TO_SERVER_TIME -> now in
  set (fun i0 -> i0.inode_state_meta) (fun f0 e -> { inode_state_meta = (f0 e.inode_state_meta);
    inode_state_type = e.inode_state_type; ctr = e.ctr }) (fun m ->
    set (fun i0 -> i0.inode_meta_ctime) (fun f0 e -> { inode_meta_nlink = e.inode_meta_nlink;
      inode_meta_mode = e.inode_meta_mode; inode_meta_uid = e.inode_meta_uid; inode_meta_gid =
      e.inode_meta_gid; inode_meta_fileid = e.inode_meta_fileid; inode_meta_atime =
      e.inode_meta_atime; inode_meta_mtime = e.inode_meta_mtime; inode_meta_ctime =
      (f0 e.inode_meta_ctime) }) (constructor now) (set f setter0 (constructor newtime) m)) i
| None -> i

(** val truncate :
    inode_state -> time -> u0 option -> 'a1 -> (state, ('a1, inode_state) res) transition **)

let truncate i now sattr_req a =
  match sattr_req with
  | Some len ->
    (match i.inode_state_type with
     | Ifile (buf0, cverf) ->
       Bind ((Obj.magic symBool), (fun outOfSpace ->
         match match bool_decide
                       (is_true_dec
                         (Z.gtb (Coq_u64_instance.u64.Coq_word.unsigned len)
                           (Coq_u64_instance.u64.Coq_word.unsigned (len_buf buf0)))) with
               | True -> Obj.magic outOfSpace
               | False -> False with
         | True -> ret (Err (a, ERR_NOSPC))
         | False ->
           ret (OK (a,
             (set (fun i0 -> i0.inode_state_meta) (fun f e -> { inode_state_meta =
               (f e.inode_state_meta); inode_state_type = e.inode_state_type; ctr = e.ctr })
               (set (fun i0 -> i0.inode_meta_mtime) (fun f e -> { inode_meta_nlink =
                 e.inode_meta_nlink; inode_meta_mode = e.inode_meta_mode; inode_meta_uid =
                 e.inode_meta_uid; inode_meta_gid = e.inode_meta_gid; inode_meta_fileid =
                 e.inode_meta_fileid; inode_meta_atime = e.inode_meta_atime; inode_meta_mtime =
                 (f e.inode_meta_mtime); inode_meta_ctime = e.inode_meta_ctime }) (constructor now))
               (set (fun i0 -> i0.inode_state_type) (fun f e -> { inode_state_meta =
                 e.inode_state_meta; inode_state_type = (f e.inode_state_type); ctr = e.ctr })
                 (constructor (Ifile ((resize_buf len buf0), cverf))) i))))))
     | _ -> ret (Err (a, ERR_INVAL)))
  | None -> ret (OK (a, i))

(** val update_fh_sync : fh -> inode_state -> (state, unit0) transition **)

let update_fh_sync f i =
  Bind ((Obj.magic get_ctr), (fun ctr_val ->
    let i0 =
      set (Obj.magic (fun i0 -> i0.ctr)) (fun f0 e -> { inode_state_meta = e.inode_state_meta;
        inode_state_type = e.inode_state_type; ctr = (Obj.magic f0 e.ctr) }) (fun _ -> ctr_val) i
    in
    Bind ((call_reads (fun s -> Obj.magic lookup0 (gmap_lookup eq_dec_fh countable_fh) f s.fhs)),
    (fun ia ->
    match Obj.magic ia with
    | Some _ ->
      call_puts
        (set (fun s -> s.fhs) (fun f0 e -> { fhs = (f0 e.fhs); verf = e.verf; clock = e.clock;
          global_ctr = e.global_ctr }) (fun x ->
          insert0 (map_insert (gmap_partial_alter eq_dec_fh countable_fh)) f
            (sync eq_dec_inode_state countable_inode_state i0) x))
    | None -> ret Tt))))

(** val set_attr_nonlen : inode_state -> time -> sattr -> inode_state **)

let set_attr_nonlen i now a =
  let i0 =
    set_attr_one i now (fun i0 -> i0.inode_meta_mode) (fun f e -> { inode_meta_nlink =
      e.inode_meta_nlink; inode_meta_mode = (f e.inode_meta_mode); inode_meta_uid =
      e.inode_meta_uid; inode_meta_gid = e.inode_meta_gid; inode_meta_fileid = e.inode_meta_fileid;
      inode_meta_atime = e.inode_meta_atime; inode_meta_mtime = e.inode_meta_mtime;
      inode_meta_ctime = e.inode_meta_ctime }) a.sattr_mode
  in
  let i1 =
    set_attr_one i0 now (fun i1 -> i1.inode_meta_uid) (fun f e -> { inode_meta_nlink =
      e.inode_meta_nlink; inode_meta_mode = e.inode_meta_mode; inode_meta_uid =
      (f e.inode_meta_uid); inode_meta_gid = e.inode_meta_gid; inode_meta_fileid =
      e.inode_meta_fileid; inode_meta_atime = e.inode_meta_atime; inode_meta_mtime =
      e.inode_meta_mtime; inode_meta_ctime = e.inode_meta_ctime }) a.sattr_uid
  in
  let i2 =
    set_attr_one i1 now (fun i2 -> i2.inode_meta_gid) (fun f e -> { inode_meta_nlink =
      e.inode_meta_nlink; inode_meta_mode = e.inode_meta_mode; inode_meta_uid = e.inode_meta_uid;
      inode_meta_gid = (f e.inode_meta_gid); inode_meta_fileid = e.inode_meta_fileid;
      inode_meta_atime = e.inode_meta_atime; inode_meta_mtime = e.inode_meta_mtime;
      inode_meta_ctime = e.inode_meta_ctime }) a.sattr_gid
  in
  let i3 =
    set_attr_time i2 now (fun i3 -> i3.inode_meta_atime) (fun f e -> { inode_meta_nlink =
      e.inode_meta_nlink; inode_meta_mode = e.inode_meta_mode; inode_meta_uid = e.inode_meta_uid;
      inode_meta_gid = e.inode_meta_gid; inode_meta_fileid = e.inode_meta_fileid; inode_meta_atime =
      (f e.inode_meta_atime); inode_meta_mtime = e.inode_meta_mtime; inode_meta_ctime =
      e.inode_meta_ctime }) a.sattr_atime
  in
  set_attr_time i3 now (fun i4 -> i4.inode_meta_mtime) (fun f e -> { inode_meta_nlink =
    e.inode_meta_nlink; inode_meta_mode = e.inode_meta_mode; inode_meta_uid = e.inode_meta_uid;
    inode_meta_gid = e.inode_meta_gid; inode_meta_fileid = e.inode_meta_fileid; inode_meta_atime =
    e.inode_meta_atime; inode_meta_mtime = (f e.inode_meta_mtime); inode_meta_ctime =
    e.inode_meta_ctime }) a.sattr_mtime

(** val setattr_step : fh -> sattr -> time option -> (state, (wcc_data, unit0) res) transition **)

let setattr_step f a ctime_guard =
  result_bind (get_fh f wcc_data_none) (fun i ->
    let wcc_before0 = inode_wcc i in
    result_bind
      (check_ctime_guard i ctime_guard { wcc_before = (Some wcc_before0); wcc_after = (Some
        wcc_before0) }) (fun _ -> Bind ((Obj.magic get_time), (fun t ->
      result_bind
        (truncate i (Obj.magic t) a.sattr_size { wcc_before = (Some wcc_before0); wcc_after = (Some
          wcc_before0) }) (fun i0 ->
        let i1 = set_attr_nonlen i0 (Obj.magic t) a in
        Bind ((Obj.magic update_fh_sync f i1), (fun _ ->
        ret (OK ({ wcc_before = (Some wcc_before0); wcc_after = (Some (inode_wcc i1)) }, Tt)))))))))
