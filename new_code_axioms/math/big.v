(* autogenerated by goose axiom generator; do not modify *)
From New.golang Require Import defn.

Section axioms.
Context `{ffi_syntax}.

Axiom Accuracy__String : val.
Axiom Word : go_type.
Axiom Word__mset : list (go_string * val).
Axiom Word__mset_ptr : list (go_string * val).
Axiom decimal__String : val.
Axiom Float : go_type.
Axiom Float__mset : list (go_string * val).
Axiom Float__mset_ptr : list (go_string * val).
Axiom ErrNaN : go_type.
Axiom ErrNaN__mset : list (go_string * val).
Axiom ErrNaN__mset_ptr : list (go_string * val).
Axiom ErrNaN__Error : val.
Axiom NewFloat : val.
Axiom MaxExp : Z.
Axiom MinExp : Z.
Axiom MaxPrec : Z.
Axiom RoundingMode : go_type.
Axiom RoundingMode__mset : list (go_string * val).
Axiom RoundingMode__mset_ptr : list (go_string * val).
Axiom ToNearestEven : expr.
Axiom ToNearestAway : expr.
Axiom ToZero : expr.
Axiom AwayFromZero : expr.
Axiom ToNegativeInf : expr.
Axiom ToPositiveInf : expr.
Axiom Accuracy : go_type.
Axiom Accuracy__mset : list (go_string * val).
Axiom Accuracy__mset_ptr : list (go_string * val).
Axiom Below : expr.
Axiom Exact : expr.
Axiom Above : expr.
Axiom Float__SetPrec : val.
Axiom Float__SetMode : val.
Axiom Float__Prec : val.
Axiom Float__MinPrec : val.
Axiom Float__Mode : val.
Axiom Float__Acc : val.
Axiom Float__Sign : val.
Axiom Float__MantExp : val.
Axiom Float__SetMantExp : val.
Axiom Float__Signbit : val.
Axiom Float__IsInf : val.
Axiom Float__IsInt : val.
Axiom Float__SetUint64 : val.
Axiom Float__SetInt64 : val.
Axiom Float__SetFloat64 : val.
Axiom Float__SetInt : val.
Axiom Float__SetRat : val.
Axiom Float__SetInf : val.
Axiom Float__Set : val.
Axiom Float__Copy : val.
Axiom Float__Uint64 : val.
Axiom Float__Int64 : val.
Axiom Float__Float32 : val.
Axiom Float__Float64 : val.
Axiom Float__Int : val.
Axiom Float__Rat : val.
Axiom Float__Abs : val.
Axiom Float__Neg : val.
Axiom Float__Add : val.
Axiom Float__Sub : val.
Axiom Float__Mul : val.
Axiom Float__Quo : val.
Axiom Float__Cmp : val.
Axiom Float__SetString : val.
Axiom Float__Parse : val.
Axiom ParseFloat : val.
Axiom Float__Scan : val.
Axiom Float__GobEncode : val.
Axiom Float__GobDecode : val.
Axiom Float__MarshalText : val.
Axiom Float__UnmarshalText : val.
Axiom Float__Text : val.
Axiom Float__String : val.
Axiom Float__Append : val.
Axiom Float__Format : val.
Axiom Int : go_type.
Axiom Int__mset : list (go_string * val).
Axiom Int__mset_ptr : list (go_string * val).
Axiom Int__Sign : val.
Axiom Int__SetInt64 : val.
Axiom Int__SetUint64 : val.
Axiom NewInt : val.
Axiom Int__Set : val.
Axiom Int__Bits : val.
Axiom Int__SetBits : val.
Axiom Int__Abs : val.
Axiom Int__Neg : val.
Axiom Int__Add : val.
Axiom Int__Sub : val.
Axiom Int__Mul : val.
Axiom Int__MulRange : val.
Axiom Int__Binomial : val.
Axiom Int__Quo : val.
Axiom Int__Rem : val.
Axiom Int__QuoRem : val.
Axiom Int__Div : val.
Axiom Int__Mod : val.
Axiom Int__DivMod : val.
Axiom Int__Cmp : val.
Axiom Int__CmpAbs : val.
Axiom Int__Int64 : val.
Axiom Int__Uint64 : val.
Axiom Int__IsInt64 : val.
Axiom Int__IsUint64 : val.
Axiom Int__Float64 : val.
Axiom Int__SetString : val.
Axiom Int__SetBytes : val.
Axiom Int__Bytes : val.
Axiom Int__FillBytes : val.
Axiom Int__BitLen : val.
Axiom Int__TrailingZeroBits : val.
Axiom Int__Exp : val.
Axiom Int__GCD : val.
Axiom Int__Rand : val.
Axiom Int__ModInverse : val.
Axiom Jacobi : val.
Axiom Int__ModSqrt : val.
Axiom Int__Lsh : val.
Axiom Int__Rsh : val.
Axiom Int__Bit : val.
Axiom Int__SetBit : val.
Axiom Int__And : val.
Axiom Int__AndNot : val.
Axiom Int__Or : val.
Axiom Int__Xor : val.
Axiom Int__Not : val.
Axiom Int__Sqrt : val.
Axiom Int__Text : val.
Axiom Int__Append : val.
Axiom Int__String : val.
Axiom Int__Format : val.
Axiom byteReader__ReadByte : val.
Axiom byteReader__UnreadByte : val.
Axiom Int__Scan : val.
Axiom Int__GobEncode : val.
Axiom Int__GobDecode : val.
Axiom Int__MarshalText : val.
Axiom Int__UnmarshalText : val.
Axiom Int__MarshalJSON : val.
Axiom Int__UnmarshalJSON : val.
Axiom nat__String : val.
Axiom MaxBase : expr.
Axiom Int__ProbablyPrime : val.
Axiom Rat : go_type.
Axiom Rat__mset : list (go_string * val).
Axiom Rat__mset_ptr : list (go_string * val).
Axiom NewRat : val.
Axiom Rat__SetFloat64 : val.
Axiom Rat__Float32 : val.
Axiom Rat__Float64 : val.
Axiom Rat__SetFrac : val.
Axiom Rat__SetFrac64 : val.
Axiom Rat__SetInt : val.
Axiom Rat__SetInt64 : val.
Axiom Rat__SetUint64 : val.
Axiom Rat__Set : val.
Axiom Rat__Abs : val.
Axiom Rat__Neg : val.
Axiom Rat__Inv : val.
Axiom Rat__Sign : val.
Axiom Rat__IsInt : val.
Axiom Rat__Num : val.
Axiom Rat__Denom : val.
Axiom Rat__Cmp : val.
Axiom Rat__Add : val.
Axiom Rat__Sub : val.
Axiom Rat__Mul : val.
Axiom Rat__Quo : val.
Axiom Rat__Scan : val.
Axiom Rat__SetString : val.
Axiom Rat__String : val.
Axiom Rat__RatString : val.
Axiom Rat__FloatString : val.
Axiom Rat__FloatPrec : val.
Axiom Rat__GobEncode : val.
Axiom Rat__GobDecode : val.
Axiom Rat__MarshalText : val.
Axiom Rat__UnmarshalText : val.
Axiom RoundingMode__String : val.
Axiom Float__Sqrt : val.
Axiom initialize' : val.
End axioms.
