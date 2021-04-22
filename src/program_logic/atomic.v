From Perennial.program_logic Require Export crash_weakestpre.
From Perennial.algebra Require Export abs_laterable.
Set Default Proof Using "Type".

(** Sugar for TaDA-style logically atomic non-crash specs. *)
(* Use [ncfupd_mask_intro] if you are stuck with non-matching masks. *)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e @ Eo '<<<▷' β '>>>' {{{ 'RET' v ; Q } } }" :=
  (□ ∀ Φ, P -∗ (|NC={Eo%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ ▷ (β -∗ |NC={∅,Eo}=> Q -∗ Φ v)) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder,
   format "'[hv' {{{  P  } } }  '/'  '<<<'  ∀∀  x1  ..  xn ,  α  '>>>'  '/  ' e  @  Eo  '/' '[    ' '<<<▷'  β  '>>>'  '/' {{{  RET  v ;  Q  } } } ']' ']'")
  : bi_scope.

(** Sugar for HoCAP-style logically atomic crash specs.
[Pa] is what the client *gets* right before the linearization point, and [Qa]
is what they have to prove to complete linearization.

We use [<<{] becazse [<<<] is already used in Iris for TaDa-style logically
atomic triples.

TODO: add versions without the ∀∀ binder.
And maybe versions with an ∃∃ binder in front of [Qa]? *)

Notation "'{{{' P } } } '<<{' ∀∀ x1 .. xn , Pa '}>>' e @ k ; E1 <<{ Qa '}>>' {{{ z1 .. zn , 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (□ ∀ Φ Φc (HL: AbsLaterable Φc),
      P -∗
      <disc> (Qc%I%I -∗ Φc) (* crash condition before lin.point *) ∧
        ▷ (∀ x1, .. (∀ xn, Pa -∗ |NC={E1}=> Qa ∗
          (<disc> (Qc -∗ Φc) (* crash condition after lin.point *) ∧
           ∀ z1, .. (∀ zn, Q -∗ Φ pat%V) .. )) .. ) -∗
      WPC e @ k; ⊤ {{ Φ }} {{ Φc }})%I
    (at level 20, x1 closed binder, xn closed binder, z1 closed binder, zn closed binder,
     format "'[hv' {{{  P  } } }  '/'  <<{  ∀∀  x1  ..  xn ,  Pa }>>  '/  ' e  '/' @  k ;  E1  '/' <<{ Qa }>>  '/' {{{  z1  ..  zn ,  RET  pat ;  Q  } } }  '/' {{{  Qc  } } } ']'") : bi_scope.

Notation "'{{{' P } } } '<<{' ∀∀ x1 .. xn , Pa '}>>' e @ k ; E1 <<{ Qa '}>>' {{{ 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (□ ∀ Φ Φc (HL: AbsLaterable Φc),
      P -∗
      <disc> (Qc%I%I -∗ Φc) (* crash condition before lin.point *) ∧
        ▷ (∀ x1, .. (∀ xn, Pa -∗ |NC={E1}=> Qa ∗
          (<disc> (Qc -∗ Φc) (* crash condition after lin.point *) ∧
          (Q -∗ Φ pat%V) )) .. ) -∗
      WPC e @ k; ⊤ {{ Φ }} {{ Φc }})%I
    (at level 20, x1 closed binder, xn closed binder,
     format "'[hv' {{{  P  } } }  '/'  <<{  ∀∀  x1  ..  xn ,  Pa }>>  '/  ' e  '/' @  k ;  E1  '/' <<{ Qa }>>  '/' {{{  RET  pat ;  Q  } } }  '/' {{{  Qc  } } } ']'") : bi_scope.
