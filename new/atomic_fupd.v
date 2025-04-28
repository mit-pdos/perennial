From Perennial.program_logic Require Import crash_weakestpre.
Set Default Proof Using "Type".

(* Note regarding the use of [Eo%I%I%I%I] below:

   Coq insists that in a notation, if a nonterminal (like Eo) is used multiple
   times, it must be under the exact same scope stack each time. Some Iris
   notations add [%I] to their nonterminals to ensure they remain in the iris
   scope. Eo is used below by different Iris connectives, meaning different
   numbers of these implicit [%Is], and that difference has to be compensated by
   adding some explicit [%I] annotations.
 *)

(** Sugar for TaDA-style logically atomic specs. We only have the variants we need. *)
(** Use [fupd_mask_intro] if you are stuck with non-matching masks. *)

(* Without ▷ at lin.point (but still with ▷ around the entire continuation) *)
(* Full variant *)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e @@ Eo '<<<' ∃∃ y1 .. yn , β '>>>' {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ, P -∗ (▷ |NC={⊤∖Eo%I%I%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ ∀ y1, .. (∀ yn, β -∗ |NC={∅,⊤∖Eo}=> ∀ z1, .. (∀ zn, Q -∗ Φ v%V) .. ) .. ) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, z1 closed binder, zn closed binder,
   format "'[hv' {{{  '[' P  ']' } } }  '/' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @@  Eo  '/' '<<<'  '[' ∃∃  y1  ..  yn ,  '/' β  ']' '>>>'  '/' {{{  '[' z1  ..  zn ,  RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
(* No RET binders *)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e @@ Eo '<<<' ∃∃ y1 .. yn , β '>>>' {{{ 'RET' v ; Q } } }" :=
  (□ ∀ Φ, P -∗ (▷ |NC={⊤∖Eo%I%I%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ ∀ y1, .. (∀ yn, β -∗ |NC={∅,⊤∖Eo}=> Q -∗ Φ v%V) .. ) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder,
   format "'[hv' {{{  '[' P  ']' } } }  '/' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @@  Eo  '/' '<<<'  '[' ∃∃  y1  ..  yn ,  '/' β  ']' '>>>'  '/' {{{  '[' RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
(* No ∃∃ *)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e @@ Eo '<<<' β '>>>' {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ, P -∗ (▷ |NC={⊤∖Eo%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ (β -∗ |NC={∅,⊤∖Eo}=> ∀ z1, .. (∀ zn, Q -∗ Φ v%V) .. )) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, z1 closed binder, zn closed binder,
   format "'[hv' {{{  '[' P  ']' } } }  '/' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @@  Eo  '/' '<<<'  '[' β  ']' '>>>'  '/' {{{  '[' z1  ..  zn ,  RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
(* No ∃∃, no RET binders *)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e @@ Eo '<<<' β '>>>' {{{ 'RET' v ; Q } } }" :=
  (□ ∀ Φ, P -∗ (▷ |NC={⊤∖Eo%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ (β -∗ |NC={∅,⊤∖Eo}=> Q -∗ Φ v%V)) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder,
   format "'[hv' {{{  '[' P  ']' } } }  '/' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @@  Eo  '/' '<<<'  '[' β  ']' '>>>'  '/' {{{  '[' RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
(* No P *)
Notation "'<<<' ∀∀ x1 .. xn , α '>>>' e @@ Eo '<<<' ∃∃ y1 .. yn , β '>>>' {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ, (▷ |NC={⊤∖Eo%I%I%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ ∀ y1, .. (∀ yn, β -∗ |NC={∅,⊤∖Eo}=> ∀ z1, .. (∀ zn, Q -∗ Φ v%V) .. ) .. ) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, z1 closed binder, zn closed binder,
   format "'[hv' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @@  Eo  '/' '<<<'  '[' ∃∃  y1  ..  yn ,  '/' β  ']' '>>>'  '/' {{{  '[' z1  ..  zn ,  RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
(* No P, no RET binders *)
Notation "'<<<' ∀∀ x1 .. xn , α '>>>' e @@ Eo '<<<' ∃∃ y1 .. yn , β '>>>' {{{ 'RET' v ; Q } } }" :=
  (□ ∀ Φ, (▷ |NC={⊤∖Eo%I%I%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ ∀ y1, .. (∀ yn, β -∗ |NC={∅,⊤∖Eo}=> Q -∗ Φ v%V) .. ) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder,
   format "'[hv' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @@  Eo  '/' '<<<'  '[' ∃∃  y1  ..  yn ,  '/' β  ']' '>>>'  '/' {{{  '[' RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
(* No P, no ∃∃ *)
Notation "'<<<' ∀∀ x1 .. xn , α '>>>' e @@ Eo '<<<' β '>>>' {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ, (▷ |NC={⊤∖Eo%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ (β -∗ |NC={∅,⊤∖Eo}=> ∀ z1, .. (∀ zn, Q -∗ Φ v%V) .. )) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, z1 closed binder, zn closed binder,
   format "'[hv' '<<<'  '[' ∀∀  x1  ..  xn ,  α  ']' '>>>'  '/  ' e  '/' @@  Eo  '/' '<<<'  '[' β  ']' '>>>'  '/' {{{  '[' z1  ..  zn ,  RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
(* No P, no ∃∃, no RET binders *)
Notation "'<<<' ∀∀ x1 .. xn , α '>>>' e @@ Eo '<<<' β '>>>' {{{ 'RET' v ; Q } } }" :=
  (□ ∀ Φ, (▷ |NC={⊤∖Eo%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ (β -∗ |NC={∅,⊤∖Eo}=> Q -∗ Φ v%V)) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder,
   format "'[hv' '<<<'  '[' ∀∀  x1  ..  xn ,  α  ']' '>>>'  '/  ' e  '/' @@  Eo  '/' '<<<'  '[' β  ']' '>>>'  '/' {{{  '[' RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
