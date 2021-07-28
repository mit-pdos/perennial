From Perennial.program_logic Require Export crash_weakestpre.
From Perennial.algebra Require Export abs_laterable.
Set Default Proof Using "Type".

(** Sugar for TaDA-style logically atomic specs. We only have the variants we need. *)
(** Use [fupd_mask_intro] if you are stuck with non-matching masks. *)
(* With ▷ *)
(* Full variant *)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e @ Eo '<<<▷' ∃∃ y1 .. yn , β '>>>' {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ, P -∗ (|={⊤∖Eo%I%I%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ ▷ ∀ y1, .. (∀ yn, β -∗ |={∅,⊤∖Eo}=> ∀ z1, .. (∀ zn, Q -∗ Φ v%V) .. ) .. ) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, z1 closed binder, zn closed binder,
   format "'[hv' {{{  '[' P  ']' } } }  '/' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @  Eo  '/' '<<<▷'  '[' ∃∃  y1  ..  yn ,  '/' β  ']' '>>>'  '/' {{{  '[' z1  ..  zn ,  RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
(* No ∃∃, no RET binders *)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e @ Eo '<<<▷' β '>>>' {{{ 'RET' v ; Q } } }" :=
  (□ ∀ Φ, P -∗ (|={⊤∖Eo%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ ▷ (β -∗ |={∅,⊤∖Eo}=> Q -∗ Φ v%V)) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder,
   format "'[hv' {{{  '[' P  ']' } } }  '/' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @  Eo  '/' '<<<▷'  '[' β  ']' '>>>'  '/' {{{  '[' RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
(* No P *)
Notation "'<<<' ∀∀ x1 .. xn , α '>>>' e @ Eo '<<<▷' ∃∃ y1 .. yn , β '>>>' {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ, (|={⊤∖Eo%I%I%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ ▷ ∀ y1, .. (∀ yn, β -∗ |={∅,⊤∖Eo}=> ∀ z1, .. (∀ zn, Q -∗ Φ v%V) .. ) .. ) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, z1 closed binder, zn closed binder,
   format "'[hv' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @  Eo  '/' '<<<▷'  '[' ∃∃  y1  ..  yn ,  '/' β  ']' '>>>'  '/' {{{  '[' z1  ..  zn ,  RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
(* No P, no ∃∃ *)
Notation "'<<<' ∀∀ x1 .. xn , α '>>>' e @ Eo '<<<▷' β '>>>' {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ, (|={⊤∖Eo%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ ▷ (β -∗ |={∅,⊤∖Eo}=> ∀ z1, .. (∀ zn, Q -∗ Φ v%V) .. )) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, z1 closed binder, zn closed binder,
   format "'[hv' '<<<'  '[' ∀∀  x1  ..  xn ,  α  ']' '>>>'  '/  ' e  '/' @  Eo  '/' '<<<▷'  '[' β  ']' '>>>'  '/' {{{  '[' z1  ..  zn ,  RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.

(* Without ▷ *)
(* Full variant *)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e @ Eo '<<<' ∃∃ y1 .. yn , β '>>>' {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ, P -∗ (|={⊤∖Eo%I%I%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ ∀ y1, .. (∀ yn, β -∗ |={∅,⊤∖Eo}=> ∀ z1, .. (∀ zn, Q -∗ Φ v%V) .. ) .. ) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, z1 closed binder, zn closed binder,
   format "'[hv' {{{  '[' P  ']' } } }  '/' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @  Eo  '/' '<<<'  '[' ∃∃  y1  ..  yn ,  '/' β  ']' '>>>'  '/' {{{  '[' z1  ..  zn ,  RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
(* No ∃∃ *)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e @ Eo '<<<' β '>>>' {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ, P -∗ (|={⊤∖Eo%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ (β -∗ |={∅,⊤∖Eo}=> ∀ z1, .. (∀ zn, Q -∗ Φ v%V) .. )) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, z1 closed binder, zn closed binder,
   format "'[hv' {{{  '[' P  ']' } } }  '/' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @  Eo  '/' '<<<'  '[' β  ']' '>>>'  '/' {{{  '[' z1  ..  zn ,  RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
(* No ∃∃, no RET binders *)
Notation "'{{{' P } } } '<<<' ∀∀ x1 .. xn , α '>>>' e @ Eo '<<<' β '>>>' {{{ 'RET' v ; Q } } }" :=
  (□ ∀ Φ, P -∗ (|={⊤∖Eo%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ (β -∗ |={∅,⊤∖Eo}=> Q -∗ Φ v%V)) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder,
   format "'[hv' {{{  '[' P  ']' } } }  '/' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  '/' @  Eo  '/' '<<<'  '[' β  ']' '>>>'  '/' {{{  '[' RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
(* No P, no ∃∃ *)
Notation "'<<<' ∀∀ x1 .. xn , α '>>>' e @ Eo '<<<' β '>>>' {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ, (|={⊤∖Eo%I%I,∅}=> ∃ x1, .. (∃ xn, α ∗ (β -∗ |={∅,⊤∖Eo}=> ∀ z1, .. (∀ zn, Q -∗ Φ v%V) .. )) .. ) -∗
   WP e @ ⊤ {{ Φ }})%I
  (at level 20, x1 closed binder, xn closed binder, z1 closed binder, zn closed binder,
   format "'[hv' '<<<'  '[' ∀∀  x1  ..  xn ,  α  ']' '>>>'  '/  ' e  '/' @  Eo  '/' '<<<'  '[' β  ']' '>>>'  '/' {{{  '[' z1  ..  zn ,  RET  v ;  '/' Q  ']' } } } ']'")
  : bi_scope.
