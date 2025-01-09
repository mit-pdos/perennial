(* autogenerated by goose axiom generator; do not modify *)
From New.golang Require Import defn.

Section axioms.
Context `{ffi_syntax}.

Axiom Ldate : Z.
Axiom Ltime : Z.
Axiom Lmicroseconds : Z.
Axiom Llongfile : Z.
Axiom Lshortfile : Z.
Axiom LUTC : Z.
Axiom Lmsgprefix : Z.
Axiom LstdFlags : Z.
Axiom Logger : go_type.
Axiom Logger__mset : list (go_string * val).
Axiom Logger__mset_ptr : list (go_string * val).
Axiom New : val.
Axiom Logger__SetOutput : val.
Axiom Default : val.
Axiom Logger__Output : val.
Axiom Logger__Print : val.
Axiom Logger__Printf : val.
Axiom Logger__Println : val.
Axiom Logger__Fatal : val.
Axiom Logger__Fatalf : val.
Axiom Logger__Fatalln : val.
Axiom Logger__Panic : val.
Axiom Logger__Panicf : val.
Axiom Logger__Panicln : val.
Axiom Logger__Flags : val.
Axiom Logger__SetFlags : val.
Axiom Logger__Prefix : val.
Axiom Logger__SetPrefix : val.
Axiom Logger__Writer : val.
Axiom SetOutput : val.
Axiom Flags : val.
Axiom SetFlags : val.
Axiom Prefix : val.
Axiom SetPrefix : val.
Axiom Writer : val.
Axiom Print : val.
Axiom Printf : val.
Axiom Println : val.
Axiom Fatal : val.
Axiom Fatalf : val.
Axiom Fatalln : val.
Axiom Panic : val.
Axiom Panicf : val.
Axiom Panicln : val.
Axiom Output : val.
Axiom initialize' : val.
End axioms.
