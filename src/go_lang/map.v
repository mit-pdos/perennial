From stdpp Require Import fin_maps gmap.
From Perennial.go_lang Require Import lang notation.

Notation MapConsV k v m := (InjRV (PairV (PairV (LitV (LitInt k)) v) m)).
Notation MapNilV def := (InjLV def).
Notation AllocMap v := (Alloc (MapNilV v)) (only parsing).

Section go_lang.
  Context {ext:ext_op}.
  Local Coercion Var' (s:string) : expr := Var s.

Fixpoint map_val (v: val) : option (gmap u64 val * val) :=
  match v with
  | MapConsV k v m =>
    match map_val m with
    | Some (m, def) => Some (<[ k := v ]> m, def)
    | None => None
    end
  | MapNilV def => Some (∅, def)
  | _ => None
  end.

Definition val_of_map (m_def: gmap u64 val * val) : val :=
  let (m, def) := m_def in
  fold_right (λ '(k, v) mv, MapConsV k v mv)
             (MapNilV def)
             (map_to_list m).

Theorem map_val_id : forall v m_def,
    map_val v = Some m_def ->
    val_of_map m_def = v.
Proof.
  induction v; intros [m def]; try solve [ inversion 1 ]; simpl; intros H.
  - inversion H; subst; clear H.
    rewrite map_to_list_empty; simpl; auto.
  - destruct v; try congruence.
    destruct v1; try congruence.
    destruct v1_1; try congruence.
    destruct l; try congruence.
    destruct_with_eqn (map_val v2); try congruence.
    specialize (IHv p).
    destruct p as [m' def'].
    inversion H; subst; clear H.
    (* oops, the normal val induction principle is too weak to prove this *)
Abort.

Definition map_get (m_def: gmap u64 val * val) (k: u64) : (val*bool) :=
  let (m, def) := m_def in
  let r := default def (m !! k) in
  let ok := bool_decide (is_Some (m !! k)) in
  (r, ok).

Definition map_insert (m_def: gmap u64 val * val) (k: u64) (v: val) : gmap u64 val * val :=
  let (m, def) := m_def in
  (<[ k := v ]> m, def).

Definition MapGet: val :=
  λ: "mref" "k",
  (rec: "mapGet" "m" :=
     match: "m" with
       InjL "def" => ("def", #false)
     | InjR "kvm" =>
       let: "kv" := Fst "kvm" in
       let: "m2" := Snd "kvm" in
       if: "k" = (Fst "kv") then (Snd "kv", #true)
       else "mapGet" "m2"
     end) (!"mref").

Definition MapInsert: val :=
  λ: "mref" "k" "v",
  "mref" <- InjR ("k", "v", !"mref").

Definition mapGetDef: val :=
  rec: "mapGetDef" "m" :=
     match: "m" with
       InjL "def" => "def"
     | InjR "kvm" =>
       "mapGetDef" (Snd "kvm")
     end.

Definition MapClear: val :=
  λ: "mref",
  let: "def" := mapGetDef !"mref" in
  "mref" <- InjL "def".

End go_lang.
