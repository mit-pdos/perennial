
Definition is_interface_type `{!GoLocalContext} (t : go.type) : bool :=
  match (to_underlying t) with
  | go.InterfaceType _ => true
  | _ => false
  end.

(* Based on: https://go.dev/ref/spec#General_interfaces *)
Definition type_set_term_contains {go_ctx : GoLocalContext} t (e : go.type_term) : bool :=
  match e with
  | go.TypeTerm t' => bool_decide (t = t')
  | go.TypeTermUnderlying t' => bool_decide (to_underlying t = t')
  end.

Definition type_set_elem_contains {go_ctx : GoLocalContext} t (e : go.interface_elem) : bool :=
  match e with
  | go.MethodElem m signature => bool_decide (method_set t !! m = Some signature)
  | go.TypeElem terms => existsb (type_set_term_contains t) terms
  end.

Definition type_set_elems_contains {go_ctx : GoLocalContext} t (elems : list go.interface_elem) : bool :=
  forallb (type_set_elem_contains t) elems.

(** Equals [true] iff t is in the type set of t'. *)
Definition type_set_contains {go_ctx : GoLocalContext} t t' : bool :=
  match (to_underlying t') with
  | go.InterfaceType elems => type_set_elems_contains t elems
  | _ => bool_decide (t = t')
  end.




Inductive is_go_step_pure `{!GoGlobalContext} `{!GoLocalContext} :
  ∀ (op : go_instruction) (arg : val) (e' : expr), Prop :=
| angelic_exit_step : is_go_step_pure AngelicExit #() (GoInstruction AngelicExit #())%E
| equals_step t v1 v2 :
  is_go_step_pure (GoEquals t) (v1, v2)%V (go_eq_top_level t v1 v2)
| lt_step t v1 v2 :
  is_go_step_pure (GoLt t) (v1, v2)%V (go_lt t v1 v2)
| le_step t v1 v2 :
  is_go_step_pure (GoLe t) (v1, v2)%V (go_le t v1 v2)
| gt_step t v1 v2 :
  is_go_step_pure (GoGt t) (v1, v2)%V (go_lt t v2 v1)
| ge_step t v1 v2 :
  is_go_step_pure (GoGe t) (v1, v2)%V (go_le t v2 v1)
| plus_step t v1 v2 :
  is_go_step_pure (GoPlus t) (v1, v2)%V (go_plus t v1 v2)
| sub_step t v1 v2 :
  is_go_step_pure (GoSub t) (v1, v2)%V (go_sub t v1 v2)
| mul_step t v1 v2 :
  is_go_step_pure (GoMul t) (v1, v2)%V (go_mul t v1 v2)
| div_step t v1 v2 :
  is_go_step_pure (GoDiv t) (v1, v2)%V (go_div t v1 v2)
| rem_step t v1 v2 :
  is_go_step_pure (GoRemainder t) (v1, v2)%V (go_remainder t v1 v2)
| and_step t v1 v2 :
  is_go_step_pure (GoAnd t) (v1, v2)%V (go_and t v1 v2)
| or_step t v1 v2 :
  is_go_step_pure (GoOr t) (v1, v2)%V (go_or t v1 v2)
| xor_step t v1 v2 :
  is_go_step_pure (GoXor t) (v1, v2)%V (go_xor t v1 v2)
| bitclear_step t v1 v2 :
  is_go_step_pure (GoBitClear t) (v1, v2)%V (go_bitclear t v1 v2)
| shiftl_step t v1 v2 :
  is_go_step_pure (GoShiftl t) (v1, v2)%V (go_shiftl t v1 v2)
| shiftr_step t v1 v2 :
  is_go_step_pure (GoShiftr t) (v1, v2)%V (go_shiftr t v1 v2)

| load_step t arg : is_go_step_pure (GoLoad t) arg (load t arg)
| store_step t (l : loc) v : is_go_step_pure (GoStore t) (#l, v)%V (store t #l v)
| alloc_step t : is_go_step_pure (GoAlloc t) #() (alloc t #())%E
| prealloc_step (l : loc) : is_go_step_pure GoPrealloc #() #l
| func_resolve_step f targs : is_go_step_pure (FuncResolve f targs) #() #(functions f targs)
| method_resolve_step t m : is_go_step_pure (MethodResolve t m) #() #(methods t m)
| interface_make_step dt v :
  is_go_step_pure (InterfaceMake dt) v #(interface.mk dt v)
| interface_get_step m i :
  is_go_step_pure (InterfaceGet m) #i
    (match i with
     | interface.nil => Panic "nil dereference in interface call"
     | interface.mk t v => (GoInstruction (MethodResolve t m) #() v)%E
     end)
| type_assert_step t i :
  is_go_step_pure (TypeAssert t) #i
    (match i with
     | interface.nil => Panic "type assert failed"
     | interface.mk dt v =>
         if is_interface_type t then
           (if (type_set_contains dt t) then #i else Panic "type assert failed")
         else
           (if decide (t = dt) then v else Panic "type assert failed")
     end)
| type_assert2_step t i :
  is_go_step_pure (TypeAssert2 t) #i
    (match i with
     | interface.nil => (#interface.nil, #false)%V
     | interface.mk dt v =>
         if is_interface_type t then
           (if (type_set_contains dt t) then (#i, #true)%V else (#interface.nil, #false)%V)
         else
           (if decide (t = dt) then (v, #true)%V else (go_zero_val t, #false)%E)
     end)
| global_var_addr_step v : is_go_step_pure (GlobalVarAddr v) #() #(global_addr v)
| struct_field_ref_step t f l : is_go_step_pure (StructFieldRef t f) #l #(struct_field_ref t f l)
| struct_field_get_step t f v :
  is_go_step_pure (StructFieldGet t f) v (struct_field_get t f v)
| struct_field_set_step t f v vf :
  is_go_step_pure (StructFieldSet t f) (v, vf) (struct_field_set t f v vf)

| internal_len_slice_step_pure elem_type s :
  is_go_step_pure (InternalLen (go.SliceType elem_type)) #s #(s.(slice.len))
| internal_len_array_step_pure elem_type n v :
  is_go_step_pure (InternalLen (go.ArrayType n elem_type)) v #(W64 n)

| internal_cap_slice_step_pure elem_type s :
  is_go_step_pure (InternalCap (go.SliceType elem_type)) #s #(s.(slice.cap))
| internal_dynamic_array_alloc_pure elem_type (n : w64) :
  is_go_step_pure (InternalDynamicArrayAlloc elem_type) #n
    (GoInstruction (GoAlloc $ go.ArrayType (sint.Z n) elem_type) #())
| internal_slice_make_pure p l c :
  is_go_step_pure InternalMakeSlice (#p, #l, #c) #(slice.mk p l c)
| slice_array_step_pure n elem_type p low high:
  is_go_step_pure (Slice (go.ArrayType n elem_type))
    (#p, (#low, #high))%V
    (if decide (0 ≤ sint.Z low ≤ sint.Z high ≤ n) then
       #(slice.mk (array_index_ref elem_type (sint.Z low) p)
           (word.sub high low) (word.sub (W64 n) low))
     else Panic "slice bounds out of range")
| full_slice_array_step_pure n elem_type p low high max :
  is_go_step_pure (FullSlice (go.ArrayType n elem_type))
    (#p, (#low, #high, #max))%V
    (if decide (0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z max ∧ sint.Z max ≤ n) then
       #(slice.mk (array_index_ref elem_type (sint.Z low) p)
           (word.sub high low) (word.sub max low))
     else Panic "slice bounds out of range")
| slice_slice_step_pure elem_type s low high :
  is_go_step_pure (Slice (go.SliceType elem_type))
    (#s, (#low, #high))%V
    (if decide (0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z s.(slice.cap)) then
       #(slice.mk (array_index_ref elem_type (sint.Z low) s.(slice.ptr))
           (word.sub high low) (word.sub s.(slice.cap) low))
     else Panic "slice bounds out of range")
| full_slice_slice_step_pure elem_type s low high max :
  is_go_step_pure (FullSlice (go.SliceType elem_type))
    (#s, (#low, #high, #max))%V
    (if decide (0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z max ∧ sint.Z max ≤ sint.Z s.(slice.cap)) then
       #(slice.mk (array_index_ref elem_type (sint.Z low) s.(slice.ptr))
           (word.sub high low) (word.sub max low))
     else Panic "slice bounds out of range")
| index_ref_step t v (j : w64) : is_go_step_pure (IndexRef t) (v, #j) (index_ref t (sint.Z j) v)
| index_step t v (j : w64) : is_go_step_pure (Index t) (v, #j) (index t (sint.Z j) v)
| array_set_step_pure ty V n (l : array.t ty V n) (v : V) (i : w64) :
  is_go_step_pure ArraySet (#l, (#i, #v))%V #(array.mk ty n (<[sint.nat i := v ]> (array.arr l)))
| array_length_step_pure l :
  is_go_step_pure ArrayLength (ArrayV l)
    (if decide (length l < 2^63) then
       #(W64 (length l))
     else (GoInstruction AngelicExit #()))
| internal_map_lookup_step_pure m k :
  is_go_step_pure InternalMapLookup (m, k) (let '(ok, v) := map_lookup m k in (v, #ok))
| internal_map_insert_step_pure m k v :
  is_go_step_pure InternalMapInsert (m, k, v) (map_insert m k v)
| internal_map_delete_step_pure m k :
  is_go_step_pure InternalMapDelete (m, k) (map_delete m k)
| internal_map_length_step_pure m ks (H : is_map_domain m ks) :
  is_go_step_pure InternalMapLength m #(W64 (length ks))
| internal_map_domain_literal_step_pure m ks (H : is_map_domain m ks) :
  is_go_step_pure InternalMapDomainLiteral m
    (LiteralValue ((λ v, KeyedElement None $ ElementExpression $ Val v) <$> ks))
| internal_map_make_step_pure v :
  is_go_step_pure InternalMapMake v (map_empty v)
| composite_literal_step t v :
  is_go_step_pure (CompositeLiteral t) v (composite_literal t v)
.


  method_interface t m (H : is_interface_type t = true) :
    #(methods t m) = (InterfaceGet m);




    go_eq_top_level := inhabitant;
    go_lt := inhabitant;
    go_le := inhabitant;
    go_plus := inhabitant;
    go_sub := inhabitant;
    go_mul := inhabitant;
    go_div := inhabitant;
    go_remainder := inhabitant;
    go_and := inhabitant;
    go_or := inhabitant;
    go_xor := inhabitant;
    go_bitclear := inhabitant;
    go_shiftl := inhabitant;
    go_shiftr := inhabitant;
    global_addr := inhabitant;
    functions := inhabitant;
    methods := inhabitant;
    method_set := inhabitant;
    alloc := inhabitant;
    load := inhabitant;
    store := inhabitant;
    go_zero_val := inhabitant;
    struct_field_ref := inhabitant;
    struct_field_get := inhabitant;
    struct_field_set := inhabitant;
    index := inhabitant;
    index_ref := inhabitant;
    array_index_ref := inhabitant;
    to_underlying := inhabitant;
    map_empty := inhabitant;
    map_lookup := inhabitant;
    map_insert := inhabitant;
    map_delete := inhabitant;
    is_map_domain := inhabitant;
    composite_literal := inhabitant;
  |}.


Global Instance pure_wp_TypeAssert_non_interface t v :
  PureWp (is_interface_type t = false) (TypeAssert t #(interface.mk t v)) v.
Proof.
  iIntros "% * %Heq % HΦ"; iApply wp_GoInstruction; [ intros; repeat econstructor |  ]; iNext.
  iIntros "* %Hstep Hlc". inv Hstep. inv Hpure. iIntros "$ !>".
  simpl. rewrite Heq. rewrite decide_True //. by iApply "HΦ".
Qed.

Global Instance pure_wp_TypeAssert_interface t dt v :
  PureWp (is_interface_type t = true ∧ type_set_contains dt t = true)
    (TypeAssert t #(interface.mk dt v)) #(interface.mk dt v).
Proof.
  iIntros "% * %Heq % HΦ"; iApply wp_GoInstruction; [ intros; repeat econstructor |  ]; iNext.
  iIntros "* %Hstep Hlc". inv Hstep. inv Hpure. iIntros "$ !>".
  simpl. destruct Heq as [-> Hcontains]. rewrite Hcontains. by iApply "HΦ".
Qed.

Global Instance pure_wp_TypeAssert2_non_interface t t' `{!ZeroVal V}
                `{!go.GoZeroValEq t V} `{!TypedPointsto V} `{!IntoValTyped V t} (v : V) :
  PureWp (is_interface_type t = false)
    (TypeAssert2 t #(interface.mk t' #v))
    (if decide (t = t') then (#v, #true)%V else (#(zero_val V), #false)%V).
Proof.
  iIntros "% * %Heq % HΦ"; iApply wp_GoInstruction; [ intros; repeat econstructor |  ]; iNext.
  iIntros "* %Hstep Hlc". inv Hstep. inv Hpure. iIntros "$ !>".
  simpl. rewrite Heq. destruct decide.
  - by iApply "HΦ".
  - rewrite go.go_zero_val_eq. wp_pures. by iApply "HΦ".
Qed.

Global Instance pure_wp_TypeAssert2_interface t i :
  PureWp (is_interface_type t = true)
    (TypeAssert2 t #i)
    (match i with
     | interface.mk dt v =>
         if type_set_contains dt t then (# i, # true)%V else (# interface.nil, # false)%V
     | interface.nil => (# interface.nil, # false)%V
     end).
Proof.
  iIntros "% * %Heq % HΦ"; iApply wp_GoInstruction; [ intros; repeat econstructor |  ]; iNext.
  iIntros "* %Hstep Hlc". inv Hstep. inv Hpure. iIntros "$ !>".
  simpl. rewrite Heq. destruct i.
  - by iApply "HΦ".
  - by iApply "HΦ".
Qed.
