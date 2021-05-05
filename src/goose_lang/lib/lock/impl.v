From Perennial.goose_lang Require Export notation typing.

Definition lockRefT {ext} {ext_ty: ext_types ext} := refT boolT.
Definition condvarRefT {ext} {ext_ty: ext_types ext} := refT lockRefT.

Module lock.
  Section goose_lang.
    Context {ext:ffi_syntax}.

    Local Coercion Var' (s:string): expr := Var s.

    Definition new: val := λ: <>, ref #false.
    Definition try_acquire : val := λ: "l", CAS "l" #false #true.
    Definition acquire : val :=
      rec: "acquire" "l" := if: try_acquire "l" then #() else "acquire" "l".
    Definition release : val := λ: "l", CmpXchg "l" #true #false;; #().

    (* XXX: let binding so we can do an iMod after the allocation *)
    Definition newCond: val := λ: "l", let: "cond" := ref "l" in "cond".
    (* no-op in the model, only affects scheduling *)
    Definition condSignal: val := λ: "l", #().
    Definition condBroadcast: val := λ: "l", #().
    Definition condWait: val := λ: "l", release !"l";;
                                        (* actual cond var waits for a signal
                                           here, but the model does not take this
                                           into account *)
                                        acquire !"l".
    Definition condWaitTimeout: val := λ: "l" "timeout", condWait "l".
  End goose_lang.
End lock.
