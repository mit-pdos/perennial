From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang.lib Require Import control.impl.
From Perennial.goose_lang.lib Require Import lock.impl.

(** * Channel library *)
Notation Channel chanref lock := (InjRV (PairV chanref lock)) (only parsing).
Notation NilChannelV := (InjLV #()) (only parsing).
Notation ChannelClosedV nullV := (InjLV nullV) (only parsing).
Notation ChannelOpenV cap eff_cap content := (InjRV (cap, eff_cap, content)) (only parsing).
Notation ChannelNilV nullV := (InjLV nullV) (only parsing).
Notation ChannelConsV elem content:= (InjRV (elem, content)) (only parsing).

Section goose_lang.
Context {ext:ffi_syntax}.
Context `{ext_ty: ext_types}.
Local Coercion Var' (s:string) : expr := Var s.

  (* 
  infinite loop for nil channels
  
  Definition Assume: val :=
  λ: "cond", if: Var "cond" then #()
             else (rec: "loop" <> := Var "loop" #()) #(). *)

(* return value: (return element, channel is open, return is valid) *)
Definition InnerReceive: val :=
  λ: "chanref",
  (rec: "chanRec" "c" :=
    match: "c" with
      InjL "nullV" => ("nullV", #false, #true)
    | InjR "capcon" =>
        let: "cap" := Fst (Fst "capcon") in
        let: "eff_cap" := Snd (Fst "capcon") in
        let: "con" := Snd "capcon" in
        match: "con" with
          InjL "nullV" => ("nullV", #true, #false)
        | InjR "elemcon" =>
          let: "elem" := Fst "elemcon" in
          let: "con" := Snd "elemcon" in
          "chanref" <- InjR ("cap", "eff_cap", "con");;
          ("elem", #true, #true)
        end
  end) (!"chanref").

Definition IncCap: val :=
  λ: "chanref",
    let: "c" := !"chanref" in
    match: "c" with 
      InjL "nullV" => #()
    | InjR "capcon" =>
      let: "cap" := Fst (Fst "capcon") in
      let: "eff_cap" := Snd (Fst "capcon") in
      let: "con" := Snd "capcon" in
      "chanref" <- InjR ("cap", (#1 + "eff_cap"), "con")
    end.

Definition DecCap: val :=
  λ: "chanref",
    let: "c" := !"chanref" in
    match: "c" with 
      InjL "nullV" => #()
    | InjR "capcon" =>
      let: "cap" := Fst (Fst "capcon") in
      let: "eff_cap" := Snd (Fst "capcon") in
      let: "con" := Snd "capcon" in
      "chanref" <- InjR ("cap", "eff_cap" - #1, "con")
    end.

Definition TryReceive: val :=
  λ: "channel",
      let: "chanref" := Fst "channel" in
      let: "lock" := Snd "channel" in
      lock.acquire "lock";;
      match: (! "chanref") with
        InjL "nullV" => let: "r" := InnerReceive "chanref" in lock.release "lock";;"r"
      | InjR "capcon" =>
          IncCap "chanref";;
          lock.release "lock";;
          lock.acquire "lock";;
          let: "r" := InnerReceive "chanref" in
          DecCap "chanref";;
          lock.release "lock";;
          "r"
      end.

Definition ChannelReceive: val :=
  λ: "channel",
  (rec: "chanRec" "c" :=
    let: "r" := TryReceive "c" in
    let: "v" := Fst ("r") in
    let: "open" := Fst (Snd "r") in
    let: "valid" := Snd (Snd "r") in
    if: "valid" then ("v", "open")
    else "chanRec" ("c")
  ) ("channel").

  Definition ChanLen': val :=
    λ: "chancon",
    (rec: "chanLen" "c" :=
     match: "c" with
       InjL "empty" => #0
     | InjR "content" => #1 + "chanLen" (Snd "content")
     end) ("chancon").

(* Not the same spec as Go's chan length function *)
(* Fix len, shouldn't return more than channel's cap *)
  Definition ChanLen: val :=
    λ: "channel",
      let: "chanref" := Fst "channel" in
      let: "lock" := Snd "channel" in
      lock.acquire "lock";;
      let: "r" := (rec: "chanLen" "c" :=
        match: "c" with
         InjL "closed" => (#0, #false)
        |InjR "capcon" =>
        let: "con" := (Snd "capcon") in (ChanLen' "con", #true)
      end) (!"chanref") in (lock.release "lock";; "r").

  Definition ChanAppend: val :=
    λ: "con" "v",
    (rec: "chanAppend" "con" :=
      match: "con" with
        InjL "empty" => InjR ("v", InjL "empty")
      | InjR "elemCon" => 
        let: "elem" := Fst "elemCon" in
        let: "con2" := Snd "elemCon" in
        InjR ("elem", "chanAppend" "con2")
      end
    ) ("con").

  Definition TrySend: val :=
    λ: "channel" "v",
      let: "chanref" := Fst "channel" in
      let: "lock" := Snd "channel" in
      lock.acquire "lock";;
      match: (! "chanref") with 
        InjL "nullV" => Panic ("sending on closed channel")
        | InjR "capcon" =>
          let: "cap" := Fst (Fst "capcon") in
          let: "eff_cap" := Snd (Fst "capcon") in
          let: "con" := Snd "capcon" in
          let: "r" := ChanLen "channel" in
          let: "len" := Fst ("r") in
          if: "eff_cap" > "len" then 
            "chanref" <- InjR ("cap", "eff_cap", ChanAppend "con");;
            lock.release "lock";;#true
          else lock.release "lock";;#false
    end.

  Definition ChannelSend: val :=
    λ: "chanref" "v",
    (rec: "chanSend" "c" :=
    match: "c" with
      InjL "nullV" => Panic ("sending on closed channel")
    | InjR "capcon" =>
        let: "r" := TrySend "chanref" "v" in
        let: "valid" := Snd "r" in
        if: "valid" then #true
        else "chanSend" "c"
  end) (!"chanref").


End goose_lang.