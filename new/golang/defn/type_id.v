From New.golang.defn Require Export typing.

Definition ptrTⁱᵈ (t : go_string) : go_string := "*"%go ++ t.
Definition chanTⁱᵈ (t : go_string) : go_string := "chan "%go ++ t.
Definition sliceTⁱᵈ (t : go_string) : go_string := "[]"%go ++ t.
Definition sendchanTⁱᵈ (t : go_string) : go_string := "chan<- "%go ++ t.
Definition recvchanTⁱᵈ (t : go_string) : go_string := "<-chan "%go ++ t.
Definition funcTⁱᵈ (params : list go_string) (results: list go_string) (variadic : go_string) : go_string
  := ("func(" ++
        (foldl (λ a paramTypeId, a ++ "," ++ paramTypeId) "" params) ++ (* has a leading comma *)
        (if variadic then "..." else "") ++
        ") ()" ++
        (foldl (λ a resultTypeId, a ++ "," ++ resultTypeId) "" results) (* has a leading comma *)
     )%go.
Definition structTⁱᵈ (fields : list (go_string * go_string)) : go_string
  := ("struct{" ++
        (foldl (λ a '(fieldName, fieldType), a ++ ";" ++ fieldName ++ " " ++ fieldType) "" fields) ++
        "}"
     )%go.

Definition stringTⁱᵈ : go_string := "string".
Definition boolTⁱᵈ : go_string := "bool".

Definition uint64Tⁱᵈ : go_string := "uint64".
Definition uint32Tⁱᵈ : go_string := "uint32".
Definition uint16Tⁱᵈ : go_string := "uint16".
Definition uint8Tⁱᵈ : go_string := "uint8".

Definition int64Tⁱᵈ : go_string := "int64".
Definition int32Tⁱᵈ : go_string := "int32".
Definition int16Tⁱᵈ : go_string := "int16".
Definition int8Tⁱᵈ : go_string := "int8".

Definition byteTⁱᵈ : go_string := uint8Tⁱᵈ.
Definition intTⁱᵈ : go_string := "int".
Definition uintTⁱᵈ : go_string := "uint".

#[global] Opaque ptrTⁱᵈ chanTⁱᵈ sendchanTⁱᵈ recvchanTⁱᵈ funcTⁱᵈ structTⁱᵈ sliceTⁱᵈ.

#[global] Opaque
 stringTⁱᵈ boolTⁱᵈ uint64Tⁱᵈ uint32Tⁱᵈ uint16Tⁱᵈ uint8Tⁱᵈ int64Tⁱᵈ int32Tⁱᵈ int16Tⁱᵈ
 int8Tⁱᵈ byteTⁱᵈ intTⁱᵈ uintTⁱᵈ.
