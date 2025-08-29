From New.golang.defn Require Export typing.

Module ptrT. Definition id (t : go_string) : go_string := "*"%go ++ t. End ptrT.
Module chanT. Definition id (t : go_string) : go_string := "chan "%go ++ t. End chanT.
Module sliceT. Definition id (t : go_string) : go_string := "[]"%go ++ t. End sliceT.
Module mapT. Definition id (key elem : go_string) : go_string := "map["%go ++ key ++ "]"%go ++ elem. End mapT.
Module sendchanT. Definition id (t : go_string) : go_string := "chan<- "%go ++ t. End sendchanT.
Module recvchanT. Definition id (t : go_string) : go_string := "<-chan "%go ++ t. End recvchanT.
Module funcT.
Definition id (params : list go_string) (results: list go_string) (variadic : bool) : go_string
  := ("func(" ++
        (foldl (λ a paramTypeId, a ++ "," ++ paramTypeId) "" params) ++ (* has a leading comma *)
        (if variadic then "..." else "") ++
        ") ()" ++
        (foldl (λ a resultTypeId, a ++ "," ++ resultTypeId) "" results) (* has a leading comma *)
     )%go.
End funcT.
Module structT.
Definition id (fields : list (go_string * go_string)) : go_string
  := ("struct{" ++
        (foldl (λ a '(fieldName, fieldType), a ++ ";" ++ fieldName ++ " " ++ fieldType) "" fields) ++
        "}"
     )%go.
End structT.

Module stringT. Definition id : go_string := "string". End stringT.
Module boolT. Definition id : go_string := "bool". End boolT.

Module uint64T. Definition id : go_string := "uint64". End uint64T.
Module uint32T. Definition id : go_string := "uint32". End uint32T.
Module uint16T. Definition id : go_string := "uint16". End uint16T.
Module uint8T. Definition id : go_string := "uint8". End uint8T.

Module int64T. Definition id : go_string := "int64". End int64T.
Module int32T. Definition id : go_string := "int32". End int32T.
Module int16T. Definition id : go_string := "int16". End int16T.
Module int8T. Definition id : go_string := "int8". End int8T.

Module byteT. Definition id : go_string := uint8T.id. End byteT.
Module intT. Definition id : go_string := "int". End intT.
Module uintT. Definition id : go_string := "uint". End uintT.

#[global] Opaque ptrT.id chanT.id sendchanT.id recvchanT.id funcT.id structT.id sliceT.id.

#[global] Opaque
 stringT.id boolT.id uint64T.id uint32T.id uint16T.id uint8T.id int64T.id int32T.id int16T.id
 int8T.id byteT.id intT.id uintT.id.
