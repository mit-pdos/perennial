From Perennial.goose_lang Require Export ffi.grove_prelude notation.

(* FIXME: write the stubs here. *)
Definition GetTimeRange := grove_ffi.GetTimeRange.
Definition Listen := grove_ffi.Listen.
Definition Connect := grove_ffi.Connect.
Definition Accept := grove_ffi.Accept.
Definition Send := grove_ffi.Send.
Definition Receive := grove_ffi.Receive.
Definition FileWrite := grove_ffi.FileWrite.
Definition FileRead := grove_ffi.FileRead.
Definition FileAppend := grove_ffi.FileAppend.
Definition AddressToStr : val := (λ: "address" , #(str "PLACEHOLDER STRING")).
