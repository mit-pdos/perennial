/-
Tests for `go!"..."` literals (not imported by the umbrella `Perennial.lean`).

Lean string literals have no `\a`, `\b`, `\f`, `\v` escapes; the tests of
those use the equivalent hex escapes `\x07`, `\x08`, `\x0c`, `\x0b`.
-/
import Perennial.Std.ByteString

namespace Perennial.ByteStringTest

example : go!"\n" = [W8 10] := rfl
example : (go!"\n").length = 1 := rfl

example : go!"\t" = [W8 9] := rfl
example : (go!"\t").length = 1 := rfl

example : go!"\r" = [W8 13] := rfl
example : (go!"\r").length = 1 := rfl

example : go!"\\" = [W8 92] := rfl
example : (go!"\\").length = 1 := rfl

example : go!"\"" = [W8 34] := rfl
example : (go!"\"").length = 1 := rfl

example : go!"\x07" = [W8 7] := rfl
example : (go!"\x07").length = 1 := rfl

example : go!"\x08" = [W8 8] := rfl
example : (go!"\x08").length = 1 := rfl

example : go!"\x0c" = [W8 12] := rfl
example : (go!"\x0c").length = 1 := rfl

example : go!"\x0b" = [W8 11] := rfl
example : (go!"\x0b").length = 1 := rfl

example : go!"foo\nbar" = [W8 102, W8 111, W8 111, W8 10, W8 98, W8 97, W8 114] := rfl
example : (go!"foo\nbar").length = 7 := rfl

example : go!"\t\n\r" = [W8 9, W8 10, W8 13] := rfl
example : (go!"\t\n\r").length = 3 := rfl

example : go!"a\tb" = [W8 97, W8 9, W8 98] := rfl
example : (go!"a\tb").length = 3 := rfl

example : go!"foo\n" = [W8 102, W8 111, W8 111, W8 10] := rfl
example : (go!"foo\n").length = 4 := rfl

example : go!"\nfoo" = [W8 10, W8 102, W8 111, W8 111] := rfl
example : (go!"\nfoo").length = 4 := rfl

example : go!"\n\n\n" = [W8 10, W8 10, W8 10] := rfl
example : (go!"\n\n\n").length = 3 := rfl

example : go!"hello" = [W8 104, W8 101, W8 108, W8 108, W8 111] := rfl
example : (go!"hello").length = 5 := rfl

example : go!"" = [] := rfl
example : (go!"").length = 0 := rfl

example : go!"AB\"" = [W8 65, W8 66, W8 34] := rfl

example : go!"\x07\x08\x0c\n\r\t\x0b\\\"" =
    [W8 7, W8 8, W8 12, W8 10, W8 13, W8 9, W8 11, W8 92, W8 34] := rfl
example : (go!"\x07\x08\x0c\n\r\t\x0b\\\"").length = 9 := rfl

/-- Non-ASCII characters are UTF-8 encoded (as Go source strings are). -/
example : go!"é" = [W8 0xc3, W8 0xa9] := rfl

end Perennial.ByteStringTest
