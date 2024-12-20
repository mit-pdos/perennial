From stdpp Require Import base decidable.
From Perennial.Helpers Require Import Integers bytes.
From Coq Require Import ZArith Strings.Byte.

From Coq Require Import ssreflect.

#[local] Open Scope Z_scope.

(* Parse Coq string syntax directly to [list w8], in preparation for making
GooseLang string literals represented as [list w8] rather than [String] from the
standard library. *)

Definition byte_to_w8 (b: byte) : w8 :=
  match b with
(* python3 -c 'print("".join(f"| x{n:02x} => W8 {n} " for n in range(0, 256)))' *)
  | x00 => W8 0 | x01 => W8 1 | x02 => W8 2 | x03 => W8 3 | x04 => W8 4 | x05 => W8 5 | x06 => W8 6 | x07 => W8 7 | x08 => W8 8 | x09 => W8 9 | x0a => W8 10 | x0b => W8 11 | x0c => W8 12 | x0d => W8 13 | x0e => W8 14 | x0f => W8 15 | x10 => W8 16 | x11 => W8 17 | x12 => W8 18 | x13 => W8 19 | x14 => W8 20 | x15 => W8 21 | x16 => W8 22 | x17 => W8 23 | x18 => W8 24 | x19 => W8 25 | x1a => W8 26 | x1b => W8 27 | x1c => W8 28 | x1d => W8 29 | x1e => W8 30 | x1f => W8 31 | x20 => W8 32 | x21 => W8 33 | x22 => W8 34 | x23 => W8 35 | x24 => W8 36 | x25 => W8 37 | x26 => W8 38 | x27 => W8 39 | x28 => W8 40 | x29 => W8 41 | x2a => W8 42 | x2b => W8 43 | x2c => W8 44 | x2d => W8 45 | x2e => W8 46 | x2f => W8 47 | x30 => W8 48 | x31 => W8 49 | x32 => W8 50 | x33 => W8 51 | x34 => W8 52 | x35 => W8 53 | x36 => W8 54 | x37 => W8 55 | x38 => W8 56 | x39 => W8 57 | x3a => W8 58 | x3b => W8 59 | x3c => W8 60 | x3d => W8 61 | x3e => W8 62 | x3f => W8 63 | x40 => W8 64 | x41 => W8 65 | x42 => W8 66 | x43 => W8 67 | x44 => W8 68 | x45 => W8 69 | x46 => W8 70 | x47 => W8 71 | x48 => W8 72 | x49 => W8 73 | x4a => W8 74 | x4b => W8 75 | x4c => W8 76 | x4d => W8 77 | x4e => W8 78 | x4f => W8 79 | x50 => W8 80 | x51 => W8 81 | x52 => W8 82 | x53 => W8 83 | x54 => W8 84 | x55 => W8 85 | x56 => W8 86 | x57 => W8 87 | x58 => W8 88 | x59 => W8 89 | x5a => W8 90 | x5b => W8 91 | x5c => W8 92 | x5d => W8 93 | x5e => W8 94 | x5f => W8 95 | x60 => W8 96 | x61 => W8 97 | x62 => W8 98 | x63 => W8 99 | x64 => W8 100 | x65 => W8 101 | x66 => W8 102 | x67 => W8 103 | x68 => W8 104 | x69 => W8 105 | x6a => W8 106 | x6b => W8 107 | x6c => W8 108 | x6d => W8 109 | x6e => W8 110 | x6f => W8 111 | x70 => W8 112 | x71 => W8 113 | x72 => W8 114 | x73 => W8 115 | x74 => W8 116 | x75 => W8 117 | x76 => W8 118 | x77 => W8 119 | x78 => W8 120 | x79 => W8 121 | x7a => W8 122 | x7b => W8 123 | x7c => W8 124 | x7d => W8 125 | x7e => W8 126 | x7f => W8 127 | x80 => W8 128 | x81 => W8 129 | x82 => W8 130 | x83 => W8 131 | x84 => W8 132 | x85 => W8 133 | x86 => W8 134 | x87 => W8 135 | x88 => W8 136 | x89 => W8 137 | x8a => W8 138 | x8b => W8 139 | x8c => W8 140 | x8d => W8 141 | x8e => W8 142 | x8f => W8 143 | x90 => W8 144 | x91 => W8 145 | x92 => W8 146 | x93 => W8 147 | x94 => W8 148 | x95 => W8 149 | x96 => W8 150 | x97 => W8 151 | x98 => W8 152 | x99 => W8 153 | x9a => W8 154 | x9b => W8 155 | x9c => W8 156 | x9d => W8 157 | x9e => W8 158 | x9f => W8 159 | xa0 => W8 160 | xa1 => W8 161 | xa2 => W8 162 | xa3 => W8 163 | xa4 => W8 164 | xa5 => W8 165 | xa6 => W8 166 | xa7 => W8 167 | xa8 => W8 168 | xa9 => W8 169 | xaa => W8 170 | xab => W8 171 | xac => W8 172 | xad => W8 173 | xae => W8 174 | xaf => W8 175 | xb0 => W8 176 | xb1 => W8 177 | xb2 => W8 178 | xb3 => W8 179 | xb4 => W8 180 | xb5 => W8 181 | xb6 => W8 182 | xb7 => W8 183 | xb8 => W8 184 | xb9 => W8 185 | xba => W8 186 | xbb => W8 187 | xbc => W8 188 | xbd => W8 189 | xbe => W8 190 | xbf => W8 191 | xc0 => W8 192 | xc1 => W8 193 | xc2 => W8 194 | xc3 => W8 195 | xc4 => W8 196 | xc5 => W8 197 | xc6 => W8 198 | xc7 => W8 199 | xc8 => W8 200 | xc9 => W8 201 | xca => W8 202 | xcb => W8 203 | xcc => W8 204 | xcd => W8 205 | xce => W8 206 | xcf => W8 207 | xd0 => W8 208 | xd1 => W8 209 | xd2 => W8 210 | xd3 => W8 211 | xd4 => W8 212 | xd5 => W8 213 | xd6 => W8 214 | xd7 => W8 215 | xd8 => W8 216 | xd9 => W8 217 | xda => W8 218 | xdb => W8 219 | xdc => W8 220 | xdd => W8 221 | xde => W8 222 | xdf => W8 223 | xe0 => W8 224 | xe1 => W8 225 | xe2 => W8 226 | xe3 => W8 227 | xe4 => W8 228 | xe5 => W8 229 | xe6 => W8 230 | xe7 => W8 231 | xe8 => W8 232 | xe9 => W8 233 | xea => W8 234 | xeb => W8 235 | xec => W8 236 | xed => W8 237 | xee => W8 238 | xef => W8 239 | xf0 => W8 240 | xf1 => W8 241 | xf2 => W8 242 | xf3 => W8 243 | xf4 => W8 244 | xf5 => W8 245 | xf6 => W8 246 | xf7 => W8 247 | xf8 => W8 248 | xf9 => W8 249 | xfa => W8 250 | xfb => W8 251 | xfc => W8 252 | xfd => W8 253 | xfe => W8 254 | xff => W8 255
  end.

Definition w8_to_byte (w: w8) : byte :=
  match uint.Z w with
  (* python3 -c 'print("".join(f"| {n} => x{n:02x} " for n in range(0, 256)))' *)
  | 0 => x00 | 1 => x01 | 2 => x02 | 3 => x03 | 4 => x04 | 5 => x05 | 6 => x06 | 7 => x07 | 8 => x08 | 9 => x09 | 10 => x0a | 11 => x0b | 12 => x0c | 13 => x0d | 14 => x0e | 15 => x0f | 16 => x10 | 17 => x11 | 18 => x12 | 19 => x13 | 20 => x14 | 21 => x15 | 22 => x16 | 23 => x17 | 24 => x18 | 25 => x19 | 26 => x1a | 27 => x1b | 28 => x1c | 29 => x1d | 30 => x1e | 31 => x1f | 32 => x20 | 33 => x21 | 34 => x22 | 35 => x23 | 36 => x24 | 37 => x25 | 38 => x26 | 39 => x27 | 40 => x28 | 41 => x29 | 42 => x2a | 43 => x2b | 44 => x2c | 45 => x2d | 46 => x2e | 47 => x2f | 48 => x30 | 49 => x31 | 50 => x32 | 51 => x33 | 52 => x34 | 53 => x35 | 54 => x36 | 55 => x37 | 56 => x38 | 57 => x39 | 58 => x3a | 59 => x3b | 60 => x3c | 61 => x3d | 62 => x3e | 63 => x3f | 64 => x40 | 65 => x41 | 66 => x42 | 67 => x43 | 68 => x44 | 69 => x45 | 70 => x46 | 71 => x47 | 72 => x48 | 73 => x49 | 74 => x4a | 75 => x4b | 76 => x4c | 77 => x4d | 78 => x4e | 79 => x4f | 80 => x50 | 81 => x51 | 82 => x52 | 83 => x53 | 84 => x54 | 85 => x55 | 86 => x56 | 87 => x57 | 88 => x58 | 89 => x59 | 90 => x5a | 91 => x5b | 92 => x5c | 93 => x5d | 94 => x5e | 95 => x5f | 96 => x60 | 97 => x61 | 98 => x62 | 99 => x63 | 100 => x64 | 101 => x65 | 102 => x66 | 103 => x67 | 104 => x68 | 105 => x69 | 106 => x6a | 107 => x6b | 108 => x6c | 109 => x6d | 110 => x6e | 111 => x6f | 112 => x70 | 113 => x71 | 114 => x72 | 115 => x73 | 116 => x74 | 117 => x75 | 118 => x76 | 119 => x77 | 120 => x78 | 121 => x79 | 122 => x7a | 123 => x7b | 124 => x7c | 125 => x7d | 126 => x7e | 127 => x7f | 128 => x80 | 129 => x81 | 130 => x82 | 131 => x83 | 132 => x84 | 133 => x85 | 134 => x86 | 135 => x87 | 136 => x88 | 137 => x89 | 138 => x8a | 139 => x8b | 140 => x8c | 141 => x8d | 142 => x8e | 143 => x8f | 144 => x90 | 145 => x91 | 146 => x92 | 147 => x93 | 148 => x94 | 149 => x95 | 150 => x96 | 151 => x97 | 152 => x98 | 153 => x99 | 154 => x9a | 155 => x9b | 156 => x9c | 157 => x9d | 158 => x9e | 159 => x9f | 160 => xa0 | 161 => xa1 | 162 => xa2 | 163 => xa3 | 164 => xa4 | 165 => xa5 | 166 => xa6 | 167 => xa7 | 168 => xa8 | 169 => xa9 | 170 => xaa | 171 => xab | 172 => xac | 173 => xad | 174 => xae | 175 => xaf | 176 => xb0 | 177 => xb1 | 178 => xb2 | 179 => xb3 | 180 => xb4 | 181 => xb5 | 182 => xb6 | 183 => xb7 | 184 => xb8 | 185 => xb9 | 186 => xba | 187 => xbb | 188 => xbc | 189 => xbd | 190 => xbe | 191 => xbf | 192 => xc0 | 193 => xc1 | 194 => xc2 | 195 => xc3 | 196 => xc4 | 197 => xc5 | 198 => xc6 | 199 => xc7 | 200 => xc8 | 201 => xc9 | 202 => xca | 203 => xcb | 204 => xcc | 205 => xcd | 206 => xce | 207 => xcf | 208 => xd0 | 209 => xd1 | 210 => xd2 | 211 => xd3 | 212 => xd4 | 213 => xd5 | 214 => xd6 | 215 => xd7 | 216 => xd8 | 217 => xd9 | 218 => xda | 219 => xdb | 220 => xdc | 221 => xdd | 222 => xde | 223 => xdf | 224 => xe0 | 225 => xe1 | 226 => xe2 | 227 => xe3 | 228 => xe4 | 229 => xe5 | 230 => xe6 | 231 => xe7 | 232 => xe8 | 233 => xe9 | 234 => xea | 235 => xeb | 236 => xec | 237 => xed | 238 => xee | 239 => xef | 240 => xf0 | 241 => xf1 | 242 => xf2 | 243 => xf3 | 244 => xf4 | 245 => xf5 | 246 => xf6 | 247 => xf7 | 248 => xf8 | 249 => xf9 | 250 => xfa | 251 => xfb | 252 => xfc | 253 => xfd | 254 => xfe | 255 => xff
  | _ => x00
  end.

Notation byte_string := (@list w8) (only parsing).

#[local] Definition parse_string (s: list Byte.byte) : byte_string :=
  byte_to_w8 <$> s.
#[local] Definition print_string (b: byte_string) : list Byte.byte :=
  w8_to_byte <$> b.

Declare Scope byte_string_scope.
Bind Scope byte_string_scope with byte_string.
String Notation byte_string parse_string print_string : byte_string_scope.

Notation byte_string' := (@list (@Naive.rep 8)) (only parsing).
String Notation byte_string' parse_string print_string : byte_string_scope.

(* TODO: replace with more computationally efficient version *)
#[local] Definition eqb (s1 s2: byte_string) : bool :=
  bool_decide (s1 = s2).

(* These theorems are not actually required, but they are a sanity check that
the code above is implemented correctly. *)

#[local] Lemma byte_to_w8_to_byte b :
  w8_to_byte (byte_to_w8 b) = b.
Proof. destruct b; auto. Qed.

#[local] Lemma w8_to_byte_to_w8 w :
  byte_to_w8 (w8_to_byte w) = w.
Proof. byte_cases w; reflexivity. Qed.

#[local] Lemma parse_print_inverse s :
  print_string (parse_string s) = s.
Proof.
  rewrite /print_string /parse_string.
  rewrite -list.list_fmap_compose.
  eapply list.list_eq_same_length; eauto.
  - rewrite list.length_fmap //.
  - intros i x y Hlt Hget1 Hget2.
    rewrite list.list_lookup_fmap in Hget1.
    rewrite Hget2 /= in Hget1.
    rewrite byte_to_w8_to_byte in Hget1.
    congruence.
Qed.
