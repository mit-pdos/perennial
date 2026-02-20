From stdpp Require Import base decidable list.
From Perennial.Helpers Require Import Integers bytes.
From Coq Require Import ZArith Strings.Byte.

From Coq Require Import ssreflect.

#[local] Open Scope Z_scope.

(* Parse Coq string syntax directly to [list w8], in preparation for making
GooseLang string literals represented as [list w8] rather than [String] from the
standard library. *)

(* python3 -c 'print("".join(f"| x{n:02x} => @Naive.mk 8 {n} eq_refl " for n in range(0, 256)))' *)
Definition byte_to_w8 (b: byte) : w8 :=
  match b with
  | x00 => @Naive.mk 8 0 eq_refl | x01 => @Naive.mk 8 1 eq_refl | x02 => @Naive.mk 8 2 eq_refl | x03 => @Naive.mk 8 3 eq_refl | x04 => @Naive.mk 8 4 eq_refl | x05 => @Naive.mk 8 5 eq_refl | x06 => @Naive.mk 8 6 eq_refl | x07 => @Naive.mk 8 7 eq_refl | x08 => @Naive.mk 8 8 eq_refl | x09 => @Naive.mk 8 9 eq_refl | x0a => @Naive.mk 8 10 eq_refl | x0b => @Naive.mk 8 11 eq_refl | x0c => @Naive.mk 8 12 eq_refl | x0d => @Naive.mk 8 13 eq_refl | x0e => @Naive.mk 8 14 eq_refl | x0f => @Naive.mk 8 15 eq_refl | x10 => @Naive.mk 8 16 eq_refl | x11 => @Naive.mk 8 17 eq_refl | x12 => @Naive.mk 8 18 eq_refl | x13 => @Naive.mk 8 19 eq_refl | x14 => @Naive.mk 8 20 eq_refl | x15 => @Naive.mk 8 21 eq_refl | x16 => @Naive.mk 8 22 eq_refl | x17 => @Naive.mk 8 23 eq_refl | x18 => @Naive.mk 8 24 eq_refl | x19 => @Naive.mk 8 25 eq_refl | x1a => @Naive.mk 8 26 eq_refl | x1b => @Naive.mk 8 27 eq_refl | x1c => @Naive.mk 8 28 eq_refl | x1d => @Naive.mk 8 29 eq_refl | x1e => @Naive.mk 8 30 eq_refl | x1f => @Naive.mk 8 31 eq_refl | x20 => @Naive.mk 8 32 eq_refl | x21 => @Naive.mk 8 33 eq_refl | x22 => @Naive.mk 8 34 eq_refl | x23 => @Naive.mk 8 35 eq_refl | x24 => @Naive.mk 8 36 eq_refl | x25 => @Naive.mk 8 37 eq_refl | x26 => @Naive.mk 8 38 eq_refl | x27 => @Naive.mk 8 39 eq_refl | x28 => @Naive.mk 8 40 eq_refl | x29 => @Naive.mk 8 41 eq_refl | x2a => @Naive.mk 8 42 eq_refl | x2b => @Naive.mk 8 43 eq_refl | x2c => @Naive.mk 8 44 eq_refl | x2d => @Naive.mk 8 45 eq_refl | x2e => @Naive.mk 8 46 eq_refl | x2f => @Naive.mk 8 47 eq_refl | x30 => @Naive.mk 8 48 eq_refl | x31 => @Naive.mk 8 49 eq_refl | x32 => @Naive.mk 8 50 eq_refl | x33 => @Naive.mk 8 51 eq_refl | x34 => @Naive.mk 8 52 eq_refl | x35 => @Naive.mk 8 53 eq_refl | x36 => @Naive.mk 8 54 eq_refl | x37 => @Naive.mk 8 55 eq_refl | x38 => @Naive.mk 8 56 eq_refl | x39 => @Naive.mk 8 57 eq_refl | x3a => @Naive.mk 8 58 eq_refl | x3b => @Naive.mk 8 59 eq_refl | x3c => @Naive.mk 8 60 eq_refl | x3d => @Naive.mk 8 61 eq_refl | x3e => @Naive.mk 8 62 eq_refl | x3f => @Naive.mk 8 63 eq_refl | x40 => @Naive.mk 8 64 eq_refl | x41 => @Naive.mk 8 65 eq_refl | x42 => @Naive.mk 8 66 eq_refl | x43 => @Naive.mk 8 67 eq_refl | x44 => @Naive.mk 8 68 eq_refl | x45 => @Naive.mk 8 69 eq_refl | x46 => @Naive.mk 8 70 eq_refl | x47 => @Naive.mk 8 71 eq_refl | x48 => @Naive.mk 8 72 eq_refl | x49 => @Naive.mk 8 73 eq_refl | x4a => @Naive.mk 8 74 eq_refl | x4b => @Naive.mk 8 75 eq_refl | x4c => @Naive.mk 8 76 eq_refl | x4d => @Naive.mk 8 77 eq_refl | x4e => @Naive.mk 8 78 eq_refl | x4f => @Naive.mk 8 79 eq_refl | x50 => @Naive.mk 8 80 eq_refl | x51 => @Naive.mk 8 81 eq_refl | x52 => @Naive.mk 8 82 eq_refl | x53 => @Naive.mk 8 83 eq_refl | x54 => @Naive.mk 8 84 eq_refl | x55 => @Naive.mk 8 85 eq_refl | x56 => @Naive.mk 8 86 eq_refl | x57 => @Naive.mk 8 87 eq_refl | x58 => @Naive.mk 8 88 eq_refl | x59 => @Naive.mk 8 89 eq_refl | x5a => @Naive.mk 8 90 eq_refl | x5b => @Naive.mk 8 91 eq_refl | x5c => @Naive.mk 8 92 eq_refl | x5d => @Naive.mk 8 93 eq_refl | x5e => @Naive.mk 8 94 eq_refl | x5f => @Naive.mk 8 95 eq_refl | x60 => @Naive.mk 8 96 eq_refl | x61 => @Naive.mk 8 97 eq_refl | x62 => @Naive.mk 8 98 eq_refl | x63 => @Naive.mk 8 99 eq_refl | x64 => @Naive.mk 8 100 eq_refl | x65 => @Naive.mk 8 101 eq_refl | x66 => @Naive.mk 8 102 eq_refl | x67 => @Naive.mk 8 103 eq_refl | x68 => @Naive.mk 8 104 eq_refl | x69 => @Naive.mk 8 105 eq_refl | x6a => @Naive.mk 8 106 eq_refl | x6b => @Naive.mk 8 107 eq_refl | x6c => @Naive.mk 8 108 eq_refl | x6d => @Naive.mk 8 109 eq_refl | x6e => @Naive.mk 8 110 eq_refl | x6f => @Naive.mk 8 111 eq_refl | x70 => @Naive.mk 8 112 eq_refl | x71 => @Naive.mk 8 113 eq_refl | x72 => @Naive.mk 8 114 eq_refl | x73 => @Naive.mk 8 115 eq_refl | x74 => @Naive.mk 8 116 eq_refl | x75 => @Naive.mk 8 117 eq_refl | x76 => @Naive.mk 8 118 eq_refl | x77 => @Naive.mk 8 119 eq_refl | x78 => @Naive.mk 8 120 eq_refl | x79 => @Naive.mk 8 121 eq_refl | x7a => @Naive.mk 8 122 eq_refl | x7b => @Naive.mk 8 123 eq_refl | x7c => @Naive.mk 8 124 eq_refl | x7d => @Naive.mk 8 125 eq_refl | x7e => @Naive.mk 8 126 eq_refl | x7f => @Naive.mk 8 127 eq_refl | x80 => @Naive.mk 8 128 eq_refl | x81 => @Naive.mk 8 129 eq_refl | x82 => @Naive.mk 8 130 eq_refl | x83 => @Naive.mk 8 131 eq_refl | x84 => @Naive.mk 8 132 eq_refl | x85 => @Naive.mk 8 133 eq_refl | x86 => @Naive.mk 8 134 eq_refl | x87 => @Naive.mk 8 135 eq_refl | x88 => @Naive.mk 8 136 eq_refl | x89 => @Naive.mk 8 137 eq_refl | x8a => @Naive.mk 8 138 eq_refl | x8b => @Naive.mk 8 139 eq_refl | x8c => @Naive.mk 8 140 eq_refl | x8d => @Naive.mk 8 141 eq_refl | x8e => @Naive.mk 8 142 eq_refl | x8f => @Naive.mk 8 143 eq_refl | x90 => @Naive.mk 8 144 eq_refl | x91 => @Naive.mk 8 145 eq_refl | x92 => @Naive.mk 8 146 eq_refl | x93 => @Naive.mk 8 147 eq_refl | x94 => @Naive.mk 8 148 eq_refl | x95 => @Naive.mk 8 149 eq_refl | x96 => @Naive.mk 8 150 eq_refl | x97 => @Naive.mk 8 151 eq_refl | x98 => @Naive.mk 8 152 eq_refl | x99 => @Naive.mk 8 153 eq_refl | x9a => @Naive.mk 8 154 eq_refl | x9b => @Naive.mk 8 155 eq_refl | x9c => @Naive.mk 8 156 eq_refl | x9d => @Naive.mk 8 157 eq_refl | x9e => @Naive.mk 8 158 eq_refl | x9f => @Naive.mk 8 159 eq_refl | xa0 => @Naive.mk 8 160 eq_refl | xa1 => @Naive.mk 8 161 eq_refl | xa2 => @Naive.mk 8 162 eq_refl | xa3 => @Naive.mk 8 163 eq_refl | xa4 => @Naive.mk 8 164 eq_refl | xa5 => @Naive.mk 8 165 eq_refl | xa6 => @Naive.mk 8 166 eq_refl | xa7 => @Naive.mk 8 167 eq_refl | xa8 => @Naive.mk 8 168 eq_refl | xa9 => @Naive.mk 8 169 eq_refl | xaa => @Naive.mk 8 170 eq_refl | xab => @Naive.mk 8 171 eq_refl | xac => @Naive.mk 8 172 eq_refl | xad => @Naive.mk 8 173 eq_refl | xae => @Naive.mk 8 174 eq_refl | xaf => @Naive.mk 8 175 eq_refl | xb0 => @Naive.mk 8 176 eq_refl | xb1 => @Naive.mk 8 177 eq_refl | xb2 => @Naive.mk 8 178 eq_refl | xb3 => @Naive.mk 8 179 eq_refl | xb4 => @Naive.mk 8 180 eq_refl | xb5 => @Naive.mk 8 181 eq_refl | xb6 => @Naive.mk 8 182 eq_refl | xb7 => @Naive.mk 8 183 eq_refl | xb8 => @Naive.mk 8 184 eq_refl | xb9 => @Naive.mk 8 185 eq_refl | xba => @Naive.mk 8 186 eq_refl | xbb => @Naive.mk 8 187 eq_refl | xbc => @Naive.mk 8 188 eq_refl | xbd => @Naive.mk 8 189 eq_refl | xbe => @Naive.mk 8 190 eq_refl | xbf => @Naive.mk 8 191 eq_refl | xc0 => @Naive.mk 8 192 eq_refl | xc1 => @Naive.mk 8 193 eq_refl | xc2 => @Naive.mk 8 194 eq_refl | xc3 => @Naive.mk 8 195 eq_refl | xc4 => @Naive.mk 8 196 eq_refl | xc5 => @Naive.mk 8 197 eq_refl | xc6 => @Naive.mk 8 198 eq_refl | xc7 => @Naive.mk 8 199 eq_refl | xc8 => @Naive.mk 8 200 eq_refl | xc9 => @Naive.mk 8 201 eq_refl | xca => @Naive.mk 8 202 eq_refl | xcb => @Naive.mk 8 203 eq_refl | xcc => @Naive.mk 8 204 eq_refl | xcd => @Naive.mk 8 205 eq_refl | xce => @Naive.mk 8 206 eq_refl | xcf => @Naive.mk 8 207 eq_refl | xd0 => @Naive.mk 8 208 eq_refl | xd1 => @Naive.mk 8 209 eq_refl | xd2 => @Naive.mk 8 210 eq_refl | xd3 => @Naive.mk 8 211 eq_refl | xd4 => @Naive.mk 8 212 eq_refl | xd5 => @Naive.mk 8 213 eq_refl | xd6 => @Naive.mk 8 214 eq_refl | xd7 => @Naive.mk 8 215 eq_refl | xd8 => @Naive.mk 8 216 eq_refl | xd9 => @Naive.mk 8 217 eq_refl | xda => @Naive.mk 8 218 eq_refl | xdb => @Naive.mk 8 219 eq_refl | xdc => @Naive.mk 8 220 eq_refl | xdd => @Naive.mk 8 221 eq_refl | xde => @Naive.mk 8 222 eq_refl | xdf => @Naive.mk 8 223 eq_refl | xe0 => @Naive.mk 8 224 eq_refl | xe1 => @Naive.mk 8 225 eq_refl | xe2 => @Naive.mk 8 226 eq_refl | xe3 => @Naive.mk 8 227 eq_refl | xe4 => @Naive.mk 8 228 eq_refl | xe5 => @Naive.mk 8 229 eq_refl | xe6 => @Naive.mk 8 230 eq_refl | xe7 => @Naive.mk 8 231 eq_refl | xe8 => @Naive.mk 8 232 eq_refl | xe9 => @Naive.mk 8 233 eq_refl | xea => @Naive.mk 8 234 eq_refl | xeb => @Naive.mk 8 235 eq_refl | xec => @Naive.mk 8 236 eq_refl | xed => @Naive.mk 8 237 eq_refl | xee => @Naive.mk 8 238 eq_refl | xef => @Naive.mk 8 239 eq_refl | xf0 => @Naive.mk 8 240 eq_refl | xf1 => @Naive.mk 8 241 eq_refl | xf2 => @Naive.mk 8 242 eq_refl | xf3 => @Naive.mk 8 243 eq_refl | xf4 => @Naive.mk 8 244 eq_refl | xf5 => @Naive.mk 8 245 eq_refl | xf6 => @Naive.mk 8 246 eq_refl | xf7 => @Naive.mk 8 247 eq_refl | xf8 => @Naive.mk 8 248 eq_refl | xf9 => @Naive.mk 8 249 eq_refl | xfa => @Naive.mk 8 250 eq_refl | xfb => @Naive.mk 8 251 eq_refl | xfc => @Naive.mk 8 252 eq_refl | xfd => @Naive.mk 8 253 eq_refl | xfe => @Naive.mk 8 254 eq_refl | xff => @Naive.mk 8 255 eq_refl
  end.
Definition w8_to_byte (w: w8) : byte :=
  match uint.Z w with
  (* python3 -c 'print("".join(f"| {n} => x{n:02x} " for n in range(0, 256)))' *)
  | 0 => x00 | 1 => x01 | 2 => x02 | 3 => x03 | 4 => x04 | 5 => x05 | 6 => x06 | 7 => x07 | 8 => x08 | 9 => x09 | 10 => x0a | 11 => x0b | 12 => x0c | 13 => x0d | 14 => x0e | 15 => x0f | 16 => x10 | 17 => x11 | 18 => x12 | 19 => x13 | 20 => x14 | 21 => x15 | 22 => x16 | 23 => x17 | 24 => x18 | 25 => x19 | 26 => x1a | 27 => x1b | 28 => x1c | 29 => x1d | 30 => x1e | 31 => x1f | 32 => x20 | 33 => x21 | 34 => x22 | 35 => x23 | 36 => x24 | 37 => x25 | 38 => x26 | 39 => x27 | 40 => x28 | 41 => x29 | 42 => x2a | 43 => x2b | 44 => x2c | 45 => x2d | 46 => x2e | 47 => x2f | 48 => x30 | 49 => x31 | 50 => x32 | 51 => x33 | 52 => x34 | 53 => x35 | 54 => x36 | 55 => x37 | 56 => x38 | 57 => x39 | 58 => x3a | 59 => x3b | 60 => x3c | 61 => x3d | 62 => x3e | 63 => x3f | 64 => x40 | 65 => x41 | 66 => x42 | 67 => x43 | 68 => x44 | 69 => x45 | 70 => x46 | 71 => x47 | 72 => x48 | 73 => x49 | 74 => x4a | 75 => x4b | 76 => x4c | 77 => x4d | 78 => x4e | 79 => x4f | 80 => x50 | 81 => x51 | 82 => x52 | 83 => x53 | 84 => x54 | 85 => x55 | 86 => x56 | 87 => x57 | 88 => x58 | 89 => x59 | 90 => x5a | 91 => x5b | 92 => x5c | 93 => x5d | 94 => x5e | 95 => x5f | 96 => x60 | 97 => x61 | 98 => x62 | 99 => x63 | 100 => x64 | 101 => x65 | 102 => x66 | 103 => x67 | 104 => x68 | 105 => x69 | 106 => x6a | 107 => x6b | 108 => x6c | 109 => x6d | 110 => x6e | 111 => x6f | 112 => x70 | 113 => x71 | 114 => x72 | 115 => x73 | 116 => x74 | 117 => x75 | 118 => x76 | 119 => x77 | 120 => x78 | 121 => x79 | 122 => x7a | 123 => x7b | 124 => x7c | 125 => x7d | 126 => x7e | 127 => x7f | 128 => x80 | 129 => x81 | 130 => x82 | 131 => x83 | 132 => x84 | 133 => x85 | 134 => x86 | 135 => x87 | 136 => x88 | 137 => x89 | 138 => x8a | 139 => x8b | 140 => x8c | 141 => x8d | 142 => x8e | 143 => x8f | 144 => x90 | 145 => x91 | 146 => x92 | 147 => x93 | 148 => x94 | 149 => x95 | 150 => x96 | 151 => x97 | 152 => x98 | 153 => x99 | 154 => x9a | 155 => x9b | 156 => x9c | 157 => x9d | 158 => x9e | 159 => x9f | 160 => xa0 | 161 => xa1 | 162 => xa2 | 163 => xa3 | 164 => xa4 | 165 => xa5 | 166 => xa6 | 167 => xa7 | 168 => xa8 | 169 => xa9 | 170 => xaa | 171 => xab | 172 => xac | 173 => xad | 174 => xae | 175 => xaf | 176 => xb0 | 177 => xb1 | 178 => xb2 | 179 => xb3 | 180 => xb4 | 181 => xb5 | 182 => xb6 | 183 => xb7 | 184 => xb8 | 185 => xb9 | 186 => xba | 187 => xbb | 188 => xbc | 189 => xbd | 190 => xbe | 191 => xbf | 192 => xc0 | 193 => xc1 | 194 => xc2 | 195 => xc3 | 196 => xc4 | 197 => xc5 | 198 => xc6 | 199 => xc7 | 200 => xc8 | 201 => xc9 | 202 => xca | 203 => xcb | 204 => xcc | 205 => xcd | 206 => xce | 207 => xcf | 208 => xd0 | 209 => xd1 | 210 => xd2 | 211 => xd3 | 212 => xd4 | 213 => xd5 | 214 => xd6 | 215 => xd7 | 216 => xd8 | 217 => xd9 | 218 => xda | 219 => xdb | 220 => xdc | 221 => xdd | 222 => xde | 223 => xdf | 224 => xe0 | 225 => xe1 | 226 => xe2 | 227 => xe3 | 228 => xe4 | 229 => xe5 | 230 => xe6 | 231 => xe7 | 232 => xe8 | 233 => xe9 | 234 => xea | 235 => xeb | 236 => xec | 237 => xed | 238 => xee | 239 => xef | 240 => xf0 | 241 => xf1 | 242 => xf2 | 243 => xf3 | 244 => xf4 | 245 => xf5 | 246 => xf6 | 247 => xf7 | 248 => xf8 | 249 => xf9 | 250 => xfa | 251 => xfb | 252 => xfc | 253 => xfd | 254 => xfe | 255 => xff
  | _ => x00
  end.

Declare Scope byte_char_scope.
Inductive IndW8 := IW8 : Z → IndW8.

Definition byte_to_I (b: byte) : IndW8 :=
  match b with
(* python3 -c 'print("".join(f"| x{n:02x} => IW8 {n} " for n in range(0, 256)))' *)
  | x00 => IW8 0 | x01 => IW8 1 | x02 => IW8 2 | x03 => IW8 3 | x04 => IW8 4 | x05 => IW8 5 | x06 => IW8 6 | x07 => IW8 7 | x08 => IW8 8 | x09 => IW8 9 | x0a => IW8 10 | x0b => IW8 11 | x0c => IW8 12 | x0d => IW8 13 | x0e => IW8 14 | x0f => IW8 15 | x10 => IW8 16 | x11 => IW8 17 | x12 => IW8 18 | x13 => IW8 19 | x14 => IW8 20 | x15 => IW8 21 | x16 => IW8 22 | x17 => IW8 23 | x18 => IW8 24 | x19 => IW8 25 | x1a => IW8 26 | x1b => IW8 27 | x1c => IW8 28 | x1d => IW8 29 | x1e => IW8 30 | x1f => IW8 31 | x20 => IW8 32 | x21 => IW8 33 | x22 => IW8 34 | x23 => IW8 35 | x24 => IW8 36 | x25 => IW8 37 | x26 => IW8 38 | x27 => IW8 39 | x28 => IW8 40 | x29 => IW8 41 | x2a => IW8 42 | x2b => IW8 43 | x2c => IW8 44 | x2d => IW8 45 | x2e => IW8 46 | x2f => IW8 47 | x30 => IW8 48 | x31 => IW8 49 | x32 => IW8 50 | x33 => IW8 51 | x34 => IW8 52 | x35 => IW8 53 | x36 => IW8 54 | x37 => IW8 55 | x38 => IW8 56 | x39 => IW8 57 | x3a => IW8 58 | x3b => IW8 59 | x3c => IW8 60 | x3d => IW8 61 | x3e => IW8 62 | x3f => IW8 63 | x40 => IW8 64 | x41 => IW8 65 | x42 => IW8 66 | x43 => IW8 67 | x44 => IW8 68 | x45 => IW8 69 | x46 => IW8 70 | x47 => IW8 71 | x48 => IW8 72 | x49 => IW8 73 | x4a => IW8 74 | x4b => IW8 75 | x4c => IW8 76 | x4d => IW8 77 | x4e => IW8 78 | x4f => IW8 79 | x50 => IW8 80 | x51 => IW8 81 | x52 => IW8 82 | x53 => IW8 83 | x54 => IW8 84 | x55 => IW8 85 | x56 => IW8 86 | x57 => IW8 87 | x58 => IW8 88 | x59 => IW8 89 | x5a => IW8 90 | x5b => IW8 91 | x5c => IW8 92 | x5d => IW8 93 | x5e => IW8 94 | x5f => IW8 95 | x60 => IW8 96 | x61 => IW8 97 | x62 => IW8 98 | x63 => IW8 99 | x64 => IW8 100 | x65 => IW8 101 | x66 => IW8 102 | x67 => IW8 103 | x68 => IW8 104 | x69 => IW8 105 | x6a => IW8 106 | x6b => IW8 107 | x6c => IW8 108 | x6d => IW8 109 | x6e => IW8 110 | x6f => IW8 111 | x70 => IW8 112 | x71 => IW8 113 | x72 => IW8 114 | x73 => IW8 115 | x74 => IW8 116 | x75 => IW8 117 | x76 => IW8 118 | x77 => IW8 119 | x78 => IW8 120 | x79 => IW8 121 | x7a => IW8 122 | x7b => IW8 123 | x7c => IW8 124 | x7d => IW8 125 | x7e => IW8 126 | x7f => IW8 127 | x80 => IW8 128 | x81 => IW8 129 | x82 => IW8 130 | x83 => IW8 131 | x84 => IW8 132 | x85 => IW8 133 | x86 => IW8 134 | x87 => IW8 135 | x88 => IW8 136 | x89 => IW8 137 | x8a => IW8 138 | x8b => IW8 139 | x8c => IW8 140 | x8d => IW8 141 | x8e => IW8 142 | x8f => IW8 143 | x90 => IW8 144 | x91 => IW8 145 | x92 => IW8 146 | x93 => IW8 147 | x94 => IW8 148 | x95 => IW8 149 | x96 => IW8 150 | x97 => IW8 151 | x98 => IW8 152 | x99 => IW8 153 | x9a => IW8 154 | x9b => IW8 155 | x9c => IW8 156 | x9d => IW8 157 | x9e => IW8 158 | x9f => IW8 159 | xa0 => IW8 160 | xa1 => IW8 161 | xa2 => IW8 162 | xa3 => IW8 163 | xa4 => IW8 164 | xa5 => IW8 165 | xa6 => IW8 166 | xa7 => IW8 167 | xa8 => IW8 168 | xa9 => IW8 169 | xaa => IW8 170 | xab => IW8 171 | xac => IW8 172 | xad => IW8 173 | xae => IW8 174 | xaf => IW8 175 | xb0 => IW8 176 | xb1 => IW8 177 | xb2 => IW8 178 | xb3 => IW8 179 | xb4 => IW8 180 | xb5 => IW8 181 | xb6 => IW8 182 | xb7 => IW8 183 | xb8 => IW8 184 | xb9 => IW8 185 | xba => IW8 186 | xbb => IW8 187 | xbc => IW8 188 | xbd => IW8 189 | xbe => IW8 190 | xbf => IW8 191 | xc0 => IW8 192 | xc1 => IW8 193 | xc2 => IW8 194 | xc3 => IW8 195 | xc4 => IW8 196 | xc5 => IW8 197 | xc6 => IW8 198 | xc7 => IW8 199 | xc8 => IW8 200 | xc9 => IW8 201 | xca => IW8 202 | xcb => IW8 203 | xcc => IW8 204 | xcd => IW8 205 | xce => IW8 206 | xcf => IW8 207 | xd0 => IW8 208 | xd1 => IW8 209 | xd2 => IW8 210 | xd3 => IW8 211 | xd4 => IW8 212 | xd5 => IW8 213 | xd6 => IW8 214 | xd7 => IW8 215 | xd8 => IW8 216 | xd9 => IW8 217 | xda => IW8 218 | xdb => IW8 219 | xdc => IW8 220 | xdd => IW8 221 | xde => IW8 222 | xdf => IW8 223 | xe0 => IW8 224 | xe1 => IW8 225 | xe2 => IW8 226 | xe3 => IW8 227 | xe4 => IW8 228 | xe5 => IW8 229 | xe6 => IW8 230 | xe7 => IW8 231 | xe8 => IW8 232 | xe9 => IW8 233 | xea => IW8 234 | xeb => IW8 235 | xec => IW8 236 | xed => IW8 237 | xee => IW8 238 | xef => IW8 239 | xf0 => IW8 240 | xf1 => IW8 241 | xf2 => IW8 242 | xf3 => IW8 243 | xf4 => IW8 244 | xf5 => IW8 245 | xf6 => IW8 246 | xf7 => IW8 247 | xf8 => IW8 248 | xf9 => IW8 249 | xfa => IW8 250 | xfb => IW8 251 | xfc => IW8 252 | xfd => IW8 253 | xfe => IW8 254 | xff => IW8 255
  end.

Definition I_to_byte (w: IndW8) : byte :=
  let x := (match w with IW8 x => x end) in
  match x with
  (* python3 -c 'print("".join(f"| {n} => x{n:02x} " for n in range(0, 256)))' *)
  | 0 => x00 | 1 => x01 | 2 => x02 | 3 => x03 | 4 => x04 | 5 => x05 | 6 => x06 | 7 => x07 | 8 => x08 | 9 => x09 | 10 => x0a | 11 => x0b | 12 => x0c | 13 => x0d | 14 => x0e | 15 => x0f | 16 => x10 | 17 => x11 | 18 => x12 | 19 => x13 | 20 => x14 | 21 => x15 | 22 => x16 | 23 => x17 | 24 => x18 | 25 => x19 | 26 => x1a | 27 => x1b | 28 => x1c | 29 => x1d | 30 => x1e | 31 => x1f | 32 => x20 | 33 => x21 | 34 => x22 | 35 => x23 | 36 => x24 | 37 => x25 | 38 => x26 | 39 => x27 | 40 => x28 | 41 => x29 | 42 => x2a | 43 => x2b | 44 => x2c | 45 => x2d | 46 => x2e | 47 => x2f | 48 => x30 | 49 => x31 | 50 => x32 | 51 => x33 | 52 => x34 | 53 => x35 | 54 => x36 | 55 => x37 | 56 => x38 | 57 => x39 | 58 => x3a | 59 => x3b | 60 => x3c | 61 => x3d | 62 => x3e | 63 => x3f | 64 => x40 | 65 => x41 | 66 => x42 | 67 => x43 | 68 => x44 | 69 => x45 | 70 => x46 | 71 => x47 | 72 => x48 | 73 => x49 | 74 => x4a | 75 => x4b | 76 => x4c | 77 => x4d | 78 => x4e | 79 => x4f | 80 => x50 | 81 => x51 | 82 => x52 | 83 => x53 | 84 => x54 | 85 => x55 | 86 => x56 | 87 => x57 | 88 => x58 | 89 => x59 | 90 => x5a | 91 => x5b | 92 => x5c | 93 => x5d | 94 => x5e | 95 => x5f | 96 => x60 | 97 => x61 | 98 => x62 | 99 => x63 | 100 => x64 | 101 => x65 | 102 => x66 | 103 => x67 | 104 => x68 | 105 => x69 | 106 => x6a | 107 => x6b | 108 => x6c | 109 => x6d | 110 => x6e | 111 => x6f | 112 => x70 | 113 => x71 | 114 => x72 | 115 => x73 | 116 => x74 | 117 => x75 | 118 => x76 | 119 => x77 | 120 => x78 | 121 => x79 | 122 => x7a | 123 => x7b | 124 => x7c | 125 => x7d | 126 => x7e | 127 => x7f | 128 => x80 | 129 => x81 | 130 => x82 | 131 => x83 | 132 => x84 | 133 => x85 | 134 => x86 | 135 => x87 | 136 => x88 | 137 => x89 | 138 => x8a | 139 => x8b | 140 => x8c | 141 => x8d | 142 => x8e | 143 => x8f | 144 => x90 | 145 => x91 | 146 => x92 | 147 => x93 | 148 => x94 | 149 => x95 | 150 => x96 | 151 => x97 | 152 => x98 | 153 => x99 | 154 => x9a | 155 => x9b | 156 => x9c | 157 => x9d | 158 => x9e | 159 => x9f | 160 => xa0 | 161 => xa1 | 162 => xa2 | 163 => xa3 | 164 => xa4 | 165 => xa5 | 166 => xa6 | 167 => xa7 | 168 => xa8 | 169 => xa9 | 170 => xaa | 171 => xab | 172 => xac | 173 => xad | 174 => xae | 175 => xaf | 176 => xb0 | 177 => xb1 | 178 => xb2 | 179 => xb3 | 180 => xb4 | 181 => xb5 | 182 => xb6 | 183 => xb7 | 184 => xb8 | 185 => xb9 | 186 => xba | 187 => xbb | 188 => xbc | 189 => xbd | 190 => xbe | 191 => xbf | 192 => xc0 | 193 => xc1 | 194 => xc2 | 195 => xc3 | 196 => xc4 | 197 => xc5 | 198 => xc6 | 199 => xc7 | 200 => xc8 | 201 => xc9 | 202 => xca | 203 => xcb | 204 => xcc | 205 => xcd | 206 => xce | 207 => xcf | 208 => xd0 | 209 => xd1 | 210 => xd2 | 211 => xd3 | 212 => xd4 | 213 => xd5 | 214 => xd6 | 215 => xd7 | 216 => xd8 | 217 => xd9 | 218 => xda | 219 => xdb | 220 => xdc | 221 => xdd | 222 => xde | 223 => xdf | 224 => xe0 | 225 => xe1 | 226 => xe2 | 227 => xe3 | 228 => xe4 | 229 => xe5 | 230 => xe6 | 231 => xe7 | 232 => xe8 | 233 => xe9 | 234 => xea | 235 => xeb | 236 => xec | 237 => xed | 238 => xee | 239 => xef | 240 => xf0 | 241 => xf1 | 242 => xf2 | 243 => xf3 | 244 => xf4 | 245 => xf5 | 246 => xf6 | 247 => xf7 | 248 => xf8 | 249 => xf9 | 250 => xfa | 251 => xfb | 252 => xfc | 253 => xfd | 254 => xfe | 255 => xff
  | _ => x00
  end.

(* XXX: have to go via inductive because [w8] is not an inductive. *)
String Notation w8 byte_to_I I_to_byte (via IndW8 mapping [W8 => IW8]) : byte_char_scope.

Definition byte_string := (list w8).
Inductive IndByteString := IByteString : (list w8) → IndByteString.

#[local] Definition parse_string (s: list Byte.byte) : IndByteString :=
  IByteString (byte_to_w8 <$> s).
#[local] Definition print_string (b: IndByteString) : list Byte.byte :=
  match b with
  | IByteString b => w8_to_byte <$> b
  end.

Declare Scope byte_string_scope.
Bind Scope byte_string_scope with byte_string.

Definition id_byte_string : byte_string → byte_string := id.

(* XXX: going via inductive to byte_string avoid ending up with [list Naive.rep]
   when parsing under this notation. With this, we end up with [byte_string],
   which is convertible to [list w8]. *)
String Notation byte_string parse_string print_string
  (via IndByteString mapping [id_byte_string => IByteString] )
  : byte_string_scope.

Definition byte_eqb (x y : w8) : bool :=
  match x, y with
  | Naive.mk x _, Naive.mk y _ => Z.eqb x y
  end.

#[local] Fixpoint eqb (s1 s2: byte_string) : bool :=
  match s1 with
  | [] => match s2 with
         | [] => true
         | _ => false
         end
  | c1 :: s1' =>
      match s2 with
      | [] => false
      | c2 :: s2' => if byte_eqb c1 c2 then eqb s1' s2' else false
      end
  end.

Lemma byte_eqb_eq a b :
  a = b → byte_eqb a b = true.
Proof.
  intros. subst. destruct b.
  simpl. apply Z.eqb_refl.
Qed.

#[local] Lemma byte_eqb_true x y :
  byte_eqb x y = true → x = y.
Proof.
  intros. destruct x, y. apply Zeq_bool_eq in H. subst.
  f_equal. apply Eqdep_dec.UIP_dec. intros.
  destruct (decide (x = y)); [left|right]; done.
Qed.

#[local] Lemma eqb_refl x :
  eqb x x = true.
Proof.
  induction x; first done. simpl. rewrite byte_eqb_eq //.
Qed.

#[local] Lemma eqb_eq x y :
  x = y → eqb x y = true.
Proof.
  intros ?. subst. apply eqb_refl.
Qed.

#[local] Lemma eqb_true x y :
  eqb x y = true → x = y.
Proof.
  revert y. induction x.
  - by destruct y.
  - destruct y; first done.
    simpl.
    destruct (byte_eqb) eqn:?; last done.
    apply byte_eqb_true in Heqb. subst.
    intros H. f_equal.
    by apply IHx.
Qed.

#[local] Lemma eqb_false x y :
  eqb x y = false → x ≠ y.
Proof.
  intros Heqb.
  intros Heq. apply eqb_eq in Heq. rewrite Heqb in Heq. done.
Qed.

#[local] Lemma eqb_ne x y :
  x ≠ y → eqb x y = false.
Proof.
  destruct eqb eqn:?.
  { intros ?. apply eqb_true in Heqb. done. }
  { done. }
Qed.

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
