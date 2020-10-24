From Coq Require Import ZArith.
From Perennial.Helpers Require Import Integers.
From stdpp Require Import base numbers.
Open Scope Z.

Section byte.
Transparent u8_instance.u8.
Theorem byte_destruct (P: u8 → Prop) :
  (∀ (z:Z) (Hunsigned_in_range: z `mod` 2^8 = z) (Hrange: 0 ≤ z < 2^8), P (Word8 ((Naive.mk z Hunsigned_in_range)))) →
  (∀ x, P x).
Proof.
  intros.
  pose proof (word.unsigned_range x).
  destruct x as [ [z ?] ].
  simpl in H0.
  apply H; auto.
Qed.

Inductive byte_vals (x:u8) : Prop :=
  | Byte0 (Heq:x=U8 0) | Byte1 (Heq:x=U8 1) | Byte2 (Heq:x=U8 2) | Byte3 (Heq:x=U8 3) | Byte4 (Heq:x=U8 4) | Byte5 (Heq:x=U8 5) | Byte6 (Heq:x=U8 6) | Byte7 (Heq:x=U8 7) | Byte8 (Heq:x=U8 8) | Byte9 (Heq:x=U8 9) | Byte10 (Heq:x=U8 10) | Byte11 (Heq:x=U8 11) | Byte12 (Heq:x=U8 12) | Byte13 (Heq:x=U8 13) | Byte14 (Heq:x=U8 14) | Byte15 (Heq:x=U8 15) | Byte16 (Heq:x=U8 16) | Byte17 (Heq:x=U8 17) | Byte18 (Heq:x=U8 18) | Byte19 (Heq:x=U8 19) | Byte20 (Heq:x=U8 20) | Byte21 (Heq:x=U8 21) | Byte22 (Heq:x=U8 22) | Byte23 (Heq:x=U8 23) | Byte24 (Heq:x=U8 24) | Byte25 (Heq:x=U8 25) | Byte26 (Heq:x=U8 26) | Byte27 (Heq:x=U8 27) | Byte28 (Heq:x=U8 28) | Byte29 (Heq:x=U8 29) | Byte30 (Heq:x=U8 30) | Byte31 (Heq:x=U8 31) | Byte32 (Heq:x=U8 32) | Byte33 (Heq:x=U8 33) | Byte34 (Heq:x=U8 34) | Byte35 (Heq:x=U8 35) | Byte36 (Heq:x=U8 36) | Byte37 (Heq:x=U8 37) | Byte38 (Heq:x=U8 38) | Byte39 (Heq:x=U8 39) | Byte40 (Heq:x=U8 40) | Byte41 (Heq:x=U8 41) | Byte42 (Heq:x=U8 42) | Byte43 (Heq:x=U8 43) | Byte44 (Heq:x=U8 44) | Byte45 (Heq:x=U8 45) | Byte46 (Heq:x=U8 46) | Byte47 (Heq:x=U8 47) | Byte48 (Heq:x=U8 48) | Byte49 (Heq:x=U8 49) | Byte50 (Heq:x=U8 50) | Byte51 (Heq:x=U8 51) | Byte52 (Heq:x=U8 52) | Byte53 (Heq:x=U8 53) | Byte54 (Heq:x=U8 54) | Byte55 (Heq:x=U8 55) | Byte56 (Heq:x=U8 56) | Byte57 (Heq:x=U8 57) | Byte58 (Heq:x=U8 58) | Byte59 (Heq:x=U8 59) | Byte60 (Heq:x=U8 60) | Byte61 (Heq:x=U8 61) | Byte62 (Heq:x=U8 62) | Byte63 (Heq:x=U8 63) | Byte64 (Heq:x=U8 64) | Byte65 (Heq:x=U8 65) | Byte66 (Heq:x=U8 66) | Byte67 (Heq:x=U8 67) | Byte68 (Heq:x=U8 68) | Byte69 (Heq:x=U8 69) | Byte70 (Heq:x=U8 70) | Byte71 (Heq:x=U8 71) | Byte72 (Heq:x=U8 72) | Byte73 (Heq:x=U8 73) | Byte74 (Heq:x=U8 74) | Byte75 (Heq:x=U8 75) | Byte76 (Heq:x=U8 76) | Byte77 (Heq:x=U8 77) | Byte78 (Heq:x=U8 78) | Byte79 (Heq:x=U8 79) | Byte80 (Heq:x=U8 80) | Byte81 (Heq:x=U8 81) | Byte82 (Heq:x=U8 82) | Byte83 (Heq:x=U8 83) | Byte84 (Heq:x=U8 84) | Byte85 (Heq:x=U8 85) | Byte86 (Heq:x=U8 86) | Byte87 (Heq:x=U8 87) | Byte88 (Heq:x=U8 88) | Byte89 (Heq:x=U8 89) | Byte90 (Heq:x=U8 90) | Byte91 (Heq:x=U8 91) | Byte92 (Heq:x=U8 92) | Byte93 (Heq:x=U8 93) | Byte94 (Heq:x=U8 94) | Byte95 (Heq:x=U8 95) | Byte96 (Heq:x=U8 96) | Byte97 (Heq:x=U8 97) | Byte98 (Heq:x=U8 98) | Byte99 (Heq:x=U8 99) | Byte100 (Heq:x=U8 100) | Byte101 (Heq:x=U8 101) | Byte102 (Heq:x=U8 102) | Byte103 (Heq:x=U8 103) | Byte104 (Heq:x=U8 104) | Byte105 (Heq:x=U8 105) | Byte106 (Heq:x=U8 106) | Byte107 (Heq:x=U8 107) | Byte108 (Heq:x=U8 108) | Byte109 (Heq:x=U8 109) | Byte110 (Heq:x=U8 110) | Byte111 (Heq:x=U8 111) | Byte112 (Heq:x=U8 112) | Byte113 (Heq:x=U8 113) | Byte114 (Heq:x=U8 114) | Byte115 (Heq:x=U8 115) | Byte116 (Heq:x=U8 116) | Byte117 (Heq:x=U8 117) | Byte118 (Heq:x=U8 118) | Byte119 (Heq:x=U8 119) | Byte120 (Heq:x=U8 120) | Byte121 (Heq:x=U8 121) | Byte122 (Heq:x=U8 122) | Byte123 (Heq:x=U8 123) | Byte124 (Heq:x=U8 124) | Byte125 (Heq:x=U8 125) | Byte126 (Heq:x=U8 126) | Byte127 (Heq:x=U8 127) | Byte128 (Heq:x=U8 128) | Byte129 (Heq:x=U8 129) | Byte130 (Heq:x=U8 130) | Byte131 (Heq:x=U8 131) | Byte132 (Heq:x=U8 132) | Byte133 (Heq:x=U8 133) | Byte134 (Heq:x=U8 134) | Byte135 (Heq:x=U8 135) | Byte136 (Heq:x=U8 136) | Byte137 (Heq:x=U8 137) | Byte138 (Heq:x=U8 138) | Byte139 (Heq:x=U8 139) | Byte140 (Heq:x=U8 140) | Byte141 (Heq:x=U8 141) | Byte142 (Heq:x=U8 142) | Byte143 (Heq:x=U8 143) | Byte144 (Heq:x=U8 144) | Byte145 (Heq:x=U8 145) | Byte146 (Heq:x=U8 146) | Byte147 (Heq:x=U8 147) | Byte148 (Heq:x=U8 148) | Byte149 (Heq:x=U8 149) | Byte150 (Heq:x=U8 150) | Byte151 (Heq:x=U8 151) | Byte152 (Heq:x=U8 152) | Byte153 (Heq:x=U8 153) | Byte154 (Heq:x=U8 154) | Byte155 (Heq:x=U8 155) | Byte156 (Heq:x=U8 156) | Byte157 (Heq:x=U8 157) | Byte158 (Heq:x=U8 158) | Byte159 (Heq:x=U8 159) | Byte160 (Heq:x=U8 160) | Byte161 (Heq:x=U8 161) | Byte162 (Heq:x=U8 162) | Byte163 (Heq:x=U8 163) | Byte164 (Heq:x=U8 164) | Byte165 (Heq:x=U8 165) | Byte166 (Heq:x=U8 166) | Byte167 (Heq:x=U8 167) | Byte168 (Heq:x=U8 168) | Byte169 (Heq:x=U8 169) | Byte170 (Heq:x=U8 170) | Byte171 (Heq:x=U8 171) | Byte172 (Heq:x=U8 172) | Byte173 (Heq:x=U8 173) | Byte174 (Heq:x=U8 174) | Byte175 (Heq:x=U8 175) | Byte176 (Heq:x=U8 176) | Byte177 (Heq:x=U8 177) | Byte178 (Heq:x=U8 178) | Byte179 (Heq:x=U8 179) | Byte180 (Heq:x=U8 180) | Byte181 (Heq:x=U8 181) | Byte182 (Heq:x=U8 182) | Byte183 (Heq:x=U8 183) | Byte184 (Heq:x=U8 184) | Byte185 (Heq:x=U8 185) | Byte186 (Heq:x=U8 186) | Byte187 (Heq:x=U8 187) | Byte188 (Heq:x=U8 188) | Byte189 (Heq:x=U8 189) | Byte190 (Heq:x=U8 190) | Byte191 (Heq:x=U8 191) | Byte192 (Heq:x=U8 192) | Byte193 (Heq:x=U8 193) | Byte194 (Heq:x=U8 194) | Byte195 (Heq:x=U8 195) | Byte196 (Heq:x=U8 196) | Byte197 (Heq:x=U8 197) | Byte198 (Heq:x=U8 198) | Byte199 (Heq:x=U8 199) | Byte200 (Heq:x=U8 200) | Byte201 (Heq:x=U8 201) | Byte202 (Heq:x=U8 202) | Byte203 (Heq:x=U8 203) | Byte204 (Heq:x=U8 204) | Byte205 (Heq:x=U8 205) | Byte206 (Heq:x=U8 206) | Byte207 (Heq:x=U8 207) | Byte208 (Heq:x=U8 208) | Byte209 (Heq:x=U8 209) | Byte210 (Heq:x=U8 210) | Byte211 (Heq:x=U8 211) | Byte212 (Heq:x=U8 212) | Byte213 (Heq:x=U8 213) | Byte214 (Heq:x=U8 214) | Byte215 (Heq:x=U8 215) | Byte216 (Heq:x=U8 216) | Byte217 (Heq:x=U8 217) | Byte218 (Heq:x=U8 218) | Byte219 (Heq:x=U8 219) | Byte220 (Heq:x=U8 220) | Byte221 (Heq:x=U8 221) | Byte222 (Heq:x=U8 222) | Byte223 (Heq:x=U8 223) | Byte224 (Heq:x=U8 224) | Byte225 (Heq:x=U8 225) | Byte226 (Heq:x=U8 226) | Byte227 (Heq:x=U8 227) | Byte228 (Heq:x=U8 228) | Byte229 (Heq:x=U8 229) | Byte230 (Heq:x=U8 230) | Byte231 (Heq:x=U8 231) | Byte232 (Heq:x=U8 232) | Byte233 (Heq:x=U8 233) | Byte234 (Heq:x=U8 234) | Byte235 (Heq:x=U8 235) | Byte236 (Heq:x=U8 236) | Byte237 (Heq:x=U8 237) | Byte238 (Heq:x=U8 238) | Byte239 (Heq:x=U8 239) | Byte240 (Heq:x=U8 240) | Byte241 (Heq:x=U8 241) | Byte242 (Heq:x=U8 242) | Byte243 (Heq:x=U8 243) | Byte244 (Heq:x=U8 244) | Byte245 (Heq:x=U8 245) | Byte246 (Heq:x=U8 246) | Byte247 (Heq:x=U8 247) | Byte248 (Heq:x=U8 248) | Byte249 (Heq:x=U8 249) | Byte250 (Heq:x=U8 250) | Byte251 (Heq:x=U8 251) | Byte252 (Heq:x=U8 252) | Byte253 (Heq:x=U8 253) | Byte254 (Heq:x=U8 254) | Byte255 (Heq:x=U8 255).

Ltac t z n c :=
  destruct (decide (z = n)) as [->|?];
  [apply c, (@int_val_inj 8 u8_instance.u8 u8_instance.u8_word_ok), eq_refl
  |].

Theorem byte_explode (x:u8) : byte_vals x.
Proof.
  apply byte_destruct.
  intros z ? Hlt.
  t z 0 Byte0.
  t z 1 Byte1.
  t z 2 Byte2.
  t z 3 Byte3.
  t z 4 Byte4.
  t z 5 Byte5.
  t z 6 Byte6.
  t z 7 Byte7.
  t z 8 Byte8.
  t z 9 Byte9.
  t z 10 Byte10.
  t z 11 Byte11.
  t z 12 Byte12.
  t z 13 Byte13.
  t z 14 Byte14.
  t z 15 Byte15.
  t z 16 Byte16.
  t z 17 Byte17.
  t z 18 Byte18.
  t z 19 Byte19.
  t z 20 Byte20.
  t z 21 Byte21.
  t z 22 Byte22.
  t z 23 Byte23.
  t z 24 Byte24.
  t z 25 Byte25.
  t z 26 Byte26.
  t z 27 Byte27.
  t z 28 Byte28.
  t z 29 Byte29.
  t z 30 Byte30.
  t z 31 Byte31.
  t z 32 Byte32.
  t z 33 Byte33.
  t z 34 Byte34.
  t z 35 Byte35.
  t z 36 Byte36.
  t z 37 Byte37.
  t z 38 Byte38.
  t z 39 Byte39.
  t z 40 Byte40.
  t z 41 Byte41.
  t z 42 Byte42.
  t z 43 Byte43.
  t z 44 Byte44.
  t z 45 Byte45.
  t z 46 Byte46.
  t z 47 Byte47.
  t z 48 Byte48.
  t z 49 Byte49.
  t z 50 Byte50.
  t z 51 Byte51.
  t z 52 Byte52.
  t z 53 Byte53.
  t z 54 Byte54.
  t z 55 Byte55.
  t z 56 Byte56.
  t z 57 Byte57.
  t z 58 Byte58.
  t z 59 Byte59.
  t z 60 Byte60.
  t z 61 Byte61.
  t z 62 Byte62.
  t z 63 Byte63.
  t z 64 Byte64.
  t z 65 Byte65.
  t z 66 Byte66.
  t z 67 Byte67.
  t z 68 Byte68.
  t z 69 Byte69.
  t z 70 Byte70.
  t z 71 Byte71.
  t z 72 Byte72.
  t z 73 Byte73.
  t z 74 Byte74.
  t z 75 Byte75.
  t z 76 Byte76.
  t z 77 Byte77.
  t z 78 Byte78.
  t z 79 Byte79.
  t z 80 Byte80.
  t z 81 Byte81.
  t z 82 Byte82.
  t z 83 Byte83.
  t z 84 Byte84.
  t z 85 Byte85.
  t z 86 Byte86.
  t z 87 Byte87.
  t z 88 Byte88.
  t z 89 Byte89.
  t z 90 Byte90.
  t z 91 Byte91.
  t z 92 Byte92.
  t z 93 Byte93.
  t z 94 Byte94.
  t z 95 Byte95.
  t z 96 Byte96.
  t z 97 Byte97.
  t z 98 Byte98.
  t z 99 Byte99.
  t z 100 Byte100.
  t z 101 Byte101.
  t z 102 Byte102.
  t z 103 Byte103.
  t z 104 Byte104.
  t z 105 Byte105.
  t z 106 Byte106.
  t z 107 Byte107.
  t z 108 Byte108.
  t z 109 Byte109.
  t z 110 Byte110.
  t z 111 Byte111.
  t z 112 Byte112.
  t z 113 Byte113.
  t z 114 Byte114.
  t z 115 Byte115.
  t z 116 Byte116.
  t z 117 Byte117.
  t z 118 Byte118.
  t z 119 Byte119.
  t z 120 Byte120.
  t z 121 Byte121.
  t z 122 Byte122.
  t z 123 Byte123.
  t z 124 Byte124.
  t z 125 Byte125.
  t z 126 Byte126.
  t z 127 Byte127.
  t z 128 Byte128.
  t z 129 Byte129.
  t z 130 Byte130.
  t z 131 Byte131.
  t z 132 Byte132.
  t z 133 Byte133.
  t z 134 Byte134.
  t z 135 Byte135.
  t z 136 Byte136.
  t z 137 Byte137.
  t z 138 Byte138.
  t z 139 Byte139.
  t z 140 Byte140.
  t z 141 Byte141.
  t z 142 Byte142.
  t z 143 Byte143.
  t z 144 Byte144.
  t z 145 Byte145.
  t z 146 Byte146.
  t z 147 Byte147.
  t z 148 Byte148.
  t z 149 Byte149.
  t z 150 Byte150.
  t z 151 Byte151.
  t z 152 Byte152.
  t z 153 Byte153.
  t z 154 Byte154.
  t z 155 Byte155.
  t z 156 Byte156.
  t z 157 Byte157.
  t z 158 Byte158.
  t z 159 Byte159.
  t z 160 Byte160.
  t z 161 Byte161.
  t z 162 Byte162.
  t z 163 Byte163.
  t z 164 Byte164.
  t z 165 Byte165.
  t z 166 Byte166.
  t z 167 Byte167.
  t z 168 Byte168.
  t z 169 Byte169.
  t z 170 Byte170.
  t z 171 Byte171.
  t z 172 Byte172.
  t z 173 Byte173.
  t z 174 Byte174.
  t z 175 Byte175.
  t z 176 Byte176.
  t z 177 Byte177.
  t z 178 Byte178.
  t z 179 Byte179.
  t z 180 Byte180.
  t z 181 Byte181.
  t z 182 Byte182.
  t z 183 Byte183.
  t z 184 Byte184.
  t z 185 Byte185.
  t z 186 Byte186.
  t z 187 Byte187.
  t z 188 Byte188.
  t z 189 Byte189.
  t z 190 Byte190.
  t z 191 Byte191.
  t z 192 Byte192.
  t z 193 Byte193.
  t z 194 Byte194.
  t z 195 Byte195.
  t z 196 Byte196.
  t z 197 Byte197.
  t z 198 Byte198.
  t z 199 Byte199.
  t z 200 Byte200.
  t z 201 Byte201.
  t z 202 Byte202.
  t z 203 Byte203.
  t z 204 Byte204.
  t z 205 Byte205.
  t z 206 Byte206.
  t z 207 Byte207.
  t z 208 Byte208.
  t z 209 Byte209.
  t z 210 Byte210.
  t z 211 Byte211.
  t z 212 Byte212.
  t z 213 Byte213.
  t z 214 Byte214.
  t z 215 Byte215.
  t z 216 Byte216.
  t z 217 Byte217.
  t z 218 Byte218.
  t z 219 Byte219.
  t z 220 Byte220.
  t z 221 Byte221.
  t z 222 Byte222.
  t z 223 Byte223.
  t z 224 Byte224.
  t z 225 Byte225.
  t z 226 Byte226.
  t z 227 Byte227.
  t z 228 Byte228.
  t z 229 Byte229.
  t z 230 Byte230.
  t z 231 Byte231.
  t z 232 Byte232.
  t z 233 Byte233.
  t z 234 Byte234.
  t z 235 Byte235.
  t z 236 Byte236.
  t z 237 Byte237.
  t z 238 Byte238.
  t z 239 Byte239.
  t z 240 Byte240.
  t z 241 Byte241.
  t z 242 Byte242.
  t z 243 Byte243.
  t z 244 Byte244.
  t z 245 Byte245.
  t z 246 Byte246.
  t z 247 Byte247.
  t z 248 Byte248.
  t z 249 Byte249.
  t z 250 Byte250.
  t z 251 Byte251.
  t z 252 Byte252.
  t z 253 Byte253.
  t z 254 Byte254.
  t z 255 Byte255.
  exfalso.
  lia.
Qed.
End byte.

Opaque u8_instance.u8.
