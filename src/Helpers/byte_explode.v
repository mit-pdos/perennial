From Coq Require Import ZArith.
From Perennial.Helpers Require Import Integers.
From stdpp Require Import base numbers.
Open Scope Z.

(** Induction principles for bytes and bit-offsets that allow proving theorems
  about bytes by case analysis on all possible values (256 for a byte and 8 for
  a valid bit offset), using [reflexivity] to prove each sub-goal.

  Coq seems to be able to handle theorems with a single byte and bit offset
 (2048 cases). Two bytes (~65,000 cases) seem to be a bit too much.

These theorems are themselves stated and proven by some auto-generated code that
lists out the values and considers each valid case in turn. After all the valid
cases we're able to prove a contradiction using [lia] since no values are left
for the byte/bit in question.

This file is slow so we limit it just to these two large theorems and put the
rest of the interesting stuff in bytes.v. I have to use vim with Coqtail to work
on this file, Proof General seems to fall over. *)

Transparent u8_instance.u8.
Local Lemma byte_destruct (P: u8 → Prop) :
  (∀ (z:Z) (Hunsigned_in_range: z `mod` 2^8 = z) (Hrange: 0 ≤ z < 2^8), P (Word8 ((Naive.mk z Hunsigned_in_range)))) →
  (∀ x, P x).
Proof.
  intros.
  pose proof (word.unsigned_range x).
  destruct x as [ [z ?] ].
  simpl in H0.
  apply H; auto.
Qed.

Lemma byte_explode (P: u8 → Prop)
    (* python3 -c 'print(" ".join([f"(Byte{i}: P (U8 {i}))" for i in range(256)]))' *)
    (Byte0: P (U8 0)) (Byte1: P (U8 1)) (Byte2: P (U8 2)) (Byte3: P (U8 3)) (Byte4: P (U8 4)) (Byte5: P (U8 5)) (Byte6: P (U8 6)) (Byte7: P (U8 7)) (Byte8: P (U8 8)) (Byte9: P (U8 9)) (Byte10: P (U8 10)) (Byte11: P (U8 11)) (Byte12: P (U8 12)) (Byte13: P (U8 13)) (Byte14: P (U8 14)) (Byte15: P (U8 15)) (Byte16: P (U8 16)) (Byte17: P (U8 17)) (Byte18: P (U8 18)) (Byte19: P (U8 19)) (Byte20: P (U8 20)) (Byte21: P (U8 21)) (Byte22: P (U8 22)) (Byte23: P (U8 23)) (Byte24: P (U8 24)) (Byte25: P (U8 25)) (Byte26: P (U8 26)) (Byte27: P (U8 27)) (Byte28: P (U8 28)) (Byte29: P (U8 29)) (Byte30: P (U8 30)) (Byte31: P (U8 31)) (Byte32: P (U8 32)) (Byte33: P (U8 33)) (Byte34: P (U8 34)) (Byte35: P (U8 35)) (Byte36: P (U8 36)) (Byte37: P (U8 37)) (Byte38: P (U8 38)) (Byte39: P (U8 39)) (Byte40: P (U8 40)) (Byte41: P (U8 41)) (Byte42: P (U8 42)) (Byte43: P (U8 43)) (Byte44: P (U8 44)) (Byte45: P (U8 45)) (Byte46: P (U8 46)) (Byte47: P (U8 47)) (Byte48: P (U8 48)) (Byte49: P (U8 49)) (Byte50: P (U8 50)) (Byte51: P (U8 51)) (Byte52: P (U8 52)) (Byte53: P (U8 53)) (Byte54: P (U8 54)) (Byte55: P (U8 55)) (Byte56: P (U8 56)) (Byte57: P (U8 57)) (Byte58: P (U8 58)) (Byte59: P (U8 59)) (Byte60: P (U8 60)) (Byte61: P (U8 61)) (Byte62: P (U8 62)) (Byte63: P (U8 63)) (Byte64: P (U8 64)) (Byte65: P (U8 65)) (Byte66: P (U8 66)) (Byte67: P (U8 67)) (Byte68: P (U8 68)) (Byte69: P (U8 69)) (Byte70: P (U8 70)) (Byte71: P (U8 71)) (Byte72: P (U8 72)) (Byte73: P (U8 73)) (Byte74: P (U8 74)) (Byte75: P (U8 75)) (Byte76: P (U8 76)) (Byte77: P (U8 77)) (Byte78: P (U8 78)) (Byte79: P (U8 79)) (Byte80: P (U8 80)) (Byte81: P (U8 81)) (Byte82: P (U8 82)) (Byte83: P (U8 83)) (Byte84: P (U8 84)) (Byte85: P (U8 85)) (Byte86: P (U8 86)) (Byte87: P (U8 87)) (Byte88: P (U8 88)) (Byte89: P (U8 89)) (Byte90: P (U8 90)) (Byte91: P (U8 91)) (Byte92: P (U8 92)) (Byte93: P (U8 93)) (Byte94: P (U8 94)) (Byte95: P (U8 95)) (Byte96: P (U8 96)) (Byte97: P (U8 97)) (Byte98: P (U8 98)) (Byte99: P (U8 99)) (Byte100: P (U8 100)) (Byte101: P (U8 101)) (Byte102: P (U8 102)) (Byte103: P (U8 103)) (Byte104: P (U8 104)) (Byte105: P (U8 105)) (Byte106: P (U8 106)) (Byte107: P (U8 107)) (Byte108: P (U8 108)) (Byte109: P (U8 109)) (Byte110: P (U8 110)) (Byte111: P (U8 111)) (Byte112: P (U8 112)) (Byte113: P (U8 113)) (Byte114: P (U8 114)) (Byte115: P (U8 115)) (Byte116: P (U8 116)) (Byte117: P (U8 117)) (Byte118: P (U8 118)) (Byte119: P (U8 119)) (Byte120: P (U8 120)) (Byte121: P (U8 121)) (Byte122: P (U8 122)) (Byte123: P (U8 123)) (Byte124: P (U8 124)) (Byte125: P (U8 125)) (Byte126: P (U8 126)) (Byte127: P (U8 127)) (Byte128: P (U8 128)) (Byte129: P (U8 129)) (Byte130: P (U8 130)) (Byte131: P (U8 131)) (Byte132: P (U8 132)) (Byte133: P (U8 133)) (Byte134: P (U8 134)) (Byte135: P (U8 135)) (Byte136: P (U8 136)) (Byte137: P (U8 137)) (Byte138: P (U8 138)) (Byte139: P (U8 139)) (Byte140: P (U8 140)) (Byte141: P (U8 141)) (Byte142: P (U8 142)) (Byte143: P (U8 143)) (Byte144: P (U8 144)) (Byte145: P (U8 145)) (Byte146: P (U8 146)) (Byte147: P (U8 147)) (Byte148: P (U8 148)) (Byte149: P (U8 149)) (Byte150: P (U8 150)) (Byte151: P (U8 151)) (Byte152: P (U8 152)) (Byte153: P (U8 153)) (Byte154: P (U8 154)) (Byte155: P (U8 155)) (Byte156: P (U8 156)) (Byte157: P (U8 157)) (Byte158: P (U8 158)) (Byte159: P (U8 159)) (Byte160: P (U8 160)) (Byte161: P (U8 161)) (Byte162: P (U8 162)) (Byte163: P (U8 163)) (Byte164: P (U8 164)) (Byte165: P (U8 165)) (Byte166: P (U8 166)) (Byte167: P (U8 167)) (Byte168: P (U8 168)) (Byte169: P (U8 169)) (Byte170: P (U8 170)) (Byte171: P (U8 171)) (Byte172: P (U8 172)) (Byte173: P (U8 173)) (Byte174: P (U8 174)) (Byte175: P (U8 175)) (Byte176: P (U8 176)) (Byte177: P (U8 177)) (Byte178: P (U8 178)) (Byte179: P (U8 179)) (Byte180: P (U8 180)) (Byte181: P (U8 181)) (Byte182: P (U8 182)) (Byte183: P (U8 183)) (Byte184: P (U8 184)) (Byte185: P (U8 185)) (Byte186: P (U8 186)) (Byte187: P (U8 187)) (Byte188: P (U8 188)) (Byte189: P (U8 189)) (Byte190: P (U8 190)) (Byte191: P (U8 191)) (Byte192: P (U8 192)) (Byte193: P (U8 193)) (Byte194: P (U8 194)) (Byte195: P (U8 195)) (Byte196: P (U8 196)) (Byte197: P (U8 197)) (Byte198: P (U8 198)) (Byte199: P (U8 199)) (Byte200: P (U8 200)) (Byte201: P (U8 201)) (Byte202: P (U8 202)) (Byte203: P (U8 203)) (Byte204: P (U8 204)) (Byte205: P (U8 205)) (Byte206: P (U8 206)) (Byte207: P (U8 207)) (Byte208: P (U8 208)) (Byte209: P (U8 209)) (Byte210: P (U8 210)) (Byte211: P (U8 211)) (Byte212: P (U8 212)) (Byte213: P (U8 213)) (Byte214: P (U8 214)) (Byte215: P (U8 215)) (Byte216: P (U8 216)) (Byte217: P (U8 217)) (Byte218: P (U8 218)) (Byte219: P (U8 219)) (Byte220: P (U8 220)) (Byte221: P (U8 221)) (Byte222: P (U8 222)) (Byte223: P (U8 223)) (Byte224: P (U8 224)) (Byte225: P (U8 225)) (Byte226: P (U8 226)) (Byte227: P (U8 227)) (Byte228: P (U8 228)) (Byte229: P (U8 229)) (Byte230: P (U8 230)) (Byte231: P (U8 231)) (Byte232: P (U8 232)) (Byte233: P (U8 233)) (Byte234: P (U8 234)) (Byte235: P (U8 235)) (Byte236: P (U8 236)) (Byte237: P (U8 237)) (Byte238: P (U8 238)) (Byte239: P (U8 239)) (Byte240: P (U8 240)) (Byte241: P (U8 241)) (Byte242: P (U8 242)) (Byte243: P (U8 243)) (Byte244: P (U8 244)) (Byte245: P (U8 245)) (Byte246: P (U8 246)) (Byte247: P (U8 247)) (Byte248: P (U8 248)) (Byte249: P (U8 249)) (Byte250: P (U8 250)) (Byte251: P (U8 251)) (Byte252: P (U8 252)) (Byte253: P (U8 253)) (Byte254: P (U8 254)) (Byte255: P (U8 255)) :
    (∀ x, P x).
Proof.
  apply byte_destruct.
  intros z ? Hlt.

  let t n c :=
    destruct (decide (z = n)) as [->|?];
    [ refine (eq_rect (U8 n) P c _ _);
      apply (@int_Z_inj 8 u8_instance.u8 u8_instance.u8_word_ok); vm_compute; reflexivity
    |] in
  (* python3 -c 'print(";\n".join([f"t {i} Byte{i}" for i in range(256)]) + ".")' *)
  t 0 Byte0;
  t 1 Byte1;
  t 2 Byte2;
  t 3 Byte3;
  t 4 Byte4;
  t 5 Byte5;
  t 6 Byte6;
  t 7 Byte7;
  t 8 Byte8;
  t 9 Byte9;
  t 10 Byte10;
  t 11 Byte11;
  t 12 Byte12;
  t 13 Byte13;
  t 14 Byte14;
  t 15 Byte15;
  t 16 Byte16;
  t 17 Byte17;
  t 18 Byte18;
  t 19 Byte19;
  t 20 Byte20;
  t 21 Byte21;
  t 22 Byte22;
  t 23 Byte23;
  t 24 Byte24;
  t 25 Byte25;
  t 26 Byte26;
  t 27 Byte27;
  t 28 Byte28;
  t 29 Byte29;
  t 30 Byte30;
  t 31 Byte31;
  t 32 Byte32;
  t 33 Byte33;
  t 34 Byte34;
  t 35 Byte35;
  t 36 Byte36;
  t 37 Byte37;
  t 38 Byte38;
  t 39 Byte39;
  t 40 Byte40;
  t 41 Byte41;
  t 42 Byte42;
  t 43 Byte43;
  t 44 Byte44;
  t 45 Byte45;
  t 46 Byte46;
  t 47 Byte47;
  t 48 Byte48;
  t 49 Byte49;
  t 50 Byte50;
  t 51 Byte51;
  t 52 Byte52;
  t 53 Byte53;
  t 54 Byte54;
  t 55 Byte55;
  t 56 Byte56;
  t 57 Byte57;
  t 58 Byte58;
  t 59 Byte59;
  t 60 Byte60;
  t 61 Byte61;
  t 62 Byte62;
  t 63 Byte63;
  t 64 Byte64;
  t 65 Byte65;
  t 66 Byte66;
  t 67 Byte67;
  t 68 Byte68;
  t 69 Byte69;
  t 70 Byte70;
  t 71 Byte71;
  t 72 Byte72;
  t 73 Byte73;
  t 74 Byte74;
  t 75 Byte75;
  t 76 Byte76;
  t 77 Byte77;
  t 78 Byte78;
  t 79 Byte79;
  t 80 Byte80;
  t 81 Byte81;
  t 82 Byte82;
  t 83 Byte83;
  t 84 Byte84;
  t 85 Byte85;
  t 86 Byte86;
  t 87 Byte87;
  t 88 Byte88;
  t 89 Byte89;
  t 90 Byte90;
  t 91 Byte91;
  t 92 Byte92;
  t 93 Byte93;
  t 94 Byte94;
  t 95 Byte95;
  t 96 Byte96;
  t 97 Byte97;
  t 98 Byte98;
  t 99 Byte99;
  t 100 Byte100;
  t 101 Byte101;
  t 102 Byte102;
  t 103 Byte103;
  t 104 Byte104;
  t 105 Byte105;
  t 106 Byte106;
  t 107 Byte107;
  t 108 Byte108;
  t 109 Byte109;
  t 110 Byte110;
  t 111 Byte111;
  t 112 Byte112;
  t 113 Byte113;
  t 114 Byte114;
  t 115 Byte115;
  t 116 Byte116;
  t 117 Byte117;
  t 118 Byte118;
  t 119 Byte119;
  t 120 Byte120;
  t 121 Byte121;
  t 122 Byte122;
  t 123 Byte123;
  t 124 Byte124;
  t 125 Byte125;
  t 126 Byte126;
  t 127 Byte127;
  t 128 Byte128;
  t 129 Byte129;
  t 130 Byte130;
  t 131 Byte131;
  t 132 Byte132;
  t 133 Byte133;
  t 134 Byte134;
  t 135 Byte135;
  t 136 Byte136;
  t 137 Byte137;
  t 138 Byte138;
  t 139 Byte139;
  t 140 Byte140;
  t 141 Byte141;
  t 142 Byte142;
  t 143 Byte143;
  t 144 Byte144;
  t 145 Byte145;
  t 146 Byte146;
  t 147 Byte147;
  t 148 Byte148;
  t 149 Byte149;
  t 150 Byte150;
  t 151 Byte151;
  t 152 Byte152;
  t 153 Byte153;
  t 154 Byte154;
  t 155 Byte155;
  t 156 Byte156;
  t 157 Byte157;
  t 158 Byte158;
  t 159 Byte159;
  t 160 Byte160;
  t 161 Byte161;
  t 162 Byte162;
  t 163 Byte163;
  t 164 Byte164;
  t 165 Byte165;
  t 166 Byte166;
  t 167 Byte167;
  t 168 Byte168;
  t 169 Byte169;
  t 170 Byte170;
  t 171 Byte171;
  t 172 Byte172;
  t 173 Byte173;
  t 174 Byte174;
  t 175 Byte175;
  t 176 Byte176;
  t 177 Byte177;
  t 178 Byte178;
  t 179 Byte179;
  t 180 Byte180;
  t 181 Byte181;
  t 182 Byte182;
  t 183 Byte183;
  t 184 Byte184;
  t 185 Byte185;
  t 186 Byte186;
  t 187 Byte187;
  t 188 Byte188;
  t 189 Byte189;
  t 190 Byte190;
  t 191 Byte191;
  t 192 Byte192;
  t 193 Byte193;
  t 194 Byte194;
  t 195 Byte195;
  t 196 Byte196;
  t 197 Byte197;
  t 198 Byte198;
  t 199 Byte199;
  t 200 Byte200;
  t 201 Byte201;
  t 202 Byte202;
  t 203 Byte203;
  t 204 Byte204;
  t 205 Byte205;
  t 206 Byte206;
  t 207 Byte207;
  t 208 Byte208;
  t 209 Byte209;
  t 210 Byte210;
  t 211 Byte211;
  t 212 Byte212;
  t 213 Byte213;
  t 214 Byte214;
  t 215 Byte215;
  t 216 Byte216;
  t 217 Byte217;
  t 218 Byte218;
  t 219 Byte219;
  t 220 Byte220;
  t 221 Byte221;
  t 222 Byte222;
  t 223 Byte223;
  t 224 Byte224;
  t 225 Byte225;
  t 226 Byte226;
  t 227 Byte227;
  t 228 Byte228;
  t 229 Byte229;
  t 230 Byte230;
  t 231 Byte231;
  t 232 Byte232;
  t 233 Byte233;
  t 234 Byte234;
  t 235 Byte235;
  t 236 Byte236;
  t 237 Byte237;
  t 238 Byte238;
  t 239 Byte239;
  t 240 Byte240;
  t 241 Byte241;
  t 242 Byte242;
  t 243 Byte243;
  t 244 Byte244;
  t 245 Byte245;
  t 246 Byte246;
  t 247 Byte247;
  t 248 Byte248;
  t 249 Byte249;
  t 250 Byte250;
  t 251 Byte251;
  t 252 Byte252;
  t 253 Byte253;
  t 254 Byte254;
  t 255 Byte255.
  exfalso; lia.
Qed.

Lemma bit_off_explode (P: u64 → Prop)
  (Bit0: P (U64 0)) (Bit1: P (U64 1)) (Bit2: P (U64 2)) (Bit3: P (U64 3)) (Bit4: P (U64 4)) (Bit5: P (U64 5)) (Bit6: P (U64 6)) (Bit7: P (U64 7)) :
  ∀ (bit: u64),
    int.Z bit < 8 →
    P bit.
Proof.
  intros bit Hbound.
  destruct (decide (int.Z bit = 0)) as [Heq|]; [ refine (eq_rect _ _ Bit0 _ _); apply (inj int.Z); rewrite Heq; reflexivity |].
  destruct (decide (int.Z bit = 1)) as [Heq|]; [ refine (eq_rect _ _ Bit1 _ _); apply (inj int.Z); rewrite Heq; reflexivity |].
  destruct (decide (int.Z bit = 2)) as [Heq|]; [ refine (eq_rect _ _ Bit2 _ _); apply (inj int.Z); rewrite Heq; reflexivity |].
  destruct (decide (int.Z bit = 3)) as [Heq|]; [ refine (eq_rect _ _ Bit3 _ _); apply (inj int.Z); rewrite Heq; reflexivity |].
  destruct (decide (int.Z bit = 4)) as [Heq|]; [ refine (eq_rect _ _ Bit4 _ _); apply (inj int.Z); rewrite Heq; reflexivity |].
  destruct (decide (int.Z bit = 5)) as [Heq|]; [ refine (eq_rect _ _ Bit5 _ _); apply (inj int.Z); rewrite Heq; reflexivity |].
  destruct (decide (int.Z bit = 6)) as [Heq|]; [ refine (eq_rect _ _ Bit6 _ _); apply (inj int.Z); rewrite Heq; reflexivity |].
  destruct (decide (int.Z bit = 7)) as [Heq|]; [ refine (eq_rect _ _ Bit7 _ _); apply (inj int.Z); rewrite Heq; reflexivity |].
  exfalso; word.
Qed.

Opaque u8_instance.u8.
