(* ========================================================================= *)
(* NIST SP 800-38D GHASH multiplication — faithful transcription             *)
(*                                                                           *)
(* Implements Algorithm 1 (Section 6.3) and Algorithm 2 (Section 6.4)        *)
(* exactly as defined in NIST Special Publication 800-38D, November 2007.    *)
(*                                                                           *)
(* The NIST bit convention: a 128-bit block is a bit string x_0 x_1 ... x_127 *)
(* where x_0 is the MSB of byte 0.  In HOL Light's 128-bit word, byte 0     *)
(* occupies bits 0-7 with bit 0 = LSB.  The mapping is:                      *)
(*   NIST bit (8k + j)  <-->  HOL Light bit (8k + 7 - j)                    *)
(*                                                                           *)
(* This file defines the NIST operations directly in terms of this mapping,  *)
(* without introducing any intermediate "bit reversal" abstraction.          *)
(* ========================================================================= *)

(* Load the full algebraic proof chain from nebeid's ghash-polyval branch:
   ghash.ml -> polyval.ml -> polyval_prop3_proof.ml -> karatsuba_pmul_proof.ml -> ghash_spec.ml
   This gives us: polyval_dot, ghash_polyval_acc, PMUL_KARATSUBA,
   POLYVAL_REDUCE_PROP3_CORRECT, h_power, ghash_wide, htable predicates, etc. *)
needs "common/ghash_spec.ml";;
needs "arm/proofs/utils/gcm_gmult_v8_spec.ml";;

(* ---- NIST bit-level operations on 128-bit blocks ----------------------- *)

(* NIST bit x_i of block X: x_0 = MSB of byte 0 = HOL bit 7,
   x_1 = next bit = HOL bit 6, ..., x_7 = LSB of byte 0 = HOL bit 0,
   x_8 = MSB of byte 1 = HOL bit 15, etc.

   General formula: NIST bit i (where i = 8*k + j, 0 <= j < 8)
   maps to HOL bit 8*k + (7 - j) = 8*(i DIV 8) + 7 - i MOD 8. *)
let nist_bit = new_definition
  `nist_bit (x:int128) (i:num) =
   bit (8 * (i DIV 8) + 7 - i MOD 8) x`;;

(* NIST LSB_1(V): the rightmost bit = NIST bit 127 = HOL bit 120. *)
let nist_lsb = new_definition
  `nist_lsb (v:int128) = bit 120 v`;;

(* NIST right shift V >> 1: shift the bit string right by one position.
   x_0 x_1 ... x_127  -->  0 x_0 x_1 ... x_126

   In HOL Light bit terms, bit h of (nist_shr1 v):
   - If h MOD 8 < 7: bit (h + 1) of v    (shift within byte)
   - If h = 7:       F                     (NIST bit 0 = cleared)
   - If h MOD 8 = 7 and h > 7: bit (h - 15) of v  (carry across bytes) *)
let nist_shr1 = new_definition
  `nist_shr1 (v:int128) : int128 =
   (word_of_bits
     {k | k < 128 /\
          (if k MOD 8 < 7 then bit (k + 1) v
           else if k = 7 then F
           else bit (k - 15) v)} : int128)`;;

(* ---- Algorithm 1: X • Y (Section 6.3) --------------------------------- *)

(* R = 11100001 || 0^120.  In the HOL word representation:
   byte 0 = 0xE1 (bits 0-7, with bit 7 = NIST x_0 = 1,
   bit 6 = NIST x_1 = 1, bit 5 = NIST x_2 = 1,
   bit 0 = NIST x_7 = 1, bits 1-4 = 0).
   All other bytes = 0.  So R = word 0xE1 = word 225. *)
let ghash_R = new_definition
  `ghash_R : int128 = word 0xE1`;;

(* The loop body of Algorithm 1.  We count down the remaining steps:
   ghash_mul_loop Z V X 0 = Z   (done, return Z_128)
   ghash_mul_loop Z V X (SUC n) =
     process bit x_i where i = 128 - SUC n, then recurse with n.

   This iterates i = 0, 1, ..., 127 as n counts down from 128 to 0. *)
let ghash_mul_loop = define
  `ghash_mul_loop (z:int128) (v:int128) (x:int128) 0 = z /\
   ghash_mul_loop z v x (SUC n) =
     let i = 128 - SUC n in
     let z' = if nist_bit x i then word_xor z v else z in
     let v' = if nist_lsb v
              then word_xor (nist_shr1 v) ghash_R
              else nist_shr1 v in
     ghash_mul_loop z' v' x n`;;

(* Algorithm 1: X • Y
   Steps:
   1. Let x_0 x_1 ... x_127 denote the bits of X.
   2. Let Z_0 = 0^128 and V_0 = Y.
   3. For i = 0 to 127, compute Z_{i+1} and V_{i+1}.
   4. Return Z_128. *)
let nist_ghash_mul = new_definition
  `nist_ghash_mul (x:int128) (y:int128) : int128 =
   ghash_mul_loop (word 0) y x 128`;;

(* ---- Algorithm 2: GHASH_H(X) (Section 6.4) ----------------------------- *)

(* GHASH_H(X) where X = X_1 || X_2 || ... || X_m:
     Y_0 = 0^128
     For i = 1,...,m: Y_i = (Y_{i-1} XOR X_i) • H
     Return Y_m *)
let nist_ghash = define
  `nist_ghash (h:int128) (acc:int128) [] = acc /\
   nist_ghash h acc (CONS x xs) =
     nist_ghash h (nist_ghash_mul (word_xor acc x) h) xs`;;

(* ========================================================================= *)
(* Bridge A: NIST Algorithm 1 = polynomial multiplication mod P(x)           *)
(*                                                                           *)
(* The NIST shift-and-XOR loop computes the same result as:                  *)
(*   bit_reverse_per_byte(ghash_reduce(word_pmul(brp X)(brp Y)))             *)
(* where brp = bit_reverse_per_byte converts between NIST bit order and      *)
(* the natural polynomial bit order used by poly_of_word / word_pmul.        *)
(*                                                                           *)
(* Key insight: NIST "right shift" (V >> 1) = multiplication by the          *)
(* polynomial variable u in GF(2)[x].  In natural bit order (after brp),     *)
(* this is word_shl by 1 (shift towards MSB = higher polynomial degree).     *)
(* The conditional XOR with R implements reduction mod P(u) when the         *)
(* u^127 coefficient overflows into u^128.                                   *)
(* ========================================================================= *)

(* Per-byte bit reversal: reverses bits within each byte, keeping bytes
   in the same position.  Composed as full bit reversal + byte reversal.
   This converts between NIST bit ordering and HOL Light's poly_of_word. *)
let bit_reverse_per_byte = new_definition
  `bit_reverse_per_byte (x:int128) : int128 =
   word_reversefields 8 (word_reversefields 1 x)`;;

(* NIST bit i of x = natural bit i of brp(x).
   This is the fundamental bridge between NIST and polynomial conventions. *)
let NIST_BIT_AS_NATURAL = prove(
  `!x:int128. !i. i < 128 ==>
    (nist_bit x i <=> bit i (bit_reverse_per_byte x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[nist_bit; bit_reverse_per_byte; BIT_WORD_REVERSEFIELDS;
              DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `8 * (15 - i DIV 8) + i MOD 8 < 128` ASSUME_TAC THENL
   [MP_TAC(SPEC `i:num` (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`))) THEN
    UNDISCH_TAC `i < 128` THEN ARITH_TAC;
    ASM_REWRITE_TAC[DIV_1; MOD_1; MULT_CLAUSES; ADD_0] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPEC `i:num` (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`))) THEN
    UNDISCH_TAC `i < 128` THEN ARITH_TAC]);;

(* NIST LSB_1(V) = bit 127 of brp(V) = the highest polynomial coefficient. *)
let NIST_LSB_AS_NATURAL = prove(
  `!v:int128. nist_lsb v <=> bit 127 (bit_reverse_per_byte v)`,
  GEN_TAC THEN REWRITE_TAC[nist_lsb] THEN
  MP_TAC(SPECL [`v:int128`; `127`] NIST_BIT_AS_NATURAL) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[nist_bit] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]));;

(* R in natural bit order = word 0x87 = x^7 + x^2 + x + 1 = P(x) - x^128.
   brp reverses bits within each byte: 0xE1 = 11100001 → 10000111 = 0x87. *)
let BRP_GHASH_R = prove(
  `bit_reverse_per_byte ghash_R = (word 0x87 : int128)`,
  REWRITE_TAC[bit_reverse_per_byte; ghash_R] THEN
  SUBGOAL_THEN `word_reversefields 1 (word 0xE1:(128)word) =
                word 179445779430963642842013953137846517760`
    SUBST1_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `word_reversefields 8
    (word 179445779430963642842013953137846517760:(128)word) = word 135`
    SUBST1_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ---- Helper: bound on NIST-to-HOL bit index ----------------------------- *)

let NIST_HOL_BIT_BOUND = prove(
  `!k. k < 128 ==> 8 * k DIV 8 + 7 - k MOD 8 < 128`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `8`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `k DIV 8 < 16` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_ARITH_TAC]);;

(* ---- Arithmetic helpers ------------------------------------------------- *)

let SUB_8Q_PLUS_7 = prove(
  `!q. 1 <= q ==> (8 * q + 7) - 15 = 8 * (q - 1)`,
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC q + 7 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * q + 7))))))))`;
              SUC_SUB1] THEN ARITH_TAC);;

let EIGHT_MUL_SUB = prove(
  `!q. 1 <= q ==> 8 * q - 8 = 8 * (q - 1)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `q = (q - 1) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ARITH_TAC]);;

(* ---- NIST_SHR1_BIT: nist_shr1 shifts NIST bits right by 1 -------------- *)

(* This is the core lemma for Bridge A. It says that nist_shr1 does
   exactly what the NIST spec says: bit 0 becomes 0, and bit k becomes
   the old bit k-1. *)
let NIST_SHR1_BIT = prove(
  `!v:int128. !k. k < 128 ==>
    (nist_bit (nist_shr1 v) k <=> if k = 0 then F else nist_bit v (k - 1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[nist_bit; nist_shr1; BIT_WORD_OF_BITS; IN_ELIM_THM; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `8`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = k DIV 8` THEN ABBREV_TAC `r = k MOD 8` THEN STRIP_TAC THEN
  SUBGOAL_THEN `q < 16` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `q * 8 = 8 * q`]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
  ASM_CASES_TAC `r = 0` THENL
   [SUBGOAL_THEN `1 <= q` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[nist_bit; nist_shr1; BIT_WORD_OF_BITS; IN_ELIM_THM;
                    DIMINDEX_128; ADD_0; SUB_0] THEN
    SIMP_TAC[DIV_MULT; MOD_MULT; ARITH_RULE `~(8=0)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `(8*q+7) MOD 8 = 7` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `8*q+7 < 128 /\ ~(8*q+7=7)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SUB_8Q_PLUS_7] THEN
    SUBGOAL_THEN `(8 * q) - 1 = (q-1)*8 + 7` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_RULE `~(8=0)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0; SUB_REFL];
    SUBGOAL_THEN `1 <= r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[nist_bit; nist_shr1; BIT_WORD_OF_BITS; IN_ELIM_THM; DIMINDEX_128] THEN
    SUBGOAL_THEN `(8*q+r) DIV 8 = q /\ (8*q+r) MOD 8 = r`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r:num` THEN ASM_ARITH_TAC;
        MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num` THEN ASM_ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `(8*q+(7-r)) MOD 8 = 7-r /\ 8*q+(7-r) < 128 /\
                  ~(8*q+r=0) /\ 7-r < 7`
      (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num` THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `(8 * q + r) - 1 = q * 8 + (r - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_RULE `~(8=0)`] THEN
    SUBGOAL_THEN `(r-1) DIV 8 = 0 /\ (r-1) MOD 8 = r-1`
      (fun th -> REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[DIV_LT; MOD_LT; ARITH_RULE `r < 8 /\ 1 <= r ==> r-1 < 8`]; ALL_TAC] THEN
    REWRITE_TAC[ADD_0; MULT_0; ARITH_RULE `q * 8 = 8 * q`] THEN
    SUBGOAL_THEN `(8 * q + (7 - r)) + 1 = 8 * q + (7 - (r - 1))`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* Bridge A: NIST loop ↔ polynomial multiplication in natural bit order      *)
(* ========================================================================= *)

(* brp distributes over XOR *)
let BRP_XOR = prove(
  `!a b:int128. bit_reverse_per_byte(word_xor a b) =
                word_xor (bit_reverse_per_byte a) (bit_reverse_per_byte b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit_reverse_per_byte] THEN
  CONV_TAC WORD_BLAST);;

(* NIST shr1 in natural order = word_shl by 1 (multiply by u) *)
let NIST_SHR1_AS_SHL = prove(
  `!v:int128. bit_reverse_per_byte(nist_shr1 v) =
              word_shl (bit_reverse_per_byte v) 1`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_128] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_SHL; DIMINDEX_128] THEN
  MP_TAC(SPECL [`nist_shr1 (v:int128)`; `k:num`] NIST_BIT_AS_NATURAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o GSYM) THEN
  MP_TAC(SPECL [`v:int128`; `k:num`] NIST_SHR1_BIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `1 <= k` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`v:int128`; `k - 1`] NIST_BIT_AS_NATURAL) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o GSYM)] THEN
  REWRITE_TAC[]);;

(* V-step: brp of the full V-update = polynomial multiply-by-u with reduction *)
let V_STEP_BRP = prove(
  `!v:int128.
    bit_reverse_per_byte
      (if nist_lsb v then word_xor (nist_shr1 v) ghash_R else nist_shr1 v) =
    (if bit 127 (bit_reverse_per_byte v)
     then word_xor (word_shl (bit_reverse_per_byte v) 1) (word 0x87)
     else word_shl (bit_reverse_per_byte v) 1)`,
  GEN_TAC THEN REWRITE_TAC[NIST_LSB_AS_NATURAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[BRP_XOR; NIST_SHR1_AS_SHL; BRP_GHASH_R];
    REWRITE_TAC[NIST_SHR1_AS_SHL]]);;

(* Z-step: brp of the conditional Z-update *)
let Z_STEP_BRP = prove(
  `!z v x:int128. !i. i < 128 ==>
    bit_reverse_per_byte
      (if nist_bit x i then word_xor z v else z) =
    (if bit i (bit_reverse_per_byte x)
     then word_xor (bit_reverse_per_byte z) (bit_reverse_per_byte v)
     else bit_reverse_per_byte z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:int128`; `i:num`] NIST_BIT_AS_NATURAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[BRP_XOR]);;

(* ---- Polynomial loop (natural bit order version of Algorithm 1) --------- *)

(* The same loop as ghash_mul_loop but in natural polynomial bit order:
   V-update = word_shl + conditional XOR with 0x87
   Z-update = conditional XOR based on natural bit *)
let poly_mul_loop = define
  `poly_mul_loop (z:int128) (v:int128) (x:int128) 0 = z /\
   poly_mul_loop z v x (SUC n) =
     let i = 128 - SUC n in
     let z' = if bit i x then word_xor z v else z in
     let v' = if bit 127 v
              then word_xor (word_shl v 1) (word 0x87)
              else word_shl v 1 in
     poly_mul_loop z' v' x n`;;

(* ---- LOOP_BRP: brp commutes with the loop ------------------------------ *)

(* The NIST loop after brp equals the polynomial loop.
   Proved by induction using V_STEP_BRP and Z_STEP_BRP. *)
let LOOP_BRP = prove(
  `!n z v x:int128.
    bit_reverse_per_byte(ghash_mul_loop z v x n) =
    poly_mul_loop (bit_reverse_per_byte z) (bit_reverse_per_byte v)
                  (bit_reverse_per_byte x) n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ghash_mul_loop; poly_mul_loop];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[ghash_mul_loop; poly_mul_loop; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    SUBGOAL_THEN `128 - SUC n < 128` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun ih -> GEN_REWRITE_TAC LAND_CONV [ih]) THEN
    MP_TAC(SPECL [`z:int128`; `v:int128`; `x:int128`; `128 - SUC n`] Z_STEP_BRP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPEC `v:int128` V_STEP_BRP) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* brp(0) = 0 *)
let BRP_ZERO = prove(
  `bit_reverse_per_byte (word 0 : int128) = word 0`,
  REWRITE_TAC[bit_reverse_per_byte] THEN CONV_TAC WORD_REDUCE_CONV);;

(* ---- Top-level: brp(nist_ghash_mul) = poly_mul_loop -------------------- *)

let NIST_GHASH_MUL_AS_POLY_LOOP = prove(
  `!x y:int128.
    bit_reverse_per_byte(nist_ghash_mul x y) =
    poly_mul_loop (word 0) (bit_reverse_per_byte y) (bit_reverse_per_byte x) 128`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nist_ghash_mul; LOOP_BRP; BRP_ZERO]);;

(* ---- Uniqueness of 128-bit representatives mod P(x) --------------------- *)

let BOOL_POLY_MUL_EQ = prove(
  `ring_mul bool_poly = poly_mul bool_ring`,
  REWRITE_TAC[bool_poly; POLY_RING]);;

let BOOL_POLY_ZERO_EQ = prove(
  `ring_0 bool_poly = poly_0 bool_ring`,
  REWRITE_TAC[bool_poly; POLY_RING]);;

(* INTEGRAL_DOMAIN_BOOL_POLY already proved in ghash_spec.ml *)

let GHASH_POLY_NONZERO = prove(
  `~(ghash_poly = ring_0 bool_poly)`,
  REWRITE_TAC[bool_poly; POLY_RING] THEN
  DISCH_THEN(MP_TAC o AP_TERM `poly_deg bool_ring:((1->num)->bool)->num`) THEN
  REWRITE_TAC[POLY_DEG_GHASH_POLY; bool_poly; POLY_RING; POLY_DEG_0] THEN
  ARITH_TAC);;

let GHASH_DIVIDES_LOW_DEG = prove(
  `!p:(1->num)->bool. p IN ring_carrier bool_poly /\
       ring_divides bool_poly ghash_poly p /\
       poly_deg bool_ring p < 128
       ==> p = ring_0 bool_poly`,
  GEN_TAC THEN ASM_CASES_TAC `p:(1->num)->bool = ring_0 bool_poly` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `poly_deg bool_ring (p:(1->num)->bool) >= 128` MP_TAC THENL
   [ALL_TAC; ASM_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_divides]) THEN
  ASM_REWRITE_TAC[GHASH_BOOL_POLY] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(q:(1->num)->bool = ring_0 bool_poly)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MUL_RZERO; GHASH_BOOL_POLY]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[GE; BOOL_POLY_MUL_EQ] THEN
  SUBGOAL_THEN
    `poly_deg bool_ring (poly_mul bool_ring ghash_poly (q:(1->num)->bool)) =
     poly_deg bool_ring ghash_poly + poly_deg bool_ring q`
    (fun th -> REWRITE_TAC[th; POLY_DEG_GHASH_POLY] THEN ARITH_TAC) THEN
  MATCH_MP_TAC POLY_DEG_MUL THEN
  REWRITE_TAC[INTEGRAL_DOMAIN_BOOL_RING; RING_POLYNOMIAL_GHASH_POLY] THEN
  SUBGOAL_THEN `ring_polynomial bool_ring (q:(1->num)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `(q:(1->num)->bool) IN ring_carrier bool_poly` THEN
    REWRITE_TAC[bool_poly; POLY_RING; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM BOOL_POLY_ZERO_EQ] THEN
  ASM_MESON_TAC[GHASH_POLY_NONZERO; BOOL_POLY_ZERO_EQ]);;

(* MOD_GHASH_WORD_EQ: congruent 128-bit words mod P(x) are equal.
   The linchpin theorem — unique representative in degree < 128. *)
let MOD_GHASH_WORD_EQ = prove(
  `!(x:128 word) (y:128 word).
    (poly_of_word x == poly_of_word y) (mod_ghash) ==> x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cong] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM WORD_XOR_EQ_0] THEN
  MATCH_MP_TAC(INST_TYPE [`:128`,`:N`] POLY_OF_WORD_INJ) THEN
  REWRITE_TAC[POLY_OF_WORD_0] THEN
  MATCH_MP_TAC GHASH_DIVIDES_LOW_DEG THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[mod_ghash; BOOL_POLY_OF_WORD]) THEN
    STRIP_TAC THEN
    REWRITE_TAC[POLY_OF_WORD_XOR; GSYM BOOL_POLY_SUB] THEN
    FIRST_X_ASSUM(MP_TAC o
      REWRITE_RULE[REWRITE_RULE[GHASH_BOOL_POLY]
        (SPEC `ghash_poly:(1->num)->bool`
          (REWRITE_RULE[GHASH_BOOL_POLY]
            (ISPEC `bool_poly` IN_IDEAL_GENERATED_SING_EQ)))]) THEN
    REWRITE_TAC[];
    MATCH_MP_TAC(ARITH_RULE `x <= 127 ==> x < 128`) THEN
    REWRITE_TAC[POLY_DEG_POLY_OF_WORD] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC]);;

(* ========================================================================= *)
(* Key equivalence: gcm_gmult_spec = polyval_dot via byteswap128             *)
(*                                                                           *)
(* GCM_GMULT_POLYVAL_DOT:                                                   *)
(*   !xi h. let H = byteswap128 h in                                        *)
(*     gcm_gmult_spec xi h (word_zx(karatsuba_mid H)) =                     *)
(*     word_reversefields 8 (polyval_dot (word_reversefields 8 xi) H)        *)
(*                                                                           *)
(* This connects the ARM implementation spec to nebeid's algebraic           *)
(* polyval_dot, which already has all the mod Q(x) congruence proofs.        *)
(*                                                                           *)
(* Validated on NIST Test Case 2 concrete values.                            *)
(*                                                                           *)
(* Proof strategy:                                                           *)
(* 1. Expand both sides with PMUL_KARATSUBA + KARATSUBA_LIMBS               *)
(* 2. Abbreviate the 3 Karatsuba pmull results (xl, xh, xm)                 *)
(* 3. Use SPEC_XM_PRIME_AS_ABCD: relate Karatsuba middle term to Prop3 limbs*)
(* 4. Use REDUCTION_EQUIV: spec's 2-phase reduction = Prop3's reduction     *)
(*    (proved by WORD_BLAST on 256 Boolean variables = 4 x 64-bit limbs)    *)
(* ========================================================================= *)

(* --- Helper: Karatsuba 256-bit product limb extractions --- *)

let KARATSUBA_LIMB_A = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (0,64) : 64 word =
    word_subword xl (0,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_B = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (64,64) : 64 word =
    word_xor (word_subword xl (64,64)) (word_subword mid (0,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_C = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (128,64) : 64 word =
    word_xor (word_subword xh (0,64)) (word_subword mid (64,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_D = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (192,64) : 64 word =
    word_subword xh (64,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMBS = CONJ (CONJ KARATSUBA_LIMB_A KARATSUBA_LIMB_B)
                           (CONJ KARATSUBA_LIMB_C KARATSUBA_LIMB_D);;

(* --- Helper: xm' halves = Karatsuba ABCD limbs B and C --- *)

let SPEC_XM_PRIME_AS_ABCD = prove(
  `!(xl:int128) (xh:int128) (xm:int128).
    let mid = word_xor (word_xor xm xl) xh in
    let xm' = word_xor (word_xor xl xh)
              (word_xor (word_subword (word_join xh xl : 256 word) (64,128) : int128) xm) in
    word_subword xm' (0,64) : 64 word =
      word_xor (word_subword xl (64,64)) (word_subword mid (0,64)) /\
    word_subword xm' (64,64) : 64 word =
      word_xor (word_subword xh (0,64)) (word_subword mid (64,64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC WORD_BLAST);;

(* --- Helper: spec's reduction = Prop3's reduction (on 4 x 64-bit limbs) --- *)

let REDUCTION_EQUIV = prove(
  `!(a:64 word) (b:64 word) (c:64 word) (d:64 word).
    let wa:int128 = word_xor
      (word_xor (word_shl (word_zx a : int128) 63)
                (word_shl (word_zx a : int128) 62))
      (word_shl (word_zx a : int128) 57) in
    let phase1:int128 = word_xor wa (word_join a b : int128) in
    let t3:int128 = word_subword (word_join phase1 phase1 : 256 word) (64,128) in
    let red2:int128 = word_xor
      (word_xor (word_shl (word_zx (word_subword phase1 (0,64) : 64 word) : int128) 63)
                (word_shl (word_zx (word_subword phase1 (0,64) : 64 word) : int128) 62))
      (word_shl (word_zx (word_subword phase1 (0,64) : 64 word) : int128) 57) in
    word_xor (word_xor (word_join d c : int128) t3) red2 =
    (let v:64 word = word_xor b (word_subword wa (0,64)) in
     let u:64 word = word_xor (word_xor c a) (word_subword wa (64,64)) in
     let wv:int128 = word_xor
       (word_xor (word_shl (word_zx v : int128) 63)
                 (word_shl (word_zx v : int128) 62))
       (word_shl (word_zx v : int128) 57) in
     word_join (word_xor (word_xor d v) (word_subword wv (64,64)))
              (word_xor u (word_subword wv (0,64))) : int128)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC WORD_BLAST);;

(* --- Main theorem: gcm_gmult_spec = polyval_dot via byteswap128 --- *)

let GCM_GMULT_POLYVAL_DOT = prove(
  `!xi h:int128.
    let H = byteswap128 h in
    gcm_gmult_spec xi h (word_zx(karatsuba_mid H) : int128) =
    word_reversefields 8 (polyval_dot (word_reversefields 8 xi) H)`,
  X_GEN_TAC `xi:int128` THEN X_GEN_TAC `h:int128` THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; gcm_gmult_spec; polyval_dot;
              polyval_reduce_prop3; byteswap128; karatsuba_mid;
              REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[KARATSUBA_LIMBS] THEN
  REWRITE_TAC[PMUL_W_64_128] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> word_reversefields 8 x = word_reversefields 8 y`) THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] SPEC_XM_PRIME_AS_ABCD] THEN
  ABBREV_TAC `xl:int128 = word_pmul (word_subword (h:int128) (64,64) : 64 word)
    (word_subword (word_reversefields 8 (xi:int128)) (0,64) : 64 word)` THEN
  ABBREV_TAC `xh:int128 = word_pmul (word_subword (h:int128) (0,64) : 64 word)
    (word_subword (word_reversefields 8 (xi:int128)) (64,64) : 64 word)` THEN
  ABBREV_TAC `xm:int128 = word_pmul
    (word_xor (word_subword (h:int128) (64,64) : 64 word) (word_subword h (0,64) : 64 word))
    (word_xor (word_subword (word_reversefields 8 (xi:int128)) (0,64) : 64 word)
              (word_subword (word_reversefields 8 xi) (64,64) : 64 word))` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_PMUL_SYM]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] SPEC_XM_PRIME_AS_ABCD] THEN
  ONCE_REWRITE_TAC[WORD_PMUL_SYM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] SPEC_XM_PRIME_AS_ABCD] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] REDUCTION_EQUIV] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV));;

(* ========================================================================= *)
(* V_STEP_CONG: V-step preserves congruence mod P(x)                        *)
(*                                                                           *)
(* The V-update in poly_mul_loop (shift + conditional XOR with 0x87) is      *)
(* congruent to multiplication by the polynomial variable u mod P(x).        *)
(* This is the core inductive step for connecting the NIST loop to           *)
(* polynomial multiplication.                                                *)
(* ========================================================================= *)

(* ---- Helper lemmas for V_STEP_CONG ---- *)

(* poly_var bool_ring one is in ring_carrier bool_poly *)
let POLY_VAR_IN_BOOL_POLY = prove(
  `poly_var bool_ring one IN ring_carrier bool_poly`,
  REWRITE_TAC[bool_poly; POLY_VAR; IN_UNIV]);;

(* u * poly_of_word is in the carrier *)
let RING_MUL_POLY_VAR = prove(
  `!v:N word. ring_mul bool_poly (poly_var bool_ring one) (poly_of_word v)
              IN ring_carrier bool_poly`,
  GEN_TAC THEN MATCH_MP_TAC RING_MUL THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VAR_IN_BOOL_POLY]);;

(* word_clz v >= 1 when bit 127 v is false (for int128) *)
let WORD_CLZ_GE_1 = prove(
  `!v:int128. ~bit 127 v ==> 1 <= word_clz v`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  REWRITE_TAC[WORD_CLZ_EQ_0; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Degree bound: poly_deg(u * poly_of_word v) < 128 when ~bit 127 v *)
let POLY_DEG_MUL_V_U_BOUND = prove(
  `!v:int128. ~bit 127 v ==>
    poly_deg bool_ring
      (ring_mul bool_poly (poly_of_word v) (poly_var bool_ring one)) < 128`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[BOOL_POLY_MUL] THEN
  MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `poly_deg bool_ring (poly_of_word (v:int128)) +
              poly_deg bool_ring (poly_var bool_ring one:(1->num)->bool)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC POLY_DEG_MUL_LE THEN
    REWRITE_TAC[RING_POLYNOMIAL_OF_WORD; RING_POLYNOMIAL_VAR];
    REWRITE_TAC[POLY_DEG_POLY_OF_WORD; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[POLY_DEG_VAR] THEN
    SUBGOAL_THEN `~(ring_1 bool_ring <=> ring_0 bool_ring)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM bool_ring; BOOL_RING]; ALL_TAC] THEN
    MP_TAC(ISPEC `v:int128` WORD_CLZ_GE_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* word_shl v 1 = word_of_poly(poly_of_word v * u) at any word size *)
let WORD_SHL_1_AS_OF_POLY = prove(
  `!v:int128. word_shl v 1 =
    word_of_poly(ring_mul bool_poly (poly_of_word v) (poly_var bool_ring one)) : int128`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM POLY_OF_WORD_2; GSYM WORD_PMUL_POLY] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 WORD_PMUL_POW2)] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* FALSE case: when ~bit 127 v, poly_of_word(shl v 1) = u * poly_of_word(v) *)
let SHL_1_POLY_FALSE = prove(
  `!v:int128. ~bit 127 v ==>
    poly_of_word(word_shl v 1) =
    ring_mul bool_poly (poly_var bool_ring one) (poly_of_word v)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_SHL_1_AS_OF_POLY] THEN
  SUBGOAL_THEN
    `(poly_of_word:int128->(1->num)->bool)
     (word_of_poly(ring_mul bool_poly (poly_of_word (v:int128)) (poly_var bool_ring one))) =
     ring_mul bool_poly (poly_of_word v) (poly_var bool_ring one)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:128`,`:N`] POLY_OF_WORD_OF_POLY) THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_MUL THEN
      REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VAR_IN_BOOL_POLY];
      REWRITE_TAC[DIMINDEX_128] THEN ASM_SIMP_TAC[POLY_DEG_MUL_V_U_BOUND]];
    MP_TAC(ISPECL [`bool_poly`; `poly_of_word (v:int128)`;
                    `poly_var bool_ring one:(1->num)->bool`] RING_MUL_SYM) THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VAR_IN_BOOL_POLY] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* ODD(1 DIV 2^n) iff n = 0 *)
let ODD_1_DIV_2EXP = prove(
  `!n. ODD(1 DIV 2 EXP n) <=> (n = 0)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 DIV 2 EXP n = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN
      TRANS_TAC LTE_TRANS `2 EXP 1` THEN CONJ_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV;
        REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
      REWRITE_TAC[ODD]]]);;

(* 256-bit XOR overflow identity:
   word_zx(word_shl v 1 : int128) XOR word_shl(word_zx v : 256) 1
   = word with just bit 128 set when bit 127 v, else 0 *)
let WORD_ZX_SHL_XOR_OVERFLOW = prove(
  `!v:int128.
    word_xor (word_zx(word_shl v 1 : int128) : 256 word)
             (word_shl (word_zx v : 256 word) 1) =
    (if bit 127 v then word_shl (word 1 : 256 word) 128 else word 0 : 256 word)`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_256] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_XOR; BIT_WORD_ZX; BIT_WORD_SHL; BIT_WORD;
              BIT_WORD_0; DIMINDEX_128; DIMINDEX_256] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < 128` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `i - 1 < 256` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[BIT_WORD_SHL; BIT_WORD; BIT_WORD_0; DIMINDEX_256; ODD_1_DIV_2EXP] THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN `1 <= i /\ i - 1 < 256 /\ ~(i - 1 < 128)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `i = 128` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[BIT_WORD_SHL; BIT_WORD; BIT_WORD_0; DIMINDEX_256; ODD_1_DIV_2EXP] THEN
      CONV_TAC NUM_REDUCE_CONV;
      SUBGOAL_THEN `128 <= i - 1` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[BIT_TRIVIAL; DIMINDEX_128] THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[BIT_WORD_SHL; BIT_WORD; BIT_WORD_0; DIMINDEX_256; ODD_1_DIV_2EXP] THEN
      ASM_ARITH_TAC]]);;

(* poly_of_word(word_shl (word 1 : 256) 128) = x^128 *)
let POLY_OF_WORD_X128 = prove(
  `poly_of_word(word_shl (word 1 : 256 word) 128 : 256 word) =
   ring_pow bool_poly (poly_var bool_ring one) 128`,
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(SPEC `128` (INST_TYPE [`:256`, `:N`] POLY_VAR_POW_OF_WORD)) THEN
  REWRITE_TAC[DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* poly_of_word at 128 and 256 bits agree for zero-extended words *)
let POLY_OF_WORD_ZX_128_256 = prove(
  `!w:int128. poly_of_word(word_zx w : 256 word) = poly_of_word w`,
  GEN_TAC THEN
  MP_TAC(SPEC `w:int128` (INST_TYPE [`:128`,`:M`; `:256`,`:N`] POLY_OF_WORD_ZX)) THEN
  REWRITE_TAC[DIMINDEX_128; DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV);;

(* poly_of_word(word 2 : 256 word) = u *)
let POLY_OF_WORD_2_256 = prove(
  `poly_of_word(word 2 : 256 word) = poly_var bool_ring one`,
  MP_TAC(SPEC `1` (INST_TYPE [`:256`, `:N`] POLY_VAR_POW_OF_WORD)) THEN
  REWRITE_TAC[DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(SUBST1_TAC o GSYM) THEN
  SIMP_TAC[RING_POW_1; POLY_VAR_IN_BOOL_POLY]);;

(* poly_of_word(word_shl(word_zx v : 256) 1) = u * poly_of_word(v) *)
let POLY_OF_SHL_ZX = prove(
  `!v:int128. poly_of_word(word_shl (word_zx v : 256 word) 1 : 256 word) =
              ring_mul bool_poly (poly_var bool_ring one) (poly_of_word v)`,
  GEN_TAC THEN
  SUBGOAL_THEN `word_shl (word_zx (v:int128) : 256 word) 1 =
    (word_of_poly(ring_mul bool_poly (poly_of_word(word_zx v : 256 word))
                                     (poly_of_word(word 2 : 256 word))) : 256 word)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_PMUL_POLY; GSYM(CONJUNCT2 WORD_PMUL_POW2)] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(poly_of_word:256 word->(1->num)->bool)
    (word_of_poly(ring_mul bool_poly (poly_of_word(word_zx (v:int128) : 256 word))
                                     (poly_of_word(word 2 : 256 word)))) =
    ring_mul bool_poly (poly_of_word(word_zx v : 256 word)) (poly_of_word(word 2 : 256 word))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:256`,`:N`] POLY_OF_WORD_OF_POLY) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_MUL THEN REWRITE_TAC[BOOL_POLY_OF_WORD];
      REWRITE_TAC[DIMINDEX_256; BOOL_POLY_MUL; POLY_OF_WORD_ZX_128_256] THEN
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `poly_deg bool_ring (poly_of_word(v:int128)) +
                  poly_deg bool_ring (poly_of_word(word 2:256 word))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC POLY_DEG_MUL_LE THEN REWRITE_TAC[RING_POLYNOMIAL_OF_WORD];
        REWRITE_TAC[POLY_DEG_POLY_OF_WORD; DIMINDEX_128; DIMINDEX_256] THEN
        CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
        ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[POLY_OF_WORD_ZX_128_256; POLY_OF_WORD_2_256] THEN
  MP_TAC(ISPECL [`bool_poly`; `poly_of_word(v:int128)`;
                  `poly_var bool_ring one:(1->num)->bool`] RING_MUL_SYM) THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VAR_IN_BOOL_POLY] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ghash_poly = x^128 + poly_of_word(word 0x87 : 256 word) *)
let GHASH_POLY_AS_SUM = prove(
  `ghash_poly = ring_add bool_poly
    (ring_pow bool_poly (poly_var bool_ring one) 128)
    (poly_of_word(word 0x87 : 256 word))`,
  MP_TAC(INST_TYPE [`:256`, `:N`] GHASH_POLY_OF_WORD) THEN
  REWRITE_TAC[DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(word 340282366920938463463374607431768211591 : 256 word) =
    word_xor (word_shl (word 1 : 256 word) 128) (word 0x87 : 256 word)` SUBST1_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[POLY_OF_WORD_XOR; POLY_OF_WORD_X128]);;

(* ring_add(ring_add A B) C = ring_add(ring_add A C) B *)
let RING_ADD_ACB = prove(
  `!r (A:A) B C. A IN ring_carrier r /\ B IN ring_carrier r /\ C IN ring_carrier r ==>
    ring_add r (ring_add r A B) C = ring_add r (ring_add r A C) B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `A:A`; `B:A`; `C:A`] RING_ADD_ASSOC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o GSYM) THEN
  MP_TAC(ISPECL [`r:A ring`; `B:A`; `C:A`] RING_ADD_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `A:A`; `C:A`; `B:A`] RING_ADD_ASSOC) THEN
  ASM_REWRITE_TAC[]);;

(* ---- V_STEP_CONG: the V-step is congruent to multiplication by u ---- *)

(* The V-step of the polynomial loop:
     if bit 127 v then word_xor (word_shl v 1) (word 0x87) else word_shl v 1
   satisfies: poly_of_word(V_step(v)) ≡ u * poly_of_word(v) (mod P(x)).

   Proof strategy:
   - FALSE case (~bit 127 v): word_shl v 1 = word_of_poly(u * poly_of_word v)
     and the degree < 128, so the round-trip preserves the polynomial.
   - TRUE case (bit 127 v): work at 256 bits via WORD_ZX_SHL_XOR_OVERFLOW.
     The overflow bit gives x^128, and x^128 + poly(0x87) = ghash_poly. *)
let V_STEP_CONG = prove(
  `!v:int128.
    (poly_of_word
      (if bit 127 v then word_xor (word_shl v 1) (word 0x87)
       else word_shl v 1) ==
     ring_mul bool_poly (poly_var bool_ring one) (poly_of_word v))
    (mod_ghash)`,
  GEN_TAC THEN ASM_CASES_TAC `bit 127 (v:int128)` THEN ASM_REWRITE_TAC[] THENL
   [(* TRUE case: quotient witness = ring_1 *)
    REWRITE_TAC[cong; mod_ghash; BOOL_POLY_OF_WORD] THEN
    SIMP_TAC[IDEAL_GENERATED_SING; GHASH_BOOL_POLY; IN_ELIM_THM] THEN
    REWRITE_TAC[ring_divides; GHASH_BOOL_POLY] THEN
    SIMP_TAC[RING_SUB; BOOL_POLY_OF_WORD; RING_MUL_POLY_VAR] THEN
    EXISTS_TAC `ring_1 bool_poly` THEN
    CONJ_TAC THENL [REWRITE_TAC[RING_1; GHASH_BOOL_POLY]; ALL_TAC] THEN
    REWRITE_TAC[BOOL_POLY_SUB] THEN
    SIMP_TAC[RING_MUL_RID; GHASH_BOOL_POLY] THEN
    REWRITE_TAC[POLY_OF_WORD_XOR] THEN
    (* Derive truncation identity: poly(shl v 1) + u*poly(v) = x^128 *)
    MP_TAC(ISPEC `v:int128` WORD_ZX_SHL_XOR_OVERFLOW) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `poly_of_word:(256 word)->(1->num)->bool`) THEN
    REWRITE_TAC[POLY_OF_WORD_XOR; POLY_OF_WORD_X128;
                POLY_OF_WORD_ZX_128_256; POLY_OF_SHL_ZX] THEN
    DISCH_TAC THEN
    (* Convert poly(word 135:int128) to 256-bit type for GHASH_POLY_AS_SUM *)
    SUBGOAL_THEN `poly_of_word(word 135:int128) = poly_of_word(word 135:256 word)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MP_TAC(SPEC `word 135:int128` (INST_TYPE [`:128`,`:M`; `:256`,`:N`] POLY_OF_WORD_ZX)) THEN
      REWRITE_TAC[DIMINDEX_128; DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(SUBST1_TAC o GSYM) THEN AP_TERM_TAC THEN CONV_TAC WORD_REDUCE_CONV;
      ALL_TAC] THEN
    (* Unfold ghash_poly = x^128 + poly(word 135:256) *)
    GEN_REWRITE_TAC (RAND_CONV) [GHASH_POLY_AS_SUM] THEN
    (* Ring AC: (A+B)+C = (A+C)+B *)
    MP_TAC(ISPECL [`bool_poly`;
      `poly_of_word(word_shl (v:int128) 1)`;
      `poly_of_word(word 135 : 256 word)`;
      `ring_mul bool_poly (poly_var bool_ring one) (poly_of_word (v:int128))`] RING_ADD_ACB) THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD; RING_MUL_POLY_VAR] THEN
    DISCH_THEN SUBST1_TAC THEN
    (* Now: (A+C)+B = x^128+B, use A+C = x^128 *)
    AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM ACCEPT_TAC;
    (* FALSE case: poly(shl v 1) = u*poly(v), congruence is reflexive *)
    ASM_SIMP_TAC[SHL_1_POLY_FALSE; MOD_GHASH_REFL; RING_MUL_POLY_VAR]]);;

(* ========================================================================= *)
(* Bridge A completion: NIST loop = polynomial multiplication mod P(x)       *)
(*                                                                           *)
(* poly_mul_loop 0 y x 128 = ghash_reduce(word_pmul x y)                    *)
(* brp(nist_ghash_mul x y) = ghash_reduce(word_pmul (brp x) (brp y))        *)
(* ========================================================================= *)

(* ---- Partial polynomial: Horner evaluation of x's bits ---- *)

(* partial_poly x n = the polynomial formed by processing n bits of x
   using the Horner scheme. After 128 steps, this equals poly_of_word(x). *)
let partial_poly = define
  `partial_poly (x:int128) 0 = ring_0 bool_poly /\
   partial_poly x (SUC n) =
     ring_add bool_poly
       (if bit (128 - SUC n) x then ring_1 bool_poly else ring_0 bool_poly)
       (ring_mul bool_poly (poly_var bool_ring one) (partial_poly x n))`;;

let PARTIAL_POLY_IN_CARRIER = prove(
  `!x:int128. !n. partial_poly x n IN ring_carrier bool_poly`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[partial_poly; RING_0; GHASH_BOOL_POLY];
    REWRITE_TAC[partial_poly] THEN
    MATCH_MP_TAC RING_ADD THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[RING_1; RING_0; GHASH_BOOL_POLY];
      MATCH_MP_TAC RING_MUL THEN
      ASM_REWRITE_TAC[POLY_VAR_IN_BOOL_POLY]]]);;

(* ---- Horner evaluation: partial_poly x 128 = poly_of_word x ---- *)

(* word_horner: the word-level version of partial_poly *)
let word_horner = define
  `word_horner (x:int128) 0 = (word 0 : int128) /\
   word_horner x (SUC n) =
     word_xor (if bit (128 - SUC n) x then word 1 else word 0 : int128)
              (word_shl (word_horner x n) 1)`;;

(* Bit-level characterization of word_horner *)
let WORD_HORNER_BIT = prove(
  `!x:int128 n. n <= 128 ==>
    (!k. k < 128 ==> (bit k (word_horner x n) <=> k < n /\ bit (128 - n + k) x))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[word_horner; BIT_WORD_0; LT];
    DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `n <= 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[word_horner; BIT_WORD_XOR; BIT_WORD_SHL; DIMINDEX_128] THEN
    ASM_CASES_TAC `bit (128 - SUC n) (x:int128)` THEN ASM_REWRITE_TAC[BIT_WORD; BIT_WORD_0; ODD_1_DIV_2EXP] THENL
     [ASM_CASES_TAC `k = 0` THENL
       [ASM_REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `128 - SUC n + 0 = 128 - SUC n` SUBST1_TAC THENL
         [ARITH_TAC; ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `1 <= k /\ k - 1 < 128` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[DIMINDEX_128] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k - 1`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `128 - n + (k - 1) = 128 - SUC n + k` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(k - 1 < n <=> k < SUC n)` SUBST1_TAC THENL
         [ASM_ARITH_TAC; REFL_TAC]];
      ASM_CASES_TAC `k = 0` THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `128 - SUC n + 0 = 128 - SUC n` SUBST1_TAC THENL
         [ARITH_TAC; ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `1 <= k /\ k - 1 < 128` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k - 1`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `128 - n + (k - 1) = 128 - SUC n + k` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(k - 1 < n <=> k < SUC n)` SUBST1_TAC THENL
         [ASM_ARITH_TAC; REFL_TAC]]]]);;

(* word_horner x 128 = x *)
let WORD_HORNER_128 = prove(
  `!x:int128. word_horner x 128 = x`,
  GEN_TAC THEN ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN REWRITE_TAC[DIMINDEX_128] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:int128`; `128`] WORD_HORNER_BIT) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[ADD_CLAUSES]);;

(* bit 127 of word_horner x n is F for n <= 127 (no overflow during Horner build) *)
let WORD_HORNER_BIT127_F = prove(
  `!x:int128. !n. n <= 127 ==> ~bit 127 (word_horner x n)`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:int128`; `n:num`] WORD_HORNER_BIT) THEN
  SUBGOAL_THEN `n <= 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `127`) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC);;

(* partial_poly x n = poly_of_word(word_horner x n) for n <= 128 *)
let PARTIAL_POLY_AS_WORD_HORNER = prove(
  `!x:int128. !n. n <= 128 ==> partial_poly x n = poly_of_word(word_horner x n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[partial_poly; word_horner; POLY_OF_WORD_0];
    DISCH_TAC THEN
    SUBGOAL_THEN `n <= 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REWRITE_TAC[partial_poly; word_horner] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLY_OF_WORD_XOR] THEN
    SUBGOAL_THEN `poly_of_word(if bit (128 - SUC n) (x:int128) then word 1 else word 0 : int128) =
                  (if bit (128 - SUC n) x then ring_1 bool_poly else ring_0 bool_poly)`
      SUBST1_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[POLY_OF_WORD_1; POLY_OF_WORD_0]; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SHL_1_POLY_FALSE THEN
    MATCH_MP_TAC WORD_HORNER_BIT127_F THEN ASM_ARITH_TAC]);;

(* PARTIAL_POLY_128: the Horner evaluation of x's bits equals poly_of_word(x) *)
let PARTIAL_POLY_128 = prove(
  `!x:int128. partial_poly x 128 = poly_of_word x`,
  GEN_TAC THEN
  MP_TAC(SPECL [`x:int128`; `128`] PARTIAL_POLY_AS_WORD_HORNER) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_HORNER_128]);;

(* ---- Loop invariant: inductive congruence ---- *)

(* ---- Ring algebra helpers for the loop inductive step ---- *)

(* (1 + u*pp) * pv = pv + (u*pp)*pv [right distributivity + identity] *)
let DISTRIB_LEMMA = prove(
  `!pp pv:(1->num)->bool. pp IN ring_carrier bool_poly /\ pv IN ring_carrier bool_poly ==>
    ring_mul bool_poly
      (ring_add bool_poly (ring_1 bool_poly) (ring_mul bool_poly (poly_var bool_ring one) pp))
      pv =
    ring_add bool_poly pv (ring_mul bool_poly (ring_mul bool_poly (poly_var bool_ring one) pp) pv)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`bool_poly`; `ring_1 bool_poly:(1->num)->bool`;
    `ring_mul bool_poly (poly_var bool_ring one) (pp:(1->num)->bool)`;
    `pv:(1->num)->bool`] RING_ADD_RDISTRIB) THEN
  ASM_SIMP_TAC[RING_1; RING_MUL; GHASH_BOOL_POLY; POLY_VAR_IN_BOOL_POLY] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[RING_MUL_LID; GHASH_BOOL_POLY]);;

(* (u*pp)*pv = pp*(u*pv) [associativity + commutativity] *)
let ASSOC_COMM_LEMMA = prove(
  `!pp pv:(1->num)->bool. pp IN ring_carrier bool_poly /\ pv IN ring_carrier bool_poly ==>
    ring_mul bool_poly (ring_mul bool_poly (poly_var bool_ring one) pp) pv =
    ring_mul bool_poly pp (ring_mul bool_poly (poly_var bool_ring one) pv)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_mul bool_poly (poly_var bool_ring one) (pp:(1->num)->bool) =
                ring_mul bool_poly pp (poly_var bool_ring one)` SUBST1_TAC THENL
   [MATCH_MP_TAC(ISPEC `bool_poly` RING_MUL_SYM) THEN
    ASM_REWRITE_TAC[POLY_VAR_IN_BOOL_POLY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`bool_poly`; `pp:(1->num)->bool`;
    `poly_var bool_ring one:(1->num)->bool`; `pv:(1->num)->bool`] RING_MUL_ASSOC) THEN
  ASM_SIMP_TAC[POLY_VAR_IN_BOOL_POLY] THEN MESON_TAC[]);;

(* a + (b + c) = (a + b) + c *)
let ADD_ASSOC_LEMMA = prove(
  `!a b c:(1->num)->bool. a IN ring_carrier bool_poly /\ b IN ring_carrier bool_poly /\
    c IN ring_carrier bool_poly ==>
    ring_add bool_poly a (ring_add bool_poly b c) =
    ring_add bool_poly (ring_add bool_poly a b) c`,
  MESON_TAC[RING_ADD_ASSOC]);;

(* The key congruence step: the IH's RHS ≡ the target RHS *)
let LOOP_STEP_CONG = prove(
  `!n (z:int128) (v:int128) (x:int128) (pp:(1->num)->bool).
    pp IN ring_carrier bool_poly ==>
    (ring_add bool_poly
      (poly_of_word (if bit (128 - SUC n) x then word_xor z v else z))
      (ring_mul bool_poly pp
        (poly_of_word (if bit 127 v then word_xor (word_shl v 1) (word 135) else word_shl v 1))) ==
     ring_add bool_poly (poly_of_word z)
       (ring_mul bool_poly
         (ring_add bool_poly
           (if bit (128 - SUC n) x then ring_1 bool_poly else ring_0 bool_poly)
           (ring_mul bool_poly (poly_var bool_ring one) pp))
         (poly_of_word v)))
    (mod_ghash)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `bit (128 - SUC n) (x:int128)` THEN ASM_REWRITE_TAC[] THENL
   [(* TRUE case *)
    REWRITE_TAC[POLY_OF_WORD_XOR] THEN
    ASM_SIMP_TAC[DISTRIB_LEMMA; BOOL_POLY_OF_WORD] THEN
    ASM_SIMP_TAC[ASSOC_COMM_LEMMA; BOOL_POLY_OF_WORD] THEN
    SUBGOAL_THEN `ring_add bool_poly (poly_of_word (z:int128))
      (ring_add bool_poly (poly_of_word (v:int128))
        (ring_mul bool_poly pp (ring_mul bool_poly (poly_var bool_ring one) (poly_of_word v)))) =
    ring_add bool_poly (ring_add bool_poly (poly_of_word z) (poly_of_word v))
      (ring_mul bool_poly pp (ring_mul bool_poly (poly_var bool_ring one) (poly_of_word v)))`
      SUBST1_TAC THENL
     [MATCH_MP_TAC ADD_ASSOC_LEMMA THEN
      ASM_SIMP_TAC[BOOL_POLY_OF_WORD; RING_MUL; POLY_VAR_IN_BOOL_POLY]; ALL_TAC] THEN
    MATCH_MP_TAC MOD_GHASH_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[MOD_GHASH_REFL] THEN MATCH_MP_TAC RING_ADD THEN
      REWRITE_TAC[BOOL_POLY_OF_WORD]; ALL_TAC] THEN
    MATCH_MP_TAC MOD_GHASH_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[MOD_GHASH_REFL] THEN ASM_REWRITE_TAC[];
      MATCH_ACCEPT_TAC V_STEP_CONG];
    (* FALSE case *)
    ASM_SIMP_TAC[RING_ADD_LZERO; GHASH_BOOL_POLY; RING_MUL; POLY_VAR_IN_BOOL_POLY;
                  BOOL_POLY_OF_WORD] THEN
    ASM_SIMP_TAC[ASSOC_COMM_LEMMA; BOOL_POLY_OF_WORD] THEN
    MATCH_MP_TAC MOD_GHASH_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[MOD_GHASH_REFL; BOOL_POLY_OF_WORD]; ALL_TAC] THEN
    MATCH_MP_TAC MOD_GHASH_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[MOD_GHASH_REFL] THEN ASM_REWRITE_TAC[];
      MATCH_ACCEPT_TAC V_STEP_CONG]]);;

(* ---- Loop invariant (fully proved) ---- *)

let LOOP_INVARIANT = prove(
  `!n (z:int128) (v:int128) (x:int128). n <= 128 ==>
    (poly_of_word(poly_mul_loop z v x n) ==
     ring_add bool_poly (poly_of_word z)
       (ring_mul bool_poly (partial_poly x n) (poly_of_word v)))
    (mod_ghash)`,
  INDUCT_TAC THENL
   [(* Base case *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[poly_mul_loop; partial_poly] THEN
    SIMP_TAC[RING_MUL_LZERO; GHASH_BOOL_POLY; BOOL_POLY_OF_WORD] THEN
    SIMP_TAC[RING_ADD_RZERO; GHASH_BOOL_POLY; BOOL_POLY_OF_WORD] THEN
    REWRITE_TAC[MOD_GHASH_REFL; BOOL_POLY_OF_WORD];
    (* Inductive step: use IH + LOOP_STEP_CONG + MOD_GHASH_TRANS *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[poly_mul_loop; partial_poly; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    SUBGOAL_THEN `n <= 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [
      `(if bit (128 - SUC n) (x:int128) then word_xor z v else z) : int128`;
      `(if bit 127 (v:int128) then word_xor (word_shl v 1) (word 135) else word_shl v 1) : int128`;
      `x:int128`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `z:int128`; `v:int128`; `x:int128`; `partial_poly (x:int128) n`]
      LOOP_STEP_CONG) THEN
    REWRITE_TAC[PARTIAL_POLY_IN_CARRIER] THEN DISCH_TAC THEN
    ASM_MESON_TAC[MOD_GHASH_TRANS]]);;

(* ---- Main loop congruence ---- *)

(* poly_mul_loop computes poly(x) * poly(y) mod ghash_poly *)
let POLY_MUL_LOOP_CONG = prove(
  `!x y:int128.
    (poly_of_word(poly_mul_loop (word 0) y x 128) ==
     ring_mul bool_poly (poly_of_word x) (poly_of_word y))
    (mod_ghash)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`128`; `word 0:int128`; `y:int128`; `x:int128`] LOOP_INVARIANT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[PARTIAL_POLY_128; POLY_OF_WORD_0] THEN
  SIMP_TAC[RING_ADD_LZERO; GHASH_BOOL_POLY; RING_MUL; BOOL_POLY_OF_WORD]);;

(* ---- poly_mul_loop = ghash_reduce(word_pmul) ---- *)

(* Both sides are congruent to poly(x)*poly(y) mod P, and both are 128-bit words,
   so they are equal by MOD_GHASH_WORD_EQ. *)
let POLY_MUL_LOOP_CORRECT = prove(
  `!x y:int128. poly_mul_loop (word 0) y x 128 =
                ghash_reduce(word_pmul x y : 256 word)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MOD_GHASH_WORD_EQ THEN
  MP_TAC(SPECL [`x:int128`; `y:int128`] POLY_MUL_LOOP_CONG) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
    `(ring_mul bool_poly (poly_of_word (x:int128)) (poly_of_word (y:int128)) ==
      poly_of_word(ghash_reduce(word_pmul x y : 256 word))) (mod_ghash)`
    MP_TAC THENL
   [MP_TAC(ISPEC `word_pmul (x:int128) (y:int128) : 256 word` POLY_EQUIV_GHASH_REDUCE) THEN
    REWRITE_TAC[POLY_OF_WORD_PMUL_2N];
    FIRST_X_ASSUM(fun h0 -> DISCH_THEN(fun h1 ->
      ACCEPT_TAC(MATCH_MP MOD_GHASH_TRANS (CONJ h0 h1))))]);;

(* ========================================================================= *)
(* BRIDGE A: NIST Algorithm 1 = ghash_reduce(word_pmul(brp x, brp y))        *)
(*                                                                           *)
(* This is the top-level Bridge A theorem connecting the NIST specification  *)
(* to polynomial multiplication mod P(x) in the natural bit order.           *)
(* ========================================================================= *)

(* brp(nist_ghash_mul x y) = poly_mul_loop 0 (brp y) (brp x) 128.
   Proved by induction using V_STEP_BRP, Z_STEP_BRP, and LOOP_BRP. *)
let NIST_GHASH_MUL_AS_POLY_LOOP_2 = prove(
  `!x y:int128.
    bit_reverse_per_byte(nist_ghash_mul x y) =
    poly_mul_loop (word 0) (bit_reverse_per_byte y) (bit_reverse_per_byte x) 128`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nist_ghash_mul; LOOP_BRP; BRP_ZERO]);;

(* BRIDGE A: The main theorem.
   Combines NIST_GHASH_MUL_AS_POLY_LOOP_2 with POLY_MUL_LOOP_CORRECT. *)
let BRIDGE_A = prove(
  `!x y:int128.
    bit_reverse_per_byte(nist_ghash_mul x y) =
    ghash_reduce(word_pmul (bit_reverse_per_byte x) (bit_reverse_per_byte y) : 256 word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[NIST_GHASH_MUL_AS_POLY_LOOP_2; POLY_MUL_LOOP_CORRECT]);;
