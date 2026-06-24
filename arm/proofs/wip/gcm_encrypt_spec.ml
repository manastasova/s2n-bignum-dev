(* ========================================================================= *)
(* Recursive AES-256-GCM encrypt specification over a plaintext byte list,    *)
(* mirroring the AES-XTS spec (arm/proofs/xts_reference/aes_xts_encrypt_spec   *)
(* + aes-xts-armv8.ml).  Reuses XTS's mode-agnostic byte/word conversions and  *)
(* byte_list_at memory predicate, and the existing GCM per-block primitives    *)
(* (aes256_block_enc, gcm_ctr_inc, ghash_polyval_acc).                         *)
(* ========================================================================= *)

(* --- byte<->word conversions + memory predicate (verbatim from XTS) --- *)
let bytes_to_int128 = define
  `bytes_to_int128 (bs : byte list) : int128 =
    word_join
      (word_join
        (word_join (word_join (EL 15 bs) (EL 14 bs) : int16) (word_join (EL 13 bs) (EL 12 bs) : int16) : int32)
        (word_join (word_join (EL 11 bs) (EL 10 bs) : int16) (word_join (EL 9 bs) (EL 8 bs) : int16) : int32) : int64)
      (word_join
        (word_join (word_join (EL 7 bs) (EL 6 bs) : int16) (word_join (EL 5 bs) (EL 4 bs) : int16) : int32)
        (word_join (word_join (EL 3 bs) (EL 2 bs) : int16) (word_join (EL 1 bs) (EL 0 bs) : int16) : int32) : int64)`;;

let int128_to_bytes = define
  `int128_to_bytes (w : int128) : byte list =
     [word_subword w (0, 8); word_subword w (8, 8); word_subword w (16, 8); word_subword w (24, 8);
      word_subword w (32, 8); word_subword w (40, 8); word_subword w (48, 8); word_subword w (56, 8);
      word_subword w (64, 8); word_subword w (72, 8); word_subword w (80, 8); word_subword w (88, 8);
      word_subword w (96, 8); word_subword w (104, 8); word_subword w (112, 8); word_subword w (120, 8)]`;;

let byte_list_at = define
  `byte_list_at (m : byte list) (m_p : int64) (len:int64) s =
    ! i. i < val len ==> read (memory :> bytes8(word_add m_p (word i))) s = EL i m`;;

(* --- GCM keystream: AES-CTR of (gcm_ctr_inc^i ivec) --- *)
let gcm_ctr_iter = new_recursive_definition num_RECURSION
  `gcm_ctr_iter 0 (ivec:(128)word) = ivec /\
   gcm_ctr_iter (SUC n) (ivec:(128)word) = gcm_ctr_inc (gcm_ctr_iter n ivec)`;;

let gcm_keystream = new_definition
  `gcm_keystream (i:num) (ivec:(128)word) (rks:int128 list) : (128)word =
     aes256_block_enc (gcm_ctr_iter i ivec)
       (EL 0 rks) (EL 1 rks) (EL 2 rks) (EL 3 rks) (EL 4 rks) (EL 5 rks) (EL 6 rks) (EL 7 rks)
       (EL 8 rks) (EL 9 rks) (EL 10 rks) (EL 11 rks) (EL 12 rks) (EL 13 rks) (EL 14 rks)`;;

(* --- recursive full-block ciphertext (int128 blocks) --- *)
let gcm_ct_rec = new_specification ["gcm_ct_rec"]
  (prove_general_recursive_function_exists
    `?gcm_ct_rec.
       ! (i:num) (nfull:num) (P:byte list) (ivec:(128)word) (rks:int128 list).
         gcm_ct_rec i nfull P ivec rks : (int128 list) =
           if nfull = 0 then []
           else
             let blk = bytes_to_int128 (SUB_LIST (i * 16, 16) P) in
             let ct = word_xor blk (gcm_keystream i ivec rks) in
             CONS ct (gcm_ct_rec (i + 1) (nfull - 1) P ivec rks)`);;

(* --- recursive full-block ciphertext (flat byte list) --- *)
let gcm_ct_bytes_rec = new_specification ["gcm_ct_bytes_rec"]
  (prove_general_recursive_function_exists
    `?gcm_ct_bytes_rec.
       ! (i:num) (nfull:num) (P:byte list) (ivec:(128)word) (rks:int128 list).
         gcm_ct_bytes_rec i nfull P ivec rks : (byte list) =
           if nfull = 0 then []
           else
             let blk = bytes_to_int128 (SUB_LIST (i * 16, 16) P) in
             let ct = word_xor blk (gcm_keystream i ivec rks) in
             APPEND (int128_to_bytes ct) (gcm_ct_bytes_rec (i + 1) (nfull - 1) P ivec rks)`);;

(* --- masked partial-tail ciphertext block: read the full 16-byte block then  *)
(* mask to `tail` bytes (the binary reads a full block and masks).            *)
let gcm_ctm_tail = new_definition
  `gcm_ctm_tail (i:num) (tail:num) (P:byte list) (ivec:(128)word) (rks:int128 list) : (128)word =
     let blk = bytes_to_int128 (SUB_LIST (i * 16, 16) P) in
     let ct = word_xor blk (gcm_keystream i ivec rks) in
     word_and ct (word (2 EXP (8 * tail) - 1))`;;

(* --- list of GHASH input blocks: full blocks ++ masked tail --- *)
let gcm_ghash_blocks = new_definition
  `gcm_ghash_blocks (len:num) (P:byte list) (ivec:(128)word) (rks:int128 list) : (int128 list) =
     let tail = len - 16 * ((len - 1) DIV 16) in
     let nfull = (len - 1) DIV 16 in
     APPEND (gcm_ct_rec 0 nfull P ivec rks)
            [gcm_ctm_tail nfull tail P ivec rks]`;;

(* --- the ciphertext byte list (output): full block bytes ++ first `tail`     *)
(* bytes of the masked partial block; [] for empty input.                     *)
let aes256_gcm_encrypt = new_definition
  `aes256_gcm_encrypt (len:num) (P:byte list) (ivec:(128)word) (rks:int128 list) : (byte list) =
     let tail = len - 16 * ((len - 1) DIV 16) in
     let nfull = (len - 1) DIV 16 in
     if len = 0 then []
     else APPEND (gcm_ct_bytes_rec 0 nfull P ivec rks)
                 (SUB_LIST (0, tail) (int128_to_bytes (gcm_ctm_tail nfull tail P ivec rks)))`;;

(* --- the final GHASH accumulator Xi; unchanged for empty input. --- *)
let gcm_final_xi = new_definition
  `gcm_final_xi (len:num) (P:byte list) (ivec:(128)word) (rks:int128 list)
                (xi:(128)word) (h:(128)word) : (128)word =
     if len = 0 then xi
     else word_reversefields 8
       (ghash_polyval_acc h (word_reversefields 8 xi)
          (MAP (\b. word_reversefields 8 b) (gcm_ghash_blocks len P ivec rks)))`;;

(* ========================================================================= *)
(* Bridge lemmas: concrete 1-block band postcondition <-> abstract spec.      *)
(* ========================================================================= *)

let KS0_LEMMA = prove(
  `gcm_keystream 0 ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] =
   aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14`,
  REWRITE_TAC[gcm_keystream; gcm_ctr_iter] THEN
  REWRITE_TAC(map num_CONV [`14`;`13`;`12`;`11`;`10`;`9`;`8`;`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[EL; HD; TL]);;

let NFULL0_LEMMA = prove(
  `!n. 1 <= n /\ n <= 16 ==> (n - 1) DIV 16 = 0 /\ n - 16 * ((n-1) DIV 16) = n`,
  REPEAT STRIP_TAC THENL
   [SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `(n-1) DIV 16 = 0` SUBST1_TAC THENL
     [SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let SUB_LIST_0_16 = prove(
  `!l:(byte)list. LENGTH l = 16 ==> SUB_LIST (0,16) l = l`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM (ASSUME `LENGTH(l:byte list) = 16`)] THEN
  REWRITE_TAC[SUB_LIST_LENGTH]);;

let EL_16_8_CLAUSES = (CONJUNCTS o prove)
 (`EL 0 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a0 /\
   EL 1 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a1 /\
   EL 2 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a2 /\
   EL 3 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a3 /\
   EL 4 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a4 /\
   EL 5 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a5 /\
   EL 6 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a6 /\
   EL 7 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a7 /\
   EL 8 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a8 /\
   EL 9 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a9 /\
   EL 10 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a10 /\
   EL 11 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a11 /\
   EL 12 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a12 /\
   EL 13 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a13 /\
   EL 14 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a14 /\
   EL 15 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a15`,
  REWRITE_TAC(map num_CONV [`15`;`14`;`13`;`12`;`11`;`10`;`9`;`8`;`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[EL; HD; TL]);;

let BYTES128_TO_BYTES8_THM = prove(
  `!pos bl_ptr s.
    read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
    bytes_to_int128
      [read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x0)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x1)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x2)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x3)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x4)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x5)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x6)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x7)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x8)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x9)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xa)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xb)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xc)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xd)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xe)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xf)))) s]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bytes_to_int128] THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  GEN_REWRITE_TAC TOP_DEPTH_CONV [READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ONCE_REWRITE_TAC [ARITH_RULE `pos + 0 = (pos:num)`] THEN REFL_TAC);;

let LIST_OF_EL_16 = prove(
  `!l:(byte)list. LENGTH l = 16 ==>
     [EL 0 l; EL 1 l; EL 2 l; EL 3 l; EL 4 l; EL 5 l; EL 6 l; EL 7 l;
      EL 8 l; EL 9 l; EL 10 l; EL 11 l; EL 12 l; EL 13 l; EL 14 l; EL 15 l] = l`,
  REWRITE_TAC[ARITH_RULE `16 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC 0)))))))))))))))`] THEN
  REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC(map num_CONV [`15`;`14`;`13`;`12`;`11`;`10`;`9`;`8`;`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[EL; HD; TL]);;

let GCM_VAL16 = WORD_REDUCE_CONV `val(word 16:int64)`;;

let BYTE_LIST_AT_16_BYTES128 = prove(
  `!pt_in in_ptr s. byte_list_at pt_in in_ptr (word 16) s /\ LENGTH pt_in = 16
     ==> read (memory :> bytes128 in_ptr) s = bytes_to_int128 pt_in`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `in_ptr = word_add in_ptr (word 0):int64` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[BYTES128_TO_BYTES8_THM] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  FIRST_X_ASSUM(fun th -> if (try fst(dest_const(repeat rator (concl th)))="byte_list_at" with _->false)
    then ASSUME_TAC(REWRITE_RULE[byte_list_at; GCM_VAL16] th) else NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) then
    (MAP_EVERY (fun i -> ASSUME_TAC(REWRITE_RULE[ARITH; WORD_ADD_0](MATCH_MP th (ARITH_RULE(vsubst[mk_small_numeral i,`i:num`] `i < 16`)))))
      [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]) else NO_TAC)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LIST_OF_EL_16]);;

let SUBWORD_BYTES_TO_INT128 = prove(
 `!b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 i. i < 16
   ==> word_subword (bytes_to_int128 [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]) (8*i,8):byte =
       EL i [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[bytes_to_int128] THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC WORD_BLAST);;

let BYTES128_TO_BYTES8_0 = REWRITE_RULE[ADD_CLAUSES; WORD_ADD_0] (SPEC `0` BYTES128_TO_BYTES8_THM);;

let BYTE8_OF_BYTES128 = prove(
 `!p s i. i < 16 ==> read (memory :> bytes8 (word_add p (word i))) s =
                     word_subword (read (memory :> bytes128 p) s) (8*i,8)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [BYTES128_TO_BYTES8_0] THEN
  ASM_SIMP_TAC[SUBWORD_BYTES_TO_INT128] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN REWRITE_TAC[WORD_ADD_0]);;

let EL_SUB_LIST_0 = prove(
 `!(l:A list) n i. i < n ==> EL i (SUB_LIST(0,n) l) = EL i l`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[SUB_LIST_CLAUSES];
    ASM_CASES_TAC `n = 0` THENL [ASM_MESON_TAC[LT]; ALL_TAC] THEN
    SUBGOAL_THEN `n = SUC(n-1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES] THEN
    ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[EL; HD; TL] THEN
    SUBGOAL_THEN `i = SUC(i-1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL; TL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let EL_INT128_TO_BYTES = prove(
 `!w i. i < 16 ==> EL i (int128_to_bytes w):byte = word_subword w (8*i,8)`,
  GEN_TAC THEN REWRITE_TAC[int128_to_bytes] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[]);;

let MASK_BYTE_OUT = prove(
 `!(ct:int128) (out0:int128) (n:num) (i:num).
    i < n /\ n <= 16
    ==> word_subword (word_or (word_and ct (word (2 EXP (8*n) - 1):int128))
                              (word_and out0 (word_not (word (2 EXP (8*n) - 1):int128)))) (8*i,8):byte =
        word_subword ct (8*i,8)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_NOT;
              BIT_MASK_WORD; DIMINDEX_8; DIMINDEX_128] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * i + j < 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 * i + j < 8 * n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let XI_BRIDGE_1B = prove(
 `!len pt_in ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14 xi h.
    1 <= val(len:int64) /\ val len <= 16 /\ LENGTH pt_in = 16
    ==> word_reversefields 8
          (ghash_polyval_acc h (word_reversefields 8 xi)
            [word_reversefields 8
               (word_and (word_xor (bytes_to_int128 pt_in)
                            (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14))
                         (word (2 EXP (8 * val len) - 1)))]) =
        gcm_final_xi (val len) pt_in ivec
          [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[gcm_final_xi] THEN
  SUBGOAL_THEN `~(val(len:int64) = 0)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPEC `val(len:int64)` NFULL0_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[gcm_ct_rec; APPEND; MAP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[SUB_LIST_0_16; MULT_CLAUSES; ARITH_RULE `0 * 16 = 0`] THEN
  REWRITE_TAC[KS0_LEMMA]);;

let OUT_BRIDGE_1B = prove(
 `!len pt_in out0 ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14 out_ptr s.
    1 <= val(len:int64) /\ val len <= 16 /\ LENGTH pt_in = 16 /\
    read (memory :> bytes128 out_ptr) s =
      word_or (word_and (word_xor (bytes_to_int128 pt_in)
                          (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14))
                        (word (2 EXP (8 * val len) - 1)))
              (word_and out0 (word_not (word (2 EXP (8 * val len) - 1):int128)))
    ==> byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec
                        [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                     out_ptr len s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[byte_list_at] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < 16` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[BYTE8_OF_BYTES128] THEN
  REWRITE_TAC[aes256_gcm_encrypt] THEN
  MP_TAC(SPEC `val(len:int64)` NFULL0_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `~(val(len:int64) = 0)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[gcm_ct_bytes_rec; APPEND] THEN
  ASM_SIMP_TAC[EL_SUB_LIST_0] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[SUB_LIST_0_16; MULT_CLAUSES; ARITH_RULE `0 * 16 = 0`; KS0_LEMMA] THEN
  ASM_SIMP_TAC[EL_INT128_TO_BYTES] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MASK_BYTE_OUT] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_AND; BIT_MASK_WORD; DIMINDEX_8; DIMINDEX_128] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * i + j < 128 /\ 8 * i + j < 8 * val(len:int64)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
