(* ========================================================================= *)
(* Generic N-block bridge machinery for the combined AES-256-GCM theorem.     *)
(* Relates the concrete word-level band postconditions (bands 2..8) to the    *)
(* abstract recursive spec aes256_gcm_encrypt / gcm_final_xi.                 *)
(*                                                                            *)
(* Load AFTER arm/proofs/wip/gcm_encrypt_spec.ml (spec + 1-block bridges).    *)
(* ========================================================================= *)

(* --- arithmetic: for a band-N call len = 16*nfull + tail, 1<=tail<=16 --- *)
let NFULL_LEMMA' = prove(
  `!nfull tail. 1 <= tail /\ tail <= 16
     ==> ((16 * nfull + tail) - 1) DIV 16 = nfull /\
         (16 * nfull + tail) - 16 * (((16 * nfull + tail) - 1) DIV 16) = tail`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((16 * nfull + tail) - 1) DIV 16 = nfull` ASSUME_TAC THENL
   [SUBGOAL_THEN `(16 * nfull + tail) - 1 = nfull * 16 + (tail - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    SUBGOAL_THEN `(tail - 1) DIV 16 = 0` SUBST1_TAC THENL
     [SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC; ARITH_TAC];
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* --- EL of a SUB_LIST at general start offset --- *)
let EL_SUB_LIST_GEN = prove(
 `!m (l:A list) n i. m + n <= LENGTH l /\ i < n ==> EL i (SUB_LIST(m,n) l) = EL (m+i) l`,
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THENL
   [MESON_TAC[EL_SUB_LIST_0]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC m + n <= 0)`] THEN
  REPEAT STRIP_TAC THENL
   [UNDISCH_TAC `SUC (m + n) <= 0` THEN ARITH_TAC;
    REWRITE_TAC[SUB_LIST_CLAUSES; EL; TL] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* --- block-k input bridge: the k-th 128-bit block read = bytes_to_int128 of  *)
(* the k-th 16-byte sublist of the plaintext byte list. --- *)
let BYTE_LIST_AT_BLOCK = prove(
 `!pt_in in_ptr nblk k s.
    (!i. i < 16 * nblk ==> read (memory :> bytes8 (word_add in_ptr (word i))) s = EL i pt_in) /\
    LENGTH pt_in = 16 * nblk /\ k < nblk
    ==> read (memory :> bytes128 (word_add in_ptr (word (16 * k)))) s =
        bytes_to_int128 (SUB_LIST (16 * k, 16) pt_in)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BYTES128_TO_BYTES8_THM] THEN
  REWRITE_TAC[bytes_to_int128] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  SUBGOAL_THEN
   `!j. j < 16 ==> read (memory :> bytes8 (word_add in_ptr (word (16 * k + j)))) s =
                   EL j (SUB_LIST(16*k,16) (pt_in:byte list))`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `16 * k + 16 <= LENGTH(pt_in:byte list)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_SUB_LIST_GEN] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `16 * k + j`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    REWRITE_TAC EL_16_8_CLAUSES THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC(map (fun i ->
      MATCH_MP th (ARITH_RULE(vsubst[mk_small_numeral i,`j:num`]`j<16`)))
      [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15])) THEN
    REWRITE_TAC[ADD_CLAUSES]]);;

(* --- one-step unfolds of the recursive ciphertext builders --- *)
let GCM_CT_REC_STEP = prove(
  `gcm_ct_rec i 0 P ivec rks = [] /\
   gcm_ct_rec i (SUC m) P ivec rks =
     CONS (word_xor (bytes_to_int128 (SUB_LIST(i*16,16) P)) (gcm_keystream i ivec rks))
          (gcm_ct_rec (i+1) m P ivec rks)`,
  CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [gcm_ct_rec] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; LET_DEF; LET_END_DEF; ADD1]);;

let GCM_CT_BYTES_REC_STEP = prove(
  `gcm_ct_bytes_rec i 0 P ivec rks = [] /\
   gcm_ct_bytes_rec i (SUC m) P ivec rks =
     APPEND (int128_to_bytes (word_xor (bytes_to_int128 (SUB_LIST(i*16,16) P)) (gcm_keystream i ivec rks)))
            (gcm_ct_bytes_rec (i+1) m P ivec rks)`,
  CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [gcm_ct_bytes_rec] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; LET_DEF; LET_END_DEF; ADD1]);;

(* --- keystream at iterate i in terms of gcm_ctr_iter --- *)
let KS_ITER = prove(
  `!i. gcm_keystream i ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] =
       aes256_block_enc (gcm_ctr_iter i ivec) rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14`,
  GEN_TAC THEN REWRITE_TAC[gcm_keystream] THEN
  REWRITE_TAC(map num_CONV [`14`;`13`;`12`;`11`;`10`;`9`;`8`;`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[EL; HD; TL]);;

let CTR_ITER_CLAUSES = (CONJUNCTS o prove)(
  `gcm_ctr_iter 0 ivec = ivec /\
   gcm_ctr_iter 1 ivec = gcm_ctr_inc ivec /\
   gcm_ctr_iter 2 ivec = gcm_ctr_inc (gcm_ctr_inc ivec) /\
   gcm_ctr_iter 3 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)) /\
   gcm_ctr_iter 4 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) /\
   gcm_ctr_iter 5 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))) /\
   gcm_ctr_iter 6 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))) /\
   gcm_ctr_iter 7 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))))`,
  REWRITE_TAC(map num_CONV [`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[gcm_ctr_iter]);;

(* --- small DIV/MOD helpers for the recursive EL lemma --- *)
let ADD16_DIV = prove(`!j. (j + 16) DIV 16 = j DIV 16 + 1`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `j + 16 = 1 * 16 + j`] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC);;
let ADD16_MOD = prove(`!j. (j + 16) MOD 16 = j MOD 16`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `j + 16 = 1 * 16 + j`] THEN
  SIMP_TAC[MOD_MULT_ADD; ARITH_EQ]);;

(* --- byte i of the recursive full-block ciphertext byte list --- *)
let EL_GCM_CT_BYTES_REC = prove(
 `!nfull base P ivec rks i.
    i < 16 * nfull
    ==> EL i (gcm_ct_bytes_rec base nfull P ivec rks) =
        word_subword (word_xor (bytes_to_int128 (SUB_LIST(16*(base + i DIV 16),16) P))
                               (gcm_keystream (base + i DIV 16) ivec rks))
                     (8 * (i MOD 16), 8)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; LT] THEN ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[GCM_CT_BYTES_REC_STEP] THEN
    SUBGOAL_THEN `LENGTH(int128_to_bytes (word_xor (bytes_to_int128 (SUB_LIST(base*16,16) P)) (gcm_keystream base ivec rks))) = 16`
        ASSUME_TAC THENL [REWRITE_TAC[int128_to_bytes; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `i < 16` THENL
     [SUBGOAL_THEN `i DIV 16 = 0 /\ i MOD 16 = i` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_SIMP_TAC[DIV_LT; MOD_LT]; ALL_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES] THEN
      ASM_SIMP_TAC[EL_APPEND] THEN
      ASM_SIMP_TAC[EL_INT128_TO_BYTES] THEN
      REWRITE_TAC[MULT_AC];
      ASM_SIMP_TAC[EL_APPEND] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`base + 1`; `P:byte list`; `ivec:(128)word`; `rks:int128 list`; `i - 16`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `i = (i - 16) + 16` (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD16_DIV; ADD16_MOD] THEN
      REWRITE_TAC[ARITH_RULE `(base + 1) + j = base + (j + 1)`]]]);;

let LENGTH_GCM_CT_BYTES_REC = prove(
 `!nfull base P ivec rks. LENGTH(gcm_ct_bytes_rec base nfull P ivec rks) = 16 * nfull`,
  INDUCT_TAC THEN REWRITE_TAC[GCM_CT_BYTES_REC_STEP; LENGTH; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; int128_to_bytes; LENGTH] THEN ARITH_TAC);;

(* --- GENERIC OUTPUT BRIDGE: N-1 full ct stores + masked tail = byte_list_at spec --- *)
let OUT_BRIDGE_GEN = prove(
 `!nfull tail pt_in ivec rks out0 out_ptr (len:int64) s.
    1 <= tail /\ tail <= 16 /\ val len = 16 * nfull + tail /\
    (!k. k < nfull
         ==> read (memory :> bytes128 (word_add out_ptr (word (16 * k)))) s =
             word_xor (bytes_to_int128 (SUB_LIST(16*k,16) pt_in)) (gcm_keystream k ivec rks)) /\
    read (memory :> bytes128 (word_add out_ptr (word (16 * nfull)))) s =
      word_or (word_and (word_xor (bytes_to_int128 (SUB_LIST(16*nfull,16) pt_in)) (gcm_keystream nfull ivec rks))
                        (word (2 EXP (8 * tail) - 1)))
              (word_and out0 (word_not (word (2 EXP (8 * tail) - 1):int128)))
    ==> byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec rks) out_ptr len s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[byte_list_at] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[aes256_gcm_encrypt] THEN
  MP_TAC(SPECL [`nfull:num`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i < 16 * nfull` THENL
   [(* full-block region *)
    SUBGOAL_THEN `EL i (APPEND (gcm_ct_bytes_rec 0 nfull pt_in ivec rks)
         (SUB_LIST (0,tail) (int128_to_bytes (gcm_ctm_tail nfull tail pt_in ivec rks)))) =
       EL i (gcm_ct_bytes_rec 0 nfull pt_in ivec rks)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[EL_APPEND; LENGTH_GCM_CT_BYTES_REC]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_GCM_CT_BYTES_REC; ADD_CLAUSES] THEN
    SUBGOAL_THEN `word_add out_ptr (word i):int64 =
         word_add (word_add out_ptr (word (16 * (i DIV 16)))) (word (i MOD 16))`
       SUBST1_TAC THENL
     [SUBGOAL_THEN `i = 16 * (i DIV 16) + i MOD 16` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
       [MESON_TAC[DIVISION_SIMP]; ALL_TAC] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    MP_TAC(SPECL [`word_add out_ptr (word (16 * (i DIV 16))):int64`; `s:armstate`; `i MOD 16`] BYTE8_OF_BYTES128) THEN
    ANTS_TAC THENL [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    SUBGOAL_THEN `i DIV 16 < nfull` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) then MP_TAC(SPEC `i DIV 16` th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    (* tail region *)
    SUBGOAL_THEN `LENGTH(gcm_ct_bytes_rec 0 nfull pt_in ivec rks) = 16 * nfull` ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_GCM_CT_BYTES_REC]; ALL_TAC] THEN
    SUBGOAL_THEN `EL i (APPEND (gcm_ct_bytes_rec 0 nfull pt_in ivec rks)
         (SUB_LIST (0,tail) (int128_to_bytes (gcm_ctm_tail nfull tail pt_in ivec rks)))) =
       EL (i - 16 * nfull) (SUB_LIST (0,tail) (int128_to_bytes (gcm_ctm_tail nfull tail pt_in ivec rks)))`
       SUBST1_TAC THENL
     [ASM_SIMP_TAC[EL_APPEND]; ALL_TAC] THEN
    ABBREV_TAC `j = i - 16 * nfull` THEN
    SUBGOAL_THEN `j < tail /\ j < 16 /\ i = 16 * nfull + j` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "j" THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_SUB_LIST_0; EL_INT128_TO_BYTES] THEN
    REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN `word_add out_ptr (word (16 * nfull + j)):int64 =
         word_add (word_add out_ptr (word (16 * nfull))) (word j)` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    MP_TAC(SPECL [`word_add out_ptr (word (16 * nfull)):int64`; `s:armstate`; `j:num`] BYTE8_OF_BYTES128) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    ASM_SIMP_TAC[MASK_BYTE_OUT] THEN
    REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_AND; BIT_MASK_WORD; DIMINDEX_8; DIMINDEX_128] THEN
    X_GEN_TAC `b:num` THEN STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* --- input block read directly from byte_list_at (for the pre-impl) --- *)
let INPUT_BLOCK_BL = prove(
 `!pt_in in_ptr nblk k s.
    byte_list_at pt_in in_ptr (word (16 * nblk)) s /\ LENGTH pt_in = 16 * nblk /\
    val(word(16 * nblk):int64) = 16 * nblk /\ k < nblk
    ==> read (memory :> bytes128 (word_add in_ptr (word (16 * k)))) s =
        bytes_to_int128 (SUB_LIST (16 * k, 16) pt_in)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BYTE_LIST_AT_BLOCK THEN
  EXISTS_TAC `nblk:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if free_in `byte_list_at` (concl th) then
     MP_TAC(REWRITE_RULE[byte_list_at] th) else NO_TAC) THEN
  ASM_REWRITE_TAC[]);;

(* --- all 8 input-block reads from a 128-byte byte_list_at (for the dispatch pre-impl) --- *)
let INPUT_READS_128 = prove(
 `!pt_in in_ptr s.
    byte_list_at pt_in in_ptr (word 128) s /\ LENGTH pt_in = 128
   ==> read (memory :> bytes128 in_ptr) s = bytes_to_int128 (SUB_LIST (0,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 16))) s = bytes_to_int128 (SUB_LIST (16,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 32))) s = bytes_to_int128 (SUB_LIST (32,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 48))) s = bytes_to_int128 (SUB_LIST (48,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 64))) s = bytes_to_int128 (SUB_LIST (64,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 80))) s = bytes_to_int128 (SUB_LIST (80,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 96))) s = bytes_to_int128 (SUB_LIST (96,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 112))) s = bytes_to_int128 (SUB_LIST (112,16) pt_in)`,
  let INB k = (MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`8`;mk_small_numeral k;`s:armstate`] INPUT_BLOCK_BL) THEN
               CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
               ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_THEN ACCEPT_TAC]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word 128:int64) = 16 * 8` ASSUME_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [INB 0; INB 1; INB 2; INB 3; INB 4; INB 5; INB 6; INB 7]);;

(* --- gcm_final_xi unfold for nonempty input --- *)
let GCM_FINAL_XI_UNFOLD = prove(
 `!len pt_in ivec rks xi h. ~(len = 0)
   ==> gcm_final_xi len pt_in ivec rks xi h =
       word_reversefields 8
         (ghash_polyval_acc h (word_reversefields 8 xi)
            (MAP (\b. word_reversefields 8 b) (gcm_ghash_blocks len pt_in ivec rks)))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[gcm_final_xi]);;
