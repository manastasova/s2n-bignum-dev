(* Integration test: abstract 2-block band lemma from concrete LT_2BLOCK_CORRECT.
   Load after /tmp/gcm_2b_prefix.ml (has the concrete 2-block + spec + bridges).
   GHASH_BLOCKS_THMS must be in scope (regenerate via mk_ghash_blocks_thm). *)

let GHASH_BLOCKS_2 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 1 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks))
                   (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`1`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[num_CONV `1`; GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let AES256_GCM_ENCRYPT_LT_2BLOCK_ABS = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt_in:byte list) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (len:int64) stackptr pc.
    16 + 1 <= val len /\ val len <= 16 + 16 /\ LENGTH pt_in = 32 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,32) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,32) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,32) (out_ptr,32) /\
    nonoverlapping (in_ptr,32) (xi_ptr,16) /\
    nonoverlapping (in_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,32) (xi_ptr,16) /\
    nonoverlapping (out_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,32) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,32) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,32) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,32) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,32) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           byte_list_at pt_in in_ptr (word 32) s /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = out0 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = byteswap128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s =
             byteswap128 (polyval_dot h h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h))
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec
                          [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec
               [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,32);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(len:int64) = 0) /\ val len = 16 * 1 + (val len - 16)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `byte_len = val(len:int64) - 16` THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if val(len:int64)=0 then 4596 else 4588) = 4588` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `8 * val(len:int64) = 128 + 8 * byte_len` ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`in_ptr:int64`;`out_ptr:int64`;`xi_ptr:int64`;`ivec_ptr:int64`;`key_ptr:int64`;`htable_ptr:int64`;
    `bytes_to_int128 (SUB_LIST(0,16) pt_in)`; `bytes_to_int128 (SUB_LIST(16,16) pt_in)`;
    `out0:(128)word`;`ivec:(128)word`;
    `rk0:(128)word`;`rk1:(128)word`;`rk2:(128)word`;`rk3:(128)word`;`rk4:(128)word`;`rk5:(128)word`;
    `rk6:(128)word`;`rk7:(128)word`;`rk8:(128)word`;`rk9:(128)word`;`rk10:(128)word`;`rk11:(128)word`;
    `rk12:(128)word`;`rk13:(128)word`;`rk14:(128)word`;
    `xi:(128)word`;`h:(128)word`;`h1k:(128)word`;`byte_len:num`;`stackptr:int64`;`pc:num`]
   AES256_GCM_ENCRYPT_LT_2BLOCK_CORRECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun band ->
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [(* post-impl *)
      GEN_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [(* PC *) ASM_REWRITE_TAC[];
        (* X0 = len *)
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `16 + byte_len = val(len:int64)` SUBST1_TAC THENL
         [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC;
          REWRITE_TAC[WORD_VAL]];
        (* output byte_list_at *)
        MATCH_MP_TAC OUT_BRIDGE_GEN THEN
        MAP_EVERY EXISTS_TAC [`1`; `byte_len:num`; `out0:(128)word`] THEN
        REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[];
          EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC;
          X_GEN_TAC `k:num` THEN REWRITE_TAC[ARITH_RULE `k < 1 <=> k = 0`] THEN
          DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
          REWRITE_TAC CTR_ITER_CLAUSES THEN REWRITE_TAC[WORD_ADD_0] THEN
          CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]];
        (* xi = gcm_final_xi *)
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GCM_FINAL_XI_UNFOLD; ARITH_RULE `1 <= byte_len ==> ~(16 * 1 + byte_len = 0)`] THEN
        MP_TAC(SPECL [`byte_len:num`;`pt_in:byte list`;`ivec:(128)word`;
                      `[rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]:int128 list`]
               GHASH_BLOCKS_2) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[MAP] THEN REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES];
      (* pre-impl: combined pre ==> band pre (only diff: the 2 input-block reads) *)
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        SUBGOAL_THEN `val(word 32:int64) = 32` ASSUME_TAC THENL
         [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
        (* band C-arg word(128+8*byte_len) = combined word(8*val len) *)
        FIRST_ASSUM(fun th -> if concl th = `8 * val(len:int64) = 128 + 8 * byte_len`
                              then REWRITE_TAC[SYM th] else NO_TAC) THEN
        (* derive the two input-block reads as assumptions, then ASM_REWRITE closes the band-pre *)
        SUBGOAL_THEN
          `read (memory :> bytes128 in_ptr) x =
             bytes_to_int128 (SUB_LIST (0,16) pt_in) /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) x =
             bytes_to_int128 (SUB_LIST (16,16) pt_in)`
          STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL
           [MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`2`;`0`;`x:armstate`] INPUT_BLOCK_BL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[WORD_ADD_0];
            MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`2`;`1`;`x:armstate`] INPUT_BLOCK_BL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]];
          ASM_REWRITE_TAC[]];
        ACCEPT_TAC band]]));;

print_string("\n\nABS-2 TEST: hyps="^string_of_int(length(hyp AES256_GCM_ENCRYPT_LT_2BLOCK_ABS))^"\n");;
