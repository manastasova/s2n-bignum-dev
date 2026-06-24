(* ========================================================================= *)
(* Combined XTS-style correctness theorem for the single-binary AES-256-GCM   *)
(* encrypt kernel, dispatching by input length to the per-band lemmas.        *)
(*                                                                            *)
(* SCOPE (this file): val len <= 16, i.e. the two lowest bands                *)
(*   - len = 0          -> AES256_GCM_ENCRYPT_LT_0BLOCK_CORRECT (early exit)   *)
(*   - 1 <= len <= 16   -> AES256_GCM_ENCRYPT_LT_1BLOCK_CORRECT (one block)    *)
(*                                                                            *)
(* Mirrors the XTS combined proof AES256_XTS_ENCRYPT_CORRECT EXACTLY: the      *)
(* per-band lemmas are stated NATIVELY in the abstract byte_list_at /          *)
(* aes256_gcm_encrypt / gcm_final_xi spec form, so the top-level dispatch is   *)
(* one line per band:  MP_TAC band THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP. *)
(*                                                                            *)
(* The raw symbolic-simulation results are kept as private CONCRETE lemmas     *)
(* (AES256_GCM_ENCRYPT_LT_{0,1}BLOCK_CONCRETE, in word form); each abstract    *)
(* band lemma below is derived from its CONCRETE counterpart via the bridges   *)
(* (BYTE_LIST_AT_16_BYTES128 / OUT_BRIDGE_1B / XI_BRIDGE_1B) and, for the      *)
(* 0-block early exit, frame subsumption.  All concrete<->abstract bridging    *)
(* thus lives INSIDE the band lemma (as in XTS), not in the combined proof.    *)
(*                                                                            *)
(* NOTE on the conditional exit PC: unlike XTS (whose bands all land at one    *)
(* PC), the GCM binary sends ONLY the zero-length case to a separate early-    *)
(* exit stub.  `cbz x1,0x11f0`@pc+4 -> mov w0,#0 -> ret@pc+4596 for len=0;     *)
(* every non-empty length runs the body and rets at the main ret@pc+4588.     *)
(* Hence the faithful postcondition uses                                      *)
(*   read PC s = word(pc + (if val len = 0 then 4596 else 4588)).             *)
(*                                                                            *)
(* Requires (load first): the CONCRETE band lemmas LT_0BLOCK + LT_1BLOCK from  *)
(* arm/proofs/aes256_gcm.ml, then arm/proofs/wip/gcm_encrypt_spec.ml           *)
(* (the recursive spec + bridge lemmas).                                       *)
(* ========================================================================= *)

(* --- band lemma (abstract): 1 <= val len <= 16, one-block path -> pc+4588 --- *)

let AES256_GCM_ENCRYPT_LT_1BLOCK_CORRECT = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt_in:byte list) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) len stackptr pc.
    1 <= val (len:int64) /\ val len <= 16 /\ LENGTH pt_in = 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,16) (out_ptr,16) /\
    nonoverlapping (in_ptr,16) (xi_ptr,16) /\
    nonoverlapping (in_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,16) (xi_ptr,16) /\
    nonoverlapping (out_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,16) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,16) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,16) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,16) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,16) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           byte_list_at pt_in in_ptr (word 16) s /\
           read (memory :> bytes128 out_ptr) s = out0 /\
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
           word_subword h1k (0,64):(64)word = karatsuba_mid h)
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec
                          [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec
               [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,16);
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
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(val(len:int64) = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL
   [`in_ptr:int64`;`out_ptr:int64`;`xi_ptr:int64`;`ivec_ptr:int64`;
    `key_ptr:int64`;`htable_ptr:int64`;`bytes_to_int128 pt_in`;
    `out0:(128)word`;`ivec:(128)word`;
    `rk0:(128)word`;`rk1:(128)word`;`rk2:(128)word`;`rk3:(128)word`;
    `rk4:(128)word`;`rk5:(128)word`;`rk6:(128)word`;`rk7:(128)word`;
    `rk8:(128)word`;`rk9:(128)word`;`rk10:(128)word`;`rk11:(128)word`;
    `rk12:(128)word`;`rk13:(128)word`;`rk14:(128)word`;
    `xi:(128)word`;`h:(128)word`;`h1k:(128)word`;
    `val(len:int64)`;`stackptr:int64`;`pc:num`]
   AES256_GCM_ENCRYPT_LT_1BLOCK_CONCRETE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun band ->
    (* weaken postcondition: band concrete post ==> abstract spec post *)
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[WORD_VAL];
        MATCH_MP_TAC OUT_BRIDGE_1B THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `out0:(128)word` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC XI_BRIDGE_1B THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      (* weaken precondition: combined pre ==> band concrete pre *)
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC BYTE_LIST_AT_16_BYTES128 THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;

(* --- band lemma (abstract): val len = 0, early-exit path -> pc+4596 --- *)
let AES256_GCM_ENCRYPT_LT_0BLOCK_CORRECT = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt_in:byte list) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) len stackptr pc.
    val (len:int64) = 0 /\ val len <= 16 /\ LENGTH pt_in = 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,16) (out_ptr,16) /\
    nonoverlapping (in_ptr,16) (xi_ptr,16) /\
    nonoverlapping (in_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,16) (xi_ptr,16) /\
    nonoverlapping (out_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,16) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,16) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,16) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,16) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,16) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           byte_list_at pt_in in_ptr (word 16) s /\
           read (memory :> bytes128 out_ptr) s = out0 /\
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
           word_subword h1k (0,64):(64)word = karatsuba_mid h)
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec
                          [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec
               [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,16);
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
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `len:int64 = word 0` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES] THEN
  REWRITE_TAC[aes256_gcm_encrypt; gcm_final_xi; byte_list_at; VAL_WORD_0;
              LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL
   [`in_ptr:int64`;`out_ptr:int64`;`xi_ptr:int64`;`ivec_ptr:int64`;
    `key_ptr:int64`;`htable_ptr:int64`;`out0:(128)word`;`xi:(128)word`;
    `stackptr:int64`;`pc:num`]
   AES256_GCM_ENCRYPT_LT_0BLOCK_CONCRETE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun band ->
    (* the 0-block band has the smaller frame [ABI ,, PC]: shrink first *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      SUBSUMED_MAYCHANGE_TAC;
      (* weaken postcondition: band concrete post ==> abstract spec post *)
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC;
        (* weaken precondition: combined pre ==> band concrete pre *)
        MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
        EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
         [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
          ACCEPT_TAC band]]]));;

(* --- the combined theorem: clean XTS-style dispatch over the two bands --- *)
let AES256_GCM_ENCRYPT_CORRECT = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt_in:byte list) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) len stackptr pc.
    val (len:int64) <= 16 /\ LENGTH pt_in = 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,16) (out_ptr,16) /\
    nonoverlapping (in_ptr,16) (xi_ptr,16) /\
    nonoverlapping (in_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,16) (xi_ptr,16) /\
    nonoverlapping (out_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,16) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,16) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,16) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,16) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,16) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           byte_list_at pt_in in_ptr (word 16) s /\
           read (memory :> bytes128 out_ptr) s = out0 /\
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
           word_subword h1k (0,64):(64)word = karatsuba_mid h)
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec
                          [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec
               [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,16);
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
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `val(len:int64) = 0` THENL
   [MP_TAC AES256_GCM_ENCRYPT_LT_0BLOCK_CORRECT THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    MP_TAC AES256_GCM_ENCRYPT_LT_1BLOCK_CORRECT THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> 1 <= n`]]);;
