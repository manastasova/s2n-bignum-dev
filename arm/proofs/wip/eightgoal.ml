let gcm_8b_goal = `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (pt4:(128)word) (pt5:(128)word) (pt6:(128)word) (pt7:(128)word) (pt8:(128)word)
    (out0:(128)word)
    (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word)
    (q18i:(128)word)
    byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (896 + 8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128 (word_add in_ptr (word 48))) s = pt4 /\
           read (memory :> bytes128 (word_add in_ptr (word 64))) s = pt5 /\
           read (memory :> bytes128 (word_add in_ptr (word 80))) s = pt6 /\
           read (memory :> bytes128 (word_add in_ptr (word 96))) s = pt7 /\
           read (memory :> bytes128 (word_add in_ptr (word 112))) s = pt8 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = out0 /\
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
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s =
             byteswap128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s =
             byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s =
             byteswap128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s =
             byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s =
             byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s =
             byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word =
             karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s.
           let ct1 =
             word_xor pt1
               (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let ct2 =
             word_xor pt2
               (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let ct3 =
             word_xor pt3
               (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc ivec)) rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let ct4 =
             word_xor pt4
               (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let ct5 =
             word_xor pt5
               (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))) rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let ct6 =
             word_xor pt6
               (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))) rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let ct7 =
             word_xor pt7
               (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))))) rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let ct8 =
             word_xor pt8
               (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))))) rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm8 = word_and ct8 mask in
           read PC s = word(pc + 4588) /\
           read X0 s = word (112 + byte_len) /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = ct3 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = ct4 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = ct5 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = ct6 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = ct7 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s =
             word_or ctm8 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2;
                                     word_reversefields 8 ct3;
                                     word_reversefields 8 ct4;
                                     word_reversefields 8 ct5;
                                     word_reversefields 8 ct6;
                                     word_reversefields 8 ct7;
                                     word_reversefields 8 ctm8]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
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
                  memory :> bytes64 (word_add stackptr (word 72))])`;;
