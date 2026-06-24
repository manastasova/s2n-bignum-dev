let TAIL_P1 =
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c3lo:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c3hi:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c4lo:(64)word) = word_subword (word_reversefields 8 (ctm4:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c4hi:(64)word) = word_subword (word_reversefields 8 (ctm4:(128)word)) (64,64)` THEN
  ABBREV_TAC `(xilo:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(xihi:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(hd0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(hd1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(he0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(he1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hf0:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hf1:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (64,64)` THEN
  ABBREV_TAC `(hg0:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hg1:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* Byte-form fold: ct1's definition (pt1 xor s13_1 xor rk14) leaks the
     (rev8 _)_lo/_hi byte forms into the (xi xor ct1) Karatsuba term; re-fold
     them to the c1lo/c1hi atoms (4-block-specific; ct1 is not opaque here). *)
  SUBGOAL_THEN
    `(word_xor (word_subword (word_reversefields 8 (pt1:(128)word)) (0,64))
               (word_xor (word_subword (word_reversefields 8 (s13_1:(128)word)) (0,64))
                         (word_subword (word_reversefields 8 (rk14:(128)word)) (0,64))) :(64)word
      = c1lo) /\
     (word_xor (word_subword (word_reversefields 8 (pt1:(128)word)) (64,64))
               (word_xor (word_subword (word_reversefields 8 (s13_1:(128)word)) (64,64))
                         (word_subword (word_reversefields 8 (rk14:(128)word)) (64,64))) :(64)word
      = c1hi)`
    (fun th -> REWRITE_TAC[th]) THENL
    [CONJ_TAC THENL
       [EXPAND_TAC "c1lo" THEN EXPAND_TAC "ct1" THEN
        REWRITE_TAC[GSYM WORD_REVERSEFIELDS_XOR_8_128; GSYM WORD_SUBWORD_XOR];
        EXPAND_TAC "c1hi" THEN EXPAND_TAC "ct1" THEN
        REWRITE_TAC[GSYM WORD_REVERSEFIELDS_XOR_8_128; GSYM WORD_SUBWORD_XOR]];
     ALL_TAC];;
