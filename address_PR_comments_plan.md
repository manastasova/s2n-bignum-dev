Detailed Refactor Plan: bit_reverse_per_byte → word_reversefields 
  DO NOT PUSH ANYTHING TO GITHUB!!
  
  1                                               
                                                                                                                    
  What we're doing and why                                                                                          
                                                                                                                    
  The reviewer wants Bridge A to use full 128-bit bit reversal (word_reversefields 1) instead of the current        
  bit-reversal-then-byte-reversal composition (bit_reverse_per_byte). The reviewer's claim is that this is "more    
  faithful to what the NIST encoding actually requires."                                                            
                                                                  
  The user now clarifies: "Inside Bridge A the entire bit_reversal should be implemented. Then afterward additional 
  byte-reversals should be removed."
                                                                                                                    
  This means:                                                                                                       
  1. Change bit_reverse_per_byte's definition to be word_reversefields 1 alone.
  2. After Bridge A, subsequent bridges (B, C) should lose their word_reversefields 8 wrappers because the byte-part
   is already absorbed into Bridge A.                                                                               
                                                                                                                    
  The critical math question                                      
                                                                                                                    
  Current definitions                                                                                               
                                                                                                                    
  nist_bit x i     = bit (8·⌊i/8⌋ + 7 - (i mod 8)) x           (* NIST MSB-first-per-byte *)                        
  bit_reverse_per_byte x = word_reversefields 8 (word_reversefields 1 x)                                            
                                                                                                                    
  Current NIST_BIT_AS_NATURAL:                                                                                      
  nist_bit x i <=> bit i (bit_reverse_per_byte x)   (for i < 128)                                                   
                                                                                                                    
  Under the reviewer's reinterpretation                                                                             
                                                                                                                    
  Per the reviewer's claim "NIST bit 0 = x^127 coefficient", the semantic mapping should be:                        
                                                                                                                    
  NIST bit i = HOL bit (127 - i)                                                                                    
                                                                                                                    
  That would mean redefine nist_bit:                                                                                
                                                                                                                    
  nist_bit x i = bit (127 - i) x    (* full flip *)                                                                 
                                                                                                                    
  Then NIST_BIT_AS_NATURAL becomes:                                                                                 
  nist_bit x i <=> bit i (word_reversefields 1 x)                                                                   
                                                                                                                    
  which is automatically true by the definition of word_reversefields 1. ✓                                          
                                                                                                                    
  This is consistent with the reviewer's claim: full bit reversal maps NIST bit i to HOL bit i directly, assuming   
  NIST's bit-numbering is left-to-right across the whole 128-bit string (as opposed to left-to-right-within-byte).  
                                                                                                                    
  Which interpretation is "correct" per NIST SP 800-38D?                                                            
   
  The spec prose says:                                                                                              
                                                                  
  ▎ "x_0 is the first bit of X, x_1 is the second bit, ..., x_127 is the last bit"                                  
                                                                  
  AND the spec separately specifies that an octet has bits labeled (b_7, b_6, ..., b_0) with b_7 being the MSB. So  
  when encoding a bit string into bytes, x_0 lands in the MSB slot of the first byte — which is the current nist_bit
   x 0 = bit 7 x interpretation.                                                                                    
                                                                  
  So the current encoding is correct for the NIST-to-memory mapping. BUT the reviewer's claim about the "natural"   
  polynomial mapping might still be that NIST bit 0 semantically represents x^127.
                                                                                                                    
  If both are true:                                               
  - NIST bit 0 → byte-MSB-first → HOL bit 7 (in memory)
  - NIST bit 0 → highest polynomial coefficient → x^127                                                             
                                                       
  Then NIST's storage convention (MSB-first within bytes, leading-byte-first across bytes) is a permutation that    
  happens to equal word_reversefields 8 ∘ word_reversefields 1 applied to the natural polynomial representation.    
  Which is exactly what the current bit_reverse_per_byte is.                                                        
                                                                                                                    
  The reviewer's suggestion thus conflates two things: the "semantic reversal" (NIST bit 0 ↔ x^127) and the         
  "encoding reversal" (how bits land in memory). They might be algebraically equivalent under one interpretation but
   the proof as written uses a specific encoding.                                                                   
                                                                  
  Viability assessment                                                                                              
   
  After this analysis, here's what I conclude:                                                                      
                                                                  
  Option B1 — Mechanically change bit_reverse_per_byte to word_reversefields 1: will break NIST_BIT_AS_NATURAL      
  because the lemma states a specific bit-position equality that holds for the composition, not the single reversal.
                                                                                                                    
  Option B2 — Redefine nist_bit to match the reviewer's interpretation (NIST bit i = HOL bit 127-i), then change    
  bit_reverse_per_byte to word_reversefields 1, then re-derive all downstream lemmas.
                                                                                                                    
  B2 is the real refactor. B1 is half-done.                                                                         
   
  Detailed plan for Option B2                                                                                       
                                                                  
  Step 1: Change nist_bit and related NIST primitives                                                               
                                                                  
  Both nist_bit and nist_shr1 (currently implemented in terms of HOL bits) need to shift from "MSB-first-per-byte"  
  encoding to "MSB-first-across-word" encoding.                   
                                                                                                                    
  nist_bit x i     = bit (127 - i) x                              
  nist_lsb v       = bit 0 v           (* was: bit 120 v *)                                                         
  nist_shr1 v      = ??? (need to re-derive — probably different formula)                                           
                                                                                                                    
  Problem: the nist_shr1 definition (lines 47-53) is tightly entangled with the MSB-first-per-byte encoding. If we  
  switch to MSB-first-across-word, nist_shr1 simplifies dramatically:                                               
  - "Shift NIST bits right by 1" = "shift HOL bits left by 1" = word_shl v 1 potentially with a mask.               
                                                                                                                    
  But wait — this is changing the meaning of nist_shr1 relative to NIST spec. The NIST spec actually says
  "right-shift the bit string," which in the MSB-first-within-byte encoding (= current code) doesn't map cleanly to 
  word_shl. In the MSB-first-across-word encoding, it would.      
                                                                                                                    
  This means the current code picks one specific encoding (MSB-first-within-byte) and the reviewer's suggestion     
  implicitly uses a different one (MSB-first-across-word).
                                                                                                                    
  Step 2: Update all Bridge A lemmas                                                                                
   
  Every lemma that references nist_bit, nist_lsb, nist_shr1, or bit_reverse_per_byte needs re-examination. Affected:
                                                                  
  - NIST_BIT_AS_NATURAL — either trivial or needs new proof                                                         
  - NIST_LSB_AS_NATURAL — similarly                               
  - BYTE_BITREV_GHASH_R — proves bit_reverse_per_byte 0xE1 = 0x87. Under new definition, need to check if           
  word_reversefields 1 (word 0xE1 : int128) = word 0x87 : int128. It's not: word_reversefields 1 (word 0xE1) puts   
  the bits of 0xE1 at HOL positions 120-127, giving 0x87 * 2^120, not 0x87. So this lemma would need a different    
  formulation or become false.                                                                                      
  - NIST_SHR1_BIT — needs new proof (maybe simpler)               
  - BYTE_BITREV_XOR — word_reversefields 1 distributes over XOR, so still holds                                     
  - NIST_SHR1_AS_SHL — needs re-derivation                                                                          
  - NIST_V_UPDATE_AS_POLY_SHL — maybe changes                                                                       
  - NIST_Z_UPDATE_AS_POLY_XOR — maybe changes                                                                       
  - NIST_LOOP_AS_POLY_LOOP — follows from the above                                                                 
  - BYTE_BITREV_ZERO — follows                                                                                      
  - NIST_GHASH_MUL_BYTREV_EQ_POLY_LOOP — follows                                                                    
                                                                                                                    
  Step 3: Bridge C's byte-reversal wrapper                                                                          
                                                                                                                    
  Currently:                                                                                                        
  gcm_gmult_spec xi h hhl = word_reversefields 8 (polyval_dot (word_reversefields 8 xi) H)
                                                                                                                    
  The word_reversefields 8 wrapper is there because gcm_gmult_spec is defined to mirror the assembly's output       
  byte-format. The assembly's REV64+EXT at the end of the routine genuinely produces a byte-reversed value. So this 
  wrapper is not about Bridge A's permutation — it's about the assembly's actual output format.                     
                                                                                                                    
  Whether it can be removed depends on whether we also change gcm_gmult_spec to not include the final               
  word_reversefields 8 phase2 step. But then gcm_gmult_spec no longer matches the assembly's output, and the earlier
   exec-correctness proof (GCM_GMULT_V8_EXEC_CORRECT) needs adjustment.                                             
                                                                  
  Step 4: The top-level composition                                                                                 
   
  The full chain is:                                                                                                
  1. GCM_GMULT_V8_EXEC_CORRECT: assembly computes gcm_gmult_spec xi h hhl.
  2. GCM_GMULT_SPEC_EQ_POLYVAL_DOT (Bridge C): gcm_gmult_spec xi h hhl = word_reversefields 8 (polyval_dot          
  (word_reversefields 8 xi) H).                                                                            
  3. GHASH_POLYVAL_BRIDGE (Bridge B): word_reversefields 1 (ghash_reduce ...) = ghash_twist(polyval_dot ...).       
  4. NIST_GHASH_EQ_GHASH_REDUCE (Bridge A): bit_reverse_per_byte(nist_ghash_mul ...) = ghash_reduce(pmul (brp x) 
  (brp y)).                                                                                                         
                                                                                                                    
  For the reviewer's proposal, the chain needs to compose with the same reversal at every junction. Currently it    
  uses a mix of bit_reverse_per_byte, word_reversefields 1, and word_reversefields 8 — three different reversals    
  that cancel out in specific ways.                               
                                                                                                                    
  Detailed refactor plan                                                                                            
   
  Phase 0: Preparation                                                                                              
                                                                  
  - Safety branch pr390-before-bridgeA-refactor already created.                                                    
  - Verify the user's intent: they want Option B2 (change NIST bit-numbering too), not just mechanical renaming.
                                                                                                                    
  Phase 1: Change NIST primitives                                                                                   
                                                                                                                    
  - Redefine nist_bit x i = bit (127 - i) x.                                                                        
  - Redefine nist_lsb v = bit 0 v.                                
  - Redefine nist_shr1 v in terms of the new bit numbering (probably word_shl v 1 with a mask, or equivalent).      
  - Redefine ghash_R value if needed (check if 0xE1 is still right under new encoding — probably not, might become  
  0x87 directly or word(2^127) XOR word(2^123) XOR ...).                                                            
                                                                                                                    
  Phase 2: Change bit_reverse_per_byte                                                                              
                                                                  
  - Rename to bit_reflect128 (unifying with ghash_nist_bridge.ml).                                                  
  - New definition: bit_reflect128 x = word_reversefields 1 x.    
  - All 32 references need updating.                                                                                
                                                                                                                    
  Phase 3: Re-prove lemmas                                                                                          
                                                                                                                    
  - NIST_BIT_AS_NATURAL: trivial now.                                                                               
  - NIST_LSB_AS_NATURAL: trivial.                                 
  - BYTE_BITREV_GHASH_R (rename to REFLECT_GHASH_R): state and prove the new identity. May need ghash_R to change   
  value.                                                                                                            
  - NIST_SHR1_BIT: re-prove in the new convention.                                                                  
  - BYTE_BITREV_XOR (rename to REFLECT_XOR): word_reversefields 1 distributes over XOR — should be easy.            
  - NIST_SHR1_AS_SHL: re-derive; likely simpler now.                                                                
  - NIST_V_UPDATE_AS_POLY_SHL: mechanical re-derivation.                                                            
  - NIST_Z_UPDATE_AS_POLY_XOR: mechanical re-derivation.                                                            
  - NIST_LOOP_AS_POLY_LOOP: follows.                                                                                
  - BYTE_BITREV_ZERO: follows.                                                                                      
  - NIST_GHASH_MUL_BYTREV_EQ_POLY_LOOP: follows.                                                                    
  - NIST_GHASH_EQ_GHASH_REDUCE (the new Bridge A): statement changes — now uses word_reversefields 1 instead of     
  bit_reverse_per_byte.                                                                                             
                                                                                                                    
  Phase 4: Bridge B consolidation                                                                                   
                                                                  
  - GHASH_POLYVAL_BRIDGE already uses word_reversefields 1 — no change needed.                                      
  - Possibly rename or consolidate with GUERON_PROP1 from ghash_nist_bridge.ml (same shape now).
                                                                                                                    
  Phase 5: Bridge C byte-reversal wrapper                                                                           
                                                                                                                    
  - Question: can GCM_GMULT_SPEC_EQ_POLYVAL_DOT's word_reversefields 8 wrapper go away?                             
  - Answer: NO, unless we change gcm_gmult_spec to stop including the final REV64+EXT step. That would:
    - Invalidate GCM_GMULT_V8_EXEC_CORRECT (the exec-correctness proof against the assembly).                       
    - Require changing the top-level theorem to include the byte-reversal outside gcm_gmult_spec.                   
  - This is actually a cosmetic relocation, not elimination. The reality is: the assembly byte-reverses at the end, 
  so some byte-reversal must appear somewhere in the chain.                                                         
                                                                                                                    
  Phase 6: Top-level composition theorem                                                                            
                                                                  
  - Compose all four bridges into a single ARM_GHASH_CORRECT theorem that says: "running the assembly on            
  memory-format inputs produces the memory-format result that NIST specifies."
  - This theorem will have exactly one word_reversefields 8 somewhere (modeling the memory format at the interface).
                                                                                                                    
  Phase 7: Verify it still builds                                                                                   
                                                                                                                    
  - Run HOL Light on the refactored file.                                                                           
  - Fix any proof-closing issues that arise.      

  DO NOT PUSH ANYTHING TO GITHUB!!
