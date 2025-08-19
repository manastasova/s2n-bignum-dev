let KECCAK_SUBROUTINE_CORRECT = time prove
 (`forall rc_pointer:int64 pc:num stackpointer:int64 bitstate_in:int64 A returnaddress.
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH mlkem_keccak_f1600_x86_mc) (val  stackpointer, 264) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH mlkem_keccak_f1600_x86_mc) (val bitstate_in, 200) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH mlkem_keccak_f1600_x86_mc) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val rc_pointer,192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val stackpointer, 264) /\
  nonoverlapping_modulo (2 EXP 64) (val stackpointer, 264) (val rc_pointer,192)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_keccak_f1600_x86_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                read RSI s = rc_pointer /\
                C_ARGUMENTS [bitstate_in; rc_pointer] s /\
                wordlist_from_memory(rc_pointer,24) s = rc_table /\
                wordlist_from_memory(bitstate_in,25) s = A
                )
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                wordlist_from_memory(bitstate_in,25) s = keccak 24 A)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE KECCAK_NOIBT_SUBROUTINE_CORRECT));;
