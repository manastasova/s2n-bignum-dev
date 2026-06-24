#!/usr/bin/env python3
"""Generate combined AES-256-GCM ML: uniform 8-block precondition, abstract band
lemmas N=1..8 (from concrete _CONCRETE bands via the bridges), dispatch theorem.
The concrete bands LT_{N}BLOCK_CONCRETE and the spec/bridges must already be loaded."""

RKS = "[rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]"
RK_SPECL = ";".join(f"`rk{i}:(128)word`" for i in range(15))

# ---- uniform 8-block precondition (state predicate body), parameterized by nothing ----
def keys_reads(var="s"):
    out=[]
    for i in range(15):
        out.append(f"           read (memory :> bytes128 (word_add key_ptr (word {16*i}))) {var} = rk{i}")
    return " /\\\n".join(out)

PD="polyval_dot"
HTAB = {  # offset : rhs
 0:"byteswap128 h", 16:"h1k", 32:f"byteswap128 ({PD} h h)",
 48:f"byteswap128 ({PD} h ({PD} h h))", 64:"h3k",
 80:f"byteswap128 ({PD} ({PD} h h) ({PD} h h))",
 96:f"byteswap128 ({PD} ({PD} ({PD} h h) ({PD} h h)) h)", 112:"h5k",
 128:f"byteswap128 ({PD} ({PD} ({PD} ({PD} h h) ({PD} h h)) h) h)",
 144:f"byteswap128 ({PD} ({PD} ({PD} ({PD} ({PD} h h) ({PD} h h)) h) h) h)", 160:"h7k",
 176:f"byteswap128 ({PD} ({PD} ({PD} ({PD} ({PD} ({PD} h h) ({PD} h h)) h) h) h) h)",
}
KMS = [  # karatsuba_mid clauses
 ("h1k","(0,64)","karatsuba_mid h"),
 ("h1k","(64,64)",f"karatsuba_mid ({PD} h h)"),
 ("h3k","(0,64)",f"karatsuba_mid ({PD} h ({PD} h h))"),
 ("h3k","(64,64)",f"karatsuba_mid ({PD} ({PD} h h) ({PD} h h))"),
 ("h5k","(0,64)",f"karatsuba_mid ({PD} ({PD} ({PD} h h) ({PD} h h)) h)"),
 ("h5k","(64,64)",f"karatsuba_mid ({PD} ({PD} ({PD} ({PD} h h) ({PD} h h)) h) h)"),
 ("h7k","(0,64)",f"karatsuba_mid ({PD} ({PD} ({PD} ({PD} ({PD} h h) ({PD} h h)) h) h) h)"),
 ("h7k","(64,64)",f"karatsuba_mid ({PD} ({PD} ({PD} ({PD} ({PD} ({PD} h h) ({PD} h h)) h) h) h) h)"),
]

def htab_reads(var="s"):
    out=[]
    for off in sorted(HTAB):
        ptr = "htable_ptr" if off==0 else f"(word_add htable_ptr (word {off}))"
        out.append(f"           read (memory :> bytes128 {ptr}) {var} = {HTAB[off]}")
    return " /\\\n".join(out)

def km_clauses():
    return " /\\\n".join(f"           word_subword {v} {pos}:(64)word = {rhs}" for v,pos,rhs in KMS)

def pt_reads(var="s"):
    out=[f"           read (memory :> bytes128 in_ptr) {var} = pt1"]
    for k in range(1,8):
        out.append(f"           read (memory :> bytes128 (word_add in_ptr (word {16*k}))) {var} = pt{k+1}")
    return " /\\\n".join(out)

# nonoverlapping block (verbatim from gcm_8b_goal: 128-byte in/out)
NONOV = """    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\\
    nonoverlapping (stackptr,80) (out_ptr,128) /\\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\\
    nonoverlapping (stackptr,80) (in_ptr,128) /\\
    nonoverlapping (stackptr,80) (key_ptr,240) /\\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\\
    nonoverlapping (out_ptr,128) (word pc,4600)"""

FRAME = """      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
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
                  memory :> bytes64 (word_add stackptr (word 72))])"""

# The uniform precondition state (\s. ...) used by EVERY band lemma + the combined thm.
def precond_state(var="s"):
    return f"""(\\{var}. aligned_bytes_loaded {var} (word pc) aes256_gcm_mc /\\
           read PC {var} = word pc /\\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] {var} /\\
           read SP {var} = word_add stackptr (word 80) /\\
           read Q18 {var} = q18i /\\
           byte_list_at pt_in in_ptr (word 128) {var} /\\
           read (memory :> bytes128 out_ptr) {var} = co0 /\\
           read (memory :> bytes128 (word_add out_ptr (word 16))) {var} = co1 /\\
           read (memory :> bytes128 (word_add out_ptr (word 32))) {var} = co2 /\\
           read (memory :> bytes128 (word_add out_ptr (word 48))) {var} = co3 /\\
           read (memory :> bytes128 (word_add out_ptr (word 64))) {var} = co4 /\\
           read (memory :> bytes128 (word_add out_ptr (word 80))) {var} = co5 /\\
           read (memory :> bytes128 (word_add out_ptr (word 96))) {var} = co6 /\\
           read (memory :> bytes128 (word_add out_ptr (word 112))) {var} = co7 /\\
           read (memory :> bytes128 ivec_ptr) {var} = ivec /\\
{keys_reads(var)} /\\
           read (memory :> bytes128 xi_ptr) {var} = xi /\\
{htab_reads(var)} /\\
{km_clauses()})"""

# abstract postcond (uniform): conditional PC, X0=len, byte_list_at spec, gcm_final_xi
def postcond_state(var="s"):
    return f"""(\\{var}. read PC {var} = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\\
           read X0 {var} = len /\\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec {RKS})
                        out_ptr len {var} /\\
           read (memory :> bytes128 xi_ptr) {var} =
             gcm_final_xi (val len) pt_in ivec {RKS} xi h)"""

BINDERS = ("!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr "
  "(pt_in:byte list) "
  "(co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) "
  "(co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) "
  + " ".join(f"(rk{i}:(128)word)" for i in range(15)) + " "
  "(xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) "
  "(q18i:(128)word) (len:int64) stackptr pc.")

if __name__=="__main__":
    print("(* see emit functions *)")

# ---------------- per-band abstract lemma ----------------
# H-power VARIABLE args each concrete band takes (subset of h,h1k,h3k,h5k,h7k):
def hpow_args(N):
    a=["`h:(128)word`","`h1k:(128)word`"]
    if N>=3: a.append("`h3k:(128)word`")
    if N>=5: a.append("`h5k:(128)word`")
    if N>=7: a.append("`h7k:(128)word`")
    return a

def band_lemma(N):
    nf=N-1
    # concrete band ISPECL args: ptrs; pt1..ptN (=block 0..N-1); out0(=co{N-1}); ivec; rks; xi; hpows; [q18i if N==8]; byte_len; stackptr; pc
    pt_args=[f"`bytes_to_int128 (SUB_LIST({16*k},16) pt_in)`" for k in range(N)]
    args=(["`in_ptr:int64`","`out_ptr:int64`","`xi_ptr:int64`","`ivec_ptr:int64`","`key_ptr:int64`","`htable_ptr:int64`"]
          + pt_args + [f"`co{nf}:(128)word`","`ivec:(128)word`"]
          + [f"`rk{i}:(128)word`" for i in range(15)]
          + ["`xi:(128)word`"] + hpow_args(N)
          + (["`q18i:(128)word`"] if N==8 else [])
          + ["`byte_len:num`","`stackptr:int64`","`pc:num`"])
    ispecl=";\n    ".join(args)
    concrete = f"AES256_GCM_ENCRYPT_LT_{N}BLOCK_CONCRETE"
    # store-hyp branches for OUT_BRIDGE_GEN: nf full stores k=0..nf-1
    if nf==0:
        kbranch="GEN_TAC THEN REWRITE_TAC[ARITH_RULE `~(k < 0)`]"
    elif nf==1:
        kbranch=("X_GEN_TAC `k:num` THEN REWRITE_TAC[ARITH_RULE `k < 1 <=> k = 0`] THEN\n"
                 "          DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN\n"
                 "          REWRITE_TAC CTR_ITER_CLAUSES THEN REWRITE_TAC[WORD_ADD_0] THEN\n"
                 "          CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]")
    else:
        kcases=" \\/ ".join(f"k = {j}" for j in range(nf))
        kbranch=(f"X_GEN_TAC `k:num` THEN REWRITE_TAC[ARITH_RULE `k < {nf} <=> {kcases}`] THEN\n"
                 "          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN\n"
                 "          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN\n"
                 "          REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]")
    # C-arg bridge: band concrete C-arg is word(128*nf + 8*byte_len) (for nf=0 just word(8*byte_len));
    # goal C-arg is word(8*val len). For nf>=1 the literal 128*nf+8*byte_len matches 8*val len via SYM;
    # for nf=0 rewrite 8*byte_len -> 8*val len directly.
    if nf==0:
        cargbranch="SUBGOAL_THEN `8 * byte_len = 8 * val(len:int64)` SUBST1_TAC THENL\n         [ASM_ARITH_TAC; ALL_TAC]"
    else:
        cargbranch=(f"FIRST_ASSUM(fun th -> if concl th = `8 * val(len:int64) = {128*nf} + 8 * byte_len`\n"
                    f"                              then REWRITE_TAC[SYM th] else NO_TAC)")
    # input-block reads for pre-impl: k=0..N-1
    inconj=" /\\\n           ".join(
        f"read (memory :> bytes128 ({'in_ptr' if k==0 else f'word_add in_ptr (word {16*k})'})) x = bytes_to_int128 (SUB_LIST ({16*k},16) pt_in)"
        for k in range(N))
    inbranches=";\n            ".join(
        ("CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN\n" if k==0 else "CONV_TAC NUM_REDUCE_CONV THEN ") +
        f"            MATCH_MP_TAC INPUT_BLOCK_BL THEN EXISTS_TAC `8` THEN\n"
        f"            ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]"
        for k in range(N))
    ghash_thm=f"GHASH_BLOCKS_{N}"
    guard=f"{16*nf} + 1 <= val len /\\ val len <= {16*N}"
    lemma=f"""let AES256_GCM_ENCRYPT_LT_{N}BLOCK_ABS = prove(
 `{BINDERS}
    {guard} /\\ LENGTH pt_in = 128 /\\
    aligned 16 stackptr /\\
{NONOV}
    ==> ensures arm
      {precond_state("s")}
      {postcond_state("s")}
{FRAME}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(len:int64) = 0) /\\ val len = 16 * {nf} + (val len - {16*nf})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `byte_len = val(len:int64) - {16*nf}` THEN
  SUBGOAL_THEN `1 <= byte_len /\\ byte_len <= 16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if val(len:int64)=0 then 4596 else 4588) = 4588` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `8 * val(len:int64) = {128*nf} + 8 * byte_len` ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [{ispecl}]
   {concrete}) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST [ASM_ARITH_TAC; NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  DISCH_THEN(fun band ->
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `{('' if nf==0 else str(16*nf)+' + ')}byte_len = val(len:int64)` SUBST1_TAC THENL
         [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; REWRITE_TAC[WORD_VAL]];
        MATCH_MP_TAC OUT_BRIDGE_GEN THEN
        MAP_EVERY EXISTS_TAC [`{nf}`; `byte_len:num`; `co{nf}:(128)word`] THEN
        REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC;
          {kbranch};
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GCM_FINAL_XI_UNFOLD; ARITH_RULE `1 <= byte_len ==> ~(16 * {nf} + byte_len = 0)`] THEN
        MP_TAC(SPECL [`byte_len:num`;`pt_in:byte list`;`ivec:(128)word`;`{RKS}:int128 list`] {ghash_thm}) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[MAP] THEN REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES];
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        {cargbranch} THEN
        MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`x:armstate`] INPUT_READS_128) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;
"""
    return lemma

import sys
which = sys.argv[1] if len(sys.argv)>1 else "all"
if which=="bands":
    for N in range(2,9):
        print(band_lemma(N))
elif which.isdigit():
    print(band_lemma(int(which)))

def combined_theorem():
    # dispatch: nested ASM_CASES on val len at 16,32,...,112; bands 0,1,...,8
    # band guards: len=0 ->0blk; 1<=len<=16 ->1blk; 16(N-1)<len<=16N ->Nblk
    body=f"""let AES256_GCM_ENCRYPT_CORRECT = prove(
 `{BINDERS}
    val len <= 128 /\\ LENGTH pt_in = 128 /\\
    aligned 16 stackptr /\\
{NONOV}
    ==> ensures arm
      {precond_state("s")}
      {postcond_state("s")}
{FRAME}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `val(len:int64) = 0` THENL
   [MP_TAC AES256_GCM_ENCRYPT_LT_0BLOCK_ABS THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `val(len:int64) <= 16` THENL
   [MP_TAC AES256_GCM_ENCRYPT_LT_1BLOCK_ABS THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> 0 + 1 <= n`]; ALL_TAC] THEN"""
    for N in range(2,8):
        lo=16*(N-1); hi=16*N
        body+=f"""
  ASM_CASES_TAC `val(len:int64) <= {hi}` THENL
   [MP_TAC AES256_GCM_ENCRYPT_LT_{N}BLOCK_ABS THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN"""
    # last band 8: val len in (112,128]
    body+="""
  MP_TAC AES256_GCM_ENCRYPT_LT_8BLOCK_ABS THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
"""
    return body

if __name__=="__main__" and which=="combined":
    print(combined_theorem())

def ghash_blocks_lemma(N):
    nf=N-1
    full=[f"word_xor (bytes_to_int128 (SUB_LIST({16*k},16) pt_in)) (gcm_keystream {k} ivec rks)" for k in range(nf)]
    tail=f"word_and (word_xor (bytes_to_int128 (SUB_LIST({16*nf},16) pt_in)) (gcm_keystream {nf} ivec rks)) (word (2 EXP (8 * tail) - 1))"
    lst="[ "+";\n          ".join(full+[tail])+" ]"
    nums=" ".join("`%d`"%i for i in [7,6,5,4,3,2,1] if i<=nf and i>=1) or "`1`"
    # always include all num_CONV 1..7 (harmless)
    return f"""let GHASH_BLOCKS_{N} = prove(
  `!tail pt_in ivec rks. 1 <= tail /\\ tail <= 16
    ==> gcm_ghash_blocks (16 * {nf} + tail) pt_in ivec rks =
        {lst}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`{nf}`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;
"""

def band0_lemma():
    # abstract 0-block: val len = 0, early-exit pc+4596, frame [ABI,,PC], uniform precond.
    return f"""let AES256_GCM_ENCRYPT_LT_0BLOCK_ABS = prove(
 `{BINDERS}
    val (len:int64) = 0 /\\ LENGTH pt_in = 128 /\\
    aligned 16 stackptr /\\
{NONOV}
    ==> ensures arm
      {precond_state("s")}
      {postcond_state("s")}
{FRAME}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `len:int64 = word 0` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_0; aes256_gcm_encrypt; gcm_final_xi; byte_list_at; VAL_WORD_0;
              LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPECL
   [`in_ptr:int64`;`out_ptr:int64`;`xi_ptr:int64`;`ivec_ptr:int64`;`key_ptr:int64`;`htable_ptr:int64`;
    `co0:(128)word`;`xi:(128)word`;`stackptr:int64`;`pc:num`]
   AES256_GCM_ENCRYPT_LT_0BLOCK_CONCRETE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST [NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]]); ALL_TAC] THEN
  DISCH_THEN(fun band ->
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;
"""

def full_section():
    parts=["(* ===== N-block bridges already loaded from gcm_nblock_bridges content ===== *)"]
    parts.append("(* ===== GHASH_BLOCKS_2..8 ===== *)")
    for N in range(1,9): parts.append(ghash_blocks_lemma(N))
    parts.append("(* ===== abstract band lemmas 0,1,2..8 ===== *)")
    parts.append(band0_lemma())
    for N in range(1,9): parts.append(band_lemma(N))
    parts.append("(* ===== combined dispatch ===== *)")
    parts.append(combined_theorem())
    return "\n\n".join(parts)
