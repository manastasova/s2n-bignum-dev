(* ========================================================================= *)
(* DEAD CODE removed from arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml      *)
(* (2026-06-05). Verified unused by the 7 canonical N-block proofs AND every *)
(* other file in the tree (refs were self-references within the subsystem,   *)
(* comments, or .md docs). ARCHIVE ONLY -- not loaded by anything.            *)
(* ========================================================================= *)


(* ----- removed segment: original lines 228-239 -----
   N=1 vestigial: GHASH_NBLOCK_KARATSUBA_1 (recovers ghash_1block_karatsuba from the generic framework at N=1; never used in a proof) *)

(* The 1-block instance recovers the existing `ghash_1block_karatsuba`. *)
let GHASH_NBLOCK_KARATSUBA_1 = prove
 (`!(input:int128) (h_tw:int128) (hk:int128).
    ghash_Nblock_karatsuba [(input, h_tw, hk)] =
    ghash_1block_karatsuba input h_tw hk`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ghash_Nblock_karatsuba; ghash_1block_karatsuba;
              kara_acc; karatsuba_block_pl; karatsuba_block_ph;
              karatsuba_block_pm; karatsuba_reduce_shared;
              LET_DEF; LET_END_DEF; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[]);;


(* ----- removed segment: original lines 518-545 -----
   N=1 vestigial chain: GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_DOT_1 + GHASH_NBLOCK_INDUCTIVE_1 (sanity N=1 instances of the bridge; never used) *)

(* ------------------------------------------------------------------------- *)
(* Per-N specializations of the inductive bridge.                             *)
(*                                                                           *)
(* For N=1: ghash_Nblock_karatsuba [(b1, byteswap128 h, hk)] =                 *)
(*          word_reversefields 8 (polyval_dot b1 h)                          *)
(* Recovered from existing 1-block bridge.                                    *)
(* ------------------------------------------------------------------------- *)
let GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_DOT_1 = prove
 (`!(input:int128) (h:int128) (hk:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h
    ==> ghash_Nblock_karatsuba [(input, byteswap128 h, hk)] =
        word_reversefields 8 (polyval_dot input h)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GHASH_NBLOCK_KARATSUBA_1] THEN
  ASM_SIMP_TAC[GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT]);;

(* For N=1 via the inductive bridge: ghash_Nblock_karatsuba [(b1,htw,hk)] =
   word_reversefields 8 (polyval_reduce_prop3 (pmul b1 h)) = word_reversefields 8 (polyval_dot b1 h).
   This is consistent with the existing 1-block bridge — both prove the same equation. *)
let GHASH_NBLOCK_INDUCTIVE_1 = prove
 (`!(input:int128) (h:int128) (hk:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h
    ==> ghash_Nblock_karatsuba (project_triples [input,byteswap128 h,hk,h]) =
        word_reversefields 8 (polyval_dot input h)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `[(input:int128, byteswap128 h:int128, hk:int128, h:int128)]:(int128#int128#int128#int128)list` GHASH_NBLOCK_KARATSUBA_EQ_PROP3) THEN
  REWRITE_TAC[kara_quad_ok; kara_quad_pmul; WORD_XOR_0_LEFT] THEN
  ASM_REWRITE_TAC[polyval_dot]);;


(* ----- removed segment: original lines 721-910 -----
   Generic/parameterized GHASH-tactic subsystem: GCM_NBLOCK_GHASH_PRE_BRIDGE_TAC, _ATOMIC_ABBREVS, _PMUL_ABBREVS, _Z_ABBREVS, _FINAL_TAC, mk_atom_name, GCM_NBLOCK_GHASH_STEP_GENERATOR, GCM_NBLOCK_GHASH_STEP_TAC (abandoned generic closer; each per-N file hand-writes its own GCM_kBLOCK_GHASH_STEP_TAC) *)

(* ========================================================================= *)
(* PARAMETERIZED GHASH STEP TACTIC                                            *)
(*                                                                           *)
(* GCM_NBLOCK_GHASH_STEP_TAC : int -> tactic                                 *)
(*                                                                           *)
(* Generates the closure recipe for the N-block GHASH equation.              *)
(* Atoms scale linearly with N:                                               *)
(*   - 2 input atoms per block (uA0_k, uA1_k for k=1..N) = 2N                *)
(*   - 2 H-power atoms per distinct H power (uD0/uD1 for h^1,                *)
(*     uE0/uE1 for h^2, etc.) = 2N for N distinct powers                      *)
(*   - 3 inner pmul atoms per block (p1_k, p2_k, p3_k) = 3N                  *)
(*   - 2 z-vars per inner pmul (lo and hi subwords) = 6N                     *)
(*   - 1 z-var for the small outer pmul subword                              *)
(*   - 2 outer abbrev (qBigP and qSmallP) + 3 subword extractions             *)
(*                                                                           *)
(* Helper functions to build the right names:                                 *)
(* ========================================================================= *)

(* Helper: generate ABBREV_TAC's for the 4 atomic input/H subwords for N=1.  *)
(* These functions are EXPLICITLY built per N in the actual *_nblock.ml      *)
(* file's tactic definition, because each N has block-specific input names   *)
(* (xi/ct for N=1, xi/ct1/ct2 for N=2, etc.) and H-power binding names.       *)
(*                                                                           *)
(* The generic skeleton is captured in GCM_NBLOCK_GHASH_PRE_BRIDGE_TAC and   *)
(* GCM_NBLOCK_GHASH_POST_BRIDGE_TAC below. The bridge application itself     *)
(* differs only in WHICH per-N theorem is invoked                              *)
(* (GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_DOT_1 for N=1, the corresponding         *)
(* derived theorem for N≥2). *)

(* GCM_NBLOCK_GHASH_PRE_BRIDGE_TAC: the standard pre-bridge normalization
   chain (subword/halfswap/PMUL_NORM/karatsuba_mid). This is identical
   across all N. *)
let GCM_NBLOCK_GHASH_PRE_BRIDGE_TAC =
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word`
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_1; WORD_INSERT_AS_JOIN_2;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO;
              REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[karatsuba_mid];;

(* GCM_NBLOCK_GHASH_ATOMIC_ABBREVS n input_atoms h_atoms : tactic
   Generates ABBREV_TAC for each (var_name, term) pair in the input/H lists. *)
let GCM_NBLOCK_GHASH_ATOMIC_ABBREVS (atoms : (string * term) list) : tactic =
  let abbrevs = List.map (fun (name, body) ->
    let v = mk_var(name, type_of body) in
    ABBREV_TAC(mk_eq(v, body))) atoms in
  EVERY abbrevs;;

(* GCM_NBLOCK_GHASH_PMUL_ABBREVS pmul_specs : tactic
   pmul_specs = [(name, arg1_term, arg2_term)] where each pmul is `word_pmul arg1 arg2 :(128)word`.
   Generates ABBREV_TAC for each. *)
let GCM_NBLOCK_GHASH_PMUL_ABBREVS (pmul_specs : (string * term * term) list) : tactic =
  let abbrevs = List.map (fun (name, a, b) ->
    let body = mk_comb(mk_comb(`word_pmul:64 word -> 64 word -> 128 word`, a), b) in
    let v = mk_var(name, `:(128)word`) in
    ABBREV_TAC(mk_eq(v, body))) pmul_specs in
  EVERY abbrevs;;

(* GCM_NBLOCK_GHASH_Z_ABBREVS z_specs : tactic
   z_specs = [(name, body, (offset, length))] for word_subword extractions.
   Generates ABBREV_TAC `(name:(64)word) = word_subword body (offset,length)` *)
let GCM_NBLOCK_GHASH_Z_ABBREVS (z_specs : (string * term * (int*int)) list) : tactic =
  let abbrevs = List.map (fun (name, body, (off, len)) ->
    let off_tm = mk_small_numeral off
    and len_tm = mk_small_numeral len in
    let pair = mk_pair (off_tm, len_tm) in
    let subword_tm =
      mk_comb(mk_comb(`word_subword:128 word -> num#num -> 64 word`, body), pair) in
    let v = mk_var(name, `:(64)word`) in
    ABBREV_TAC(mk_eq(v, subword_tm))) z_specs in
  EVERY abbrevs;;

(* GCM_NBLOCK_GHASH_FINAL_TAC : tactic
   The final closure: BINOP_TAC THENL [WORD_RULE; WORD_RULE].
   Identical across all N. *)
let GCM_NBLOCK_GHASH_FINAL_TAC =
  BINOP_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE];;

(* mk_atom_name n k base : build atom variable name with block index *)
let mk_atom_name (n:int) (k:int) (base:string) : string =
  if n = 1 then base else base ^ "_" ^ string_of_int k;;

(* GCM_NBLOCK_GHASH_STEP_GENERATOR n input_terms h_powers_terms hk_term :
                                              the parts of the GHASH closure
                                              that scale linearly with N.

   The generator returns a TACTIC that does:
     1. ABBREV uA0_k, uA1_k for each block input k=1..N
     2. ABBREV uD_lo_j, uD_hi_j for each H power j=1..N
     3. SUBGOAL_THEN to normalize XOR-AC of small pmul args
     4. ABBREV inner pmuls p1_k, p2_k, p3_k for each block
     5. REWRITE DOUBLE_SUBWORD_JOIN
     6. ABBREV z-vars for each inner pmul subword + the small outer pmul subword
     7. ASM_REWRITE
     8. SUBGOAL_THEN equating BIG outer pmul forms via XOR-AC
     9. ASM_REWRITE
    10. ABBREV qBigP, qSmallP, qBigPL, qBigPH, qSmallPH
    11. BINOP_TAC THENL [WORD_RULE; WORD_RULE]

   Inputs:
     n                    : block count (1..8)
     input_terms          : list [t_1; ...; t_N] of input cleartext-XOR terms
                            for each block (term type `:(128)word`).
                            For N=1: [`word_xor xi ct`].
                            For N=2: [`word_xor xi ct1`; `ct2`].
     h_powers_terms       : list of distinct H-power terms (length N).
                            For N=1: [`h:(128)word`].
                            For N=2: [`h:(128)word`; `polyval_dot h h`].
     hk_terms             : list [`h1k:(128)word`; ...] of Htable hk values
                            paired with each h power (one per block).

   This is a SKETCH generator. The actual closing of the BIG pmul SUBGOAL_THEN
   requires the precise atom list for that N — which depends on the specific
   shape produced by GHASH_POLYVAL_ACC_<N> + bridge unfolding. The N=1 case
   has the simple `xor z2 (xor z5 (xor z3 (xor z1 zD)))` form, but N≥2 cases
   have additional cross-block atoms. The generator builds the linear
   abbreviations; the BIG pmul SUBGOAL_THEN must be supplied per N.
*)
let GCM_NBLOCK_GHASH_STEP_GENERATOR (n:int)
                                    (input_terms : term list)
                                    (h_powers_terms : term list)
                                    (hk_terms : term list) : tactic =
  if List.length input_terms <> n then
    failwith ("GCM_NBLOCK_GHASH_STEP_GENERATOR: expected " ^ string_of_int n ^
              " input terms but got " ^ string_of_int (List.length input_terms))
  else if List.length h_powers_terms <> n then
    failwith ("GCM_NBLOCK_GHASH_STEP_GENERATOR: expected " ^ string_of_int n ^
              " H-power terms but got " ^ string_of_int (List.length h_powers_terms))
  else
  (* Build atomic ABBREVs: 2 per block input, 2 per H-power. *)
  let rfields_8 = `word_reversefields 8 :(128)word -> (128)word` in
  let mk_subword body off =
    let off_tm = mk_small_numeral off in
    let pair = mk_pair (off_tm, `64`) in
    mk_comb(mk_comb(`word_subword:128 word -> num#num -> 64 word`, body), pair) in
  let input_atoms = List.concat (List.mapi (fun i t ->
    let k = i + 1 in
    let body = mk_comb(rfields_8, t) in
    [(mk_atom_name n k "uA0", mk_subword body 0);
     (mk_atom_name n k "uA1", mk_subword body 64)]) input_terms) in
  let h_letters = ["uD"; "uE"; "uF"; "uG"; "uH"; "uI"; "uJ"; "uK"] in
  let h_atoms = List.concat (List.mapi (fun i t ->
    let prefix = List.nth h_letters i in
    [(prefix ^ "0", mk_subword t 0);
     (prefix ^ "1", mk_subword t 64)]) h_powers_terms) in
  GCM_NBLOCK_GHASH_ATOMIC_ABBREVS (input_atoms @ h_atoms);;

(* GCM_NBLOCK_GHASH_STEP_TAC : int -> tactic                                  *)
(* For now, a thin wrapper that builds the atomic ABBREVs and leaves the    *)
(* user to apply the rest of the recipe. The full closure for each N is     *)
(* encoded in the per-N proof file; this generator handles the mechanical    *)
(* atomic-naming portion which scales linearly. Future enhancement: extend  *)
(* to drive the entire closure including the BIG pmul SUBGOAL_THEN.          *)
let GCM_NBLOCK_GHASH_STEP_TAC (n:int) : tactic =
  match n with
  | 1 ->
      (* For N=1: input = `word_xor xi ct`, h_power = `h`, hk = `h1k`. *)
      GCM_NBLOCK_GHASH_PRE_BRIDGE_TAC THEN
      GCM_NBLOCK_GHASH_STEP_GENERATOR 1
        [`word_xor (xi:(128)word) ct`]
        [`h:(128)word`]
        [`h1k:(128)word`]
  | 2 ->
      (* For N=2: inputs = [xor xi ct1; ct2], h_powers = [h, polyval_dot h h]. *)
      GCM_NBLOCK_GHASH_PRE_BRIDGE_TAC THEN
      GCM_NBLOCK_GHASH_STEP_GENERATOR 2
        [`word_xor (xi:(128)word) ct1`; `ct2:(128)word`]
        [`h:(128)word`; `polyval_dot (h:(128)word) h`]
        [`h1k:(128)word`; `h1k:(128)word`]
  | _ -> failwith ("GCM_NBLOCK_GHASH_STEP_TAC: N=" ^ string_of_int n ^
                   " not yet supported (only N=1, 2 wired up; extend " ^
                   "this generator for N=3..8 by adding the per-N input/H-power lists)");;


(* ----- removed orphan banner (described the removed generic GHASH subsystem) -----
   This comment block sat just before the generic-tactic subsystem and is now stale. *)

(* ========================================================================= *)
(* GENERIC GHASH STEP TACTIC: GCM_NBLOCK_GHASH_STEP_TAC                      *)
(*  ... (full banner archived; described the parameterized closer recipe) ... *)
(* ========================================================================= *)
