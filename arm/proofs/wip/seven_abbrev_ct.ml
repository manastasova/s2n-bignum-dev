(* Store-based ct abbreviation, v4: recursively chase register-read keystreams *)
(* to their fully-expanded aese form before abbreviating.  Fixes the 7-block    *)
(* case where the stored keystream resolves through a chain of register reads.  *)
let abbrev_ct_from_store offbytes nidx : tactic = fun (asl,w) ->
  let lhspat =
    if offbytes=0 then `read (memory :> bytes128 out_ptr) (s:armstate)`
    else vsubst [mk_small_numeral offbytes, `Z:num`]
           `read (memory :> bytes128 (word_add out_ptr (word Z))) (s:armstate)` in
  let store = tryfind (fun (_,th) -> let t=concl th in
    if is_eq t && (can (term_match [] lhspat) (lhs t)) &&
       (try fst(dest_const(repeat rator (rand t)))="word_xor" with _->false)
    then t else fail()) asl in
  let ks0 = rand(lhand(rand store)) in
  let is_read t = (try fst(dest_const(rator(rator t)))="read" with _->false) in
  (* recursively resolve a register-read term to its defining RHS until it is
     no longer a bare register read (i.e., the aese keystream). *)
  let rec resolve t depth =
    if depth <= 0 then t
    else if is_read t then
      (try let v = tryfind (fun (_,th) -> let c=concl th in
             if is_eq c && lhs c = t && not(rhs c = t) then rhs c else fail()) asl in
           if v = t then t else resolve v (depth-1)
       with _ -> t)
    else t in
  let ks = resolve ks0 8 in
  let s13n = mk_var("s13_"^string_of_int nidx,`:(128)word`) in
  let ptn = mk_var("pt"^string_of_int nidx,`:(128)word`) in
  let ctn = mk_var("ct"^string_of_int nidx,`:(128)word`) in
  (ABBREV_TAC(mk_eq(s13n,ks)) THEN
   ABBREV_TAC(mk_eq(ctn,
     list_mk_comb(`word_xor:(128)word->(128)word->(128)word`,
       [list_mk_comb(`word_xor:(128)word->(128)word->(128)word`,[ptn;s13n]); `rk14:(128)word`]))))
  (asl,w);;
