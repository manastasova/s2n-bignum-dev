(* Store-based ct abbreviation for the 5-block single-binary branch.  Reads    *)
(* the actual keystream stored at out_ptr+offbytes (robust against the          *)
(* per-branch Q-register scramble) and abbreviates s13_N + ctN.  v3: if the     *)
(* stored value's keystream is still a raw register read, resolve it to that    *)
(* register's (expanded aese) value assumption.                                 *)
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
  let ks =
    if (try fst(dest_const(rator(rator ks0)))="read" with _->false)
    then (try tryfind (fun (_,th) -> let t=concl th in
                if is_eq t && lhs t = ks0 then rand t else fail()) asl
          with _ -> ks0)
    else ks0 in
  let s13n = mk_var("s13_"^string_of_int nidx,`:(128)word`) in
  let ptn = mk_var("pt"^string_of_int nidx,`:(128)word`) in
  let ctn = mk_var("ct"^string_of_int nidx,`:(128)word`) in
  (ABBREV_TAC(mk_eq(s13n,ks)) THEN
   ABBREV_TAC(mk_eq(ctn,
     list_mk_comb(`word_xor:(128)word->(128)word->(128)word`,
       [list_mk_comb(`word_xor:(128)word->(128)word->(128)word`,[ptn;s13n]); `rk14:(128)word`]))))
  (asl,w);;
