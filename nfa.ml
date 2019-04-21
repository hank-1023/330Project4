open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q
type ('q, 's) nfa_t = {
  qs : 'q list;
  sigma : 's list;
  delta : ('q, 's) transition list;
  q0 : 'q;
  fs : 'q list;
}

(*********************)
(* Utility Functions *)
(*********************)

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let rec fix comp f x0 =
  let next = f x0 in
  if comp x0 next then x0 else fix comp f next

(****************)
(* Part 1: NFAs *)
(****************)

let rec map f l = match l with
    [] -> []
  | (h::t) -> (f h)::(map f t)
;;

let rec fold f a l = match l with
    [] -> a
  | (h::t) -> fold f (f a h) t
;;

let move m qs s = let {delta = d} = m in
                  let rec delta_aux d' = match d' with
                                          | [] -> []
                                          | (n0, s', n1)::next -> fold (fun a h -> if (h = n0 && s != None && s' != None && s = s') then 
                                                                                    insert n1 a 
                                                                                  else 
                                                                                    a
                                                                        ) (delta_aux next) qs
                  in delta_aux d

let e_closure m qs = let {delta = d} = m in
                      let rec closure_aux d' q0 = match d' with
                                                  | [] -> []
                                                  |  (q1, s', q2)::next -> if (q0 = q1 && s' = None) then
                                                                            union (insert q2 (closure_aux d' q2)) (closure_aux next q0)
                                                                          else
                                                                            closure_aux next q0
                      in fold (fun a h -> union (insert h a) (closure_aux d h)) [] qs

let rec f_check qs fs = match qs with
                        | [] -> false
                        | h::t -> if elem h fs then true else f_check t fs

let accept m str = let {delta = delta; q0 = q0; fs = fs} = m in
                    if String.length str = 0 then 
                      let q0e = e_closure m (q0::[]) in
                      f_check q0e fs
                    else
                      let chars = explode str in
                      let rec accept_aux ch qs = 
                        match ch with
                        | [] -> f_check qs fs
                        | h::t -> accept_aux t (e_closure m (move m qs (Some h)))
                      in accept_aux chars (e_closure m [m.q0])

let nfa_to_dfa m = 
  let step q sym = fold (fun a q' -> insert (e_closure m (move m q (Some sym))) a) [] q in
  let step_symbol dfa q sym = 
                    let l = step q sym in
                      fold (fun dfa' q1 -> let {qs = qs; sigma = sigma; delta = delta; q0 = q0; fs = fs} = dfa' in
                          let qs' = insert q1 qs in
                          let delta' = insert (q, (Some sym), q1) delta in
                          let fs' = fold (fun a f' -> if elem f' m.fs then insert q1 a else a) fs q1 in
                        {qs = qs'; sigma = sigma; delta = delta'; q0 = q0; fs = fs'}) dfa l in
  let step_state dfa q = fold (fun dfa sym -> step_symbol dfa q sym) dfa dfa.sigma in
  let step_dfa dfa = fold (fun dfa q -> step_state dfa q) dfa dfa.qs in
  let q0' = e_closure m ((m.q0)::[]) in
  let qs' = [q0'] in
  let fs' = fold (fun a f -> if elem f m.fs then insert [f] a else a) [] q0' in
  let x = {qs = qs'; sigma = m.sigma; delta = []; q0 = q0'; fs = fs'} in
  fix (fun dfa1 dfa2 -> (eq dfa1.qs dfa2.qs) && (eq dfa1.delta dfa2.delta) && (eq dfa1.q0 dfa2.q0) && (eq dfa1.fs dfa2.fs)) step_dfa x
