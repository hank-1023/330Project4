open Sets
open Nfa

(*********)
(* Types *)
(*********)

type regexp_t =
  | Empty_String
  | Char of char
  | Union of regexp_t * regexp_t
  | Concat of regexp_t * regexp_t
  | Star of regexp_t

(*******************************)
(* Part 2: Regular Expressions *)
(*******************************)

let rec nfa_helper re i = match re with
                      | Empty_String -> {qs = [i]; sigma = []; delta = []; q0 = i; fs = [i]}
                      | Char c -> {qs = [i; i + 1]; sigma = [c]; delta = [(i, Some c, i + 1)]; q0 = i; fs = [i + 1]}
                      | Union (a, b) -> let r1 = nfa_helper a (i + 1) in
                                          let r2 = nfa_helper b (i + 1 + List.length r1.qs) in
                                          let final = i + List.length r1.qs + List.length r2.qs + 1 in
                                          {
                                            qs = (union r1.qs r2.qs) @ [i; final];
                                            sigma = union r1.sigma r2.sigma;
                                            delta = [(i, None, r1.q0); (i, None, r2.q0)] @ (union r1.delta r2.delta) @ 
                                              List.fold_left (fun a f -> insert (f, None, final) a) [] r1.fs @
                                              List.fold_left (fun a f -> insert (f, None, final) a) [] r2.fs;
                                            q0 = i;
                                            fs = [final];
                                          }
                      | Concat (a, b) -> let r1 = nfa_helper a i in
                                          let r2 = nfa_helper b (i + List.length r1.qs) in
                                           {
                                            qs = union r1.qs r2.qs;
                                            sigma = union r1.sigma r2.sigma;
                                            delta = (union r1.delta r2.delta) @
                                              List.fold_left (fun a f -> insert (f, None, r2.q0) a) [] r1.fs;
                                            q0 = r1.q0;
                                            fs = r2.fs;
                                           }
                      | Star a -> let r = nfa_helper a i in
                                  let be = ((List.length r.qs)+i) in
                                  let en = ((List.length r.qs)+i+1) in
                                    {
                                      qs = r.qs @ [be; en];
                                      sigma = r.sigma;
                                      delta = r.delta @ [(be, None, r.q0); (be, None, en); (en, None, be)] @ 
                                        List.fold_left (fun a f -> insert (f, None, en) a) [] r.fs;
                                      q0 = be;
                                      fs = [en];
                                    }

let regexp_to_nfa re = nfa_helper re 0

let rec regexp_to_string r = match r with
                        | Empty_String -> "E"
                        | Char c -> String.make 1 c
                        | Union (r1,r2) -> "(" ^ (regexp_to_string r1) ^ "|" ^ (regexp_to_string r2) ^ ")"
                        | Concat (r1,r2) -> "(" ^ (regexp_to_string r1)  ^ (regexp_to_string r2) ^ ")"
                        | Star  r1-> "(" ^ (regexp_to_string r1) ^ ")*"

(*****************************************************************)
(* Below this point is parser code that YOU DO NOT NEED TO TOUCH *)
(*****************************************************************)

exception IllegalExpression of string

(* Scanner *)
type token =
  | Tok_Char of char
  | Tok_Epsilon
  | Tok_Union
  | Tok_Star
  | Tok_LParen
  | Tok_RParen
  | Tok_END

let tokenize str =
  let re_var = Str.regexp "[a-z]" in
  let re_epsilon = Str.regexp "E" in
  let re_union = Str.regexp "|" in
  let re_star = Str.regexp "*" in
  let re_lparen = Str.regexp "(" in
  let re_rparen = Str.regexp ")" in
  let rec tok pos s =
    if pos >= String.length s then
      [Tok_END]
    else begin
      if (Str.string_match re_var s pos) then
        let token = Str.matched_string s in
        (Tok_Char token.[0])::(tok (pos+1) s)
      else if (Str.string_match re_epsilon s pos) then
        Tok_Epsilon::(tok (pos+1) s)
      else if (Str.string_match re_union s pos) then
        Tok_Union::(tok (pos+1) s)
      else if (Str.string_match re_star s pos) then
        Tok_Star::(tok (pos+1) s)
      else if (Str.string_match re_lparen s pos) then
        Tok_LParen::(tok (pos+1) s)
      else if (Str.string_match re_rparen s pos) then
        Tok_RParen::(tok (pos+1) s)
      else
        raise (IllegalExpression("tokenize: " ^ s))
    end
  in
  tok 0 str

let tok_to_str t = ( match t with
      Tok_Char v -> (Char.escaped v)
    | Tok_Epsilon -> "E"
    | Tok_Union -> "|"
    | Tok_Star ->  "*"
    | Tok_LParen -> "("
    | Tok_RParen -> ")"
    | Tok_END -> "END"
  )

(*
   S -> A Tok_Union S | A
   A -> B A | B
   B -> C Tok_Star | C
   C -> Tok_Char | Tok_Epsilon | Tok_LParen S Tok_RParen

   FIRST(S) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(A) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(B) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(C) = Tok_Char | Tok_Epsilon | Tok_LParen
 *)

let parse_regexp (l : token list) =
  let lookahead tok_list = match tok_list with
      [] -> raise (IllegalExpression "lookahead")
    | (h::t) -> (h,t)
  in

  let rec parse_S l =
    let (a1,l1) = parse_A l in
    let (t,n) = lookahead l1 in
    match t with
      Tok_Union -> (
        let (a2,l2) = (parse_S n) in
        (Union (a1,a2),l2)
      )
    | _ -> (a1,l1)

  and parse_A l =
    let (a1,l1) = parse_B l in
    let (t,n) = lookahead l1 in
    match t with
      Tok_Char c ->
      let (a2,l2) = (parse_A l1) in (Concat (a1,a2),l2)
    | Tok_Epsilon ->
      let (a2,l2) = (parse_A l1) in (Concat (a1,a2),l2)
    | Tok_LParen ->
      let (a2,l2) = (parse_A l1) in (Concat (a1,a2),l2)
    | _ -> (a1,l1)

  and parse_B l =
    let (a1,l1) = parse_C l in
    let (t,n) = lookahead l1 in
    match t with
      Tok_Star -> (Star a1,n)
    | _ -> (a1,l1)

  and parse_C l =
    let (t,n) = lookahead l in
    match t with
      Tok_Char c -> (Char c, n)
    | Tok_Epsilon -> (Empty_String, n)
    | Tok_LParen ->
      let (a1,l1) = parse_S n in
      let (t2,n2) = lookahead l1 in
      if (t2 = Tok_RParen) then
        (a1,n2)
      else
        raise (IllegalExpression "parse_C 1")
    | _ -> raise (IllegalExpression "parse_C 2")
  in
  let (rxp, toks) = parse_S l in
  match toks with
  | [Tok_END] -> rxp
  | _ -> raise (IllegalExpression "parse didn't consume all tokens")

let string_to_regexp str = parse_regexp @@ tokenize str

let string_to_nfa str = regexp_to_nfa @@ string_to_regexp str
