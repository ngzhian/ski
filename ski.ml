(* set to true to output debug information *)
let debug = ref false

type name = string
type lambda =
  | Var of name
  | App of lambda * lambda
  | Abs of name * lambda

(* the SKI AST *)
type ski =
  | I
  | K
  | S
  | T of ski * ski

(* pretty print *)
let rec string_of_ski = function
  | I -> "I"
  | K -> "K"
  | S -> "S"
  | T (x, y) -> "T(" ^ (string_of_ski x) ^ "," ^ (string_of_ski y) ^ ")"

(* Rules for SKI calculus *)
(* I x     = x            *)
(* K x y   = x            *)
(* S x y z = x z (y z)    *)

let rec interp c =
  if !debug then print_endline ("pre: " ^ (string_of_ski c));
  match c with
  (* leaf node, remain unchanged *)
  | I | K | S              -> c
  (* an I term, reduce argument *)
  | T (I, x)               -> interp x
  (* a K term, reduce first argument *)
  | T (T (K, x), y)        -> interp x
  (* an S term, perform substitution *)
  | T (T (T (S, x), y), z) ->
    interp (T (T (x, z), T (y, z)))
  (* any other term *)
  (* the goal here is to check if terms are reducible *)
  (* to prevent infinite recursion   *)
  | T (c1, c2)             ->
    let c1' = interp c1 in
    let c2' = interp c2 in
    if c1 = c1' && c2 = c2'
    then T (c1, c2)
    else interp (T (c1', c2'))

type step =
  (* able to perform next step with term and current stack *)
  | Step of (ski * ski list)
  (* no reduction possible anymore *)
  | End of ski

let step term stack =
  match (term, stack) with
  (* I term, work on the top term in the stack *)
  | I, x::s -> Step(x , s)
  (* K term, work on the top term, discard the second *)
  | K, x::y::s -> Step(x, s)
  (* works on the substituted term *)
  | S, x::y::z::s ->
    Step(T (T (x, z), T(y, z)), s)
  (* push the second pargument onto the stack *)
  | T (c1, c2), s -> Step(c1, c2 :: s)
  (* empty stack, return as the result of reduction *)
  | e, [] -> End e
  (* no idea how to handle this *)
  | _ -> failwith "Unrecognized term"


let pr term stack =
  let _ = print_endline ("term: " ^ (string_of_ski term)) in
  let _ = print_endline ("stack: [" ^ (String.concat ", " (List.map string_of_ski stack)) ^ "]") in
  ()

let rec run term =
  let rec go term stack =
    if !debug then pr term stack;
    match step term stack with
    | End e -> print_endline ("end: " ^ (string_of_ski e)); e
    | Step(e, s') -> go e s';
  in
  go term []

(* examples from the blog post *)
let eg1 = T (I, I)
let eg2 = T (T (K, K), I)
let eg3 = T (T (T (S, K), S), K)

(* running examples on interpreter *)
(* helper to print interpreter result *)
let pr_interp t c = t ^ ": " ^ (string_of_ski (interp c))
let _ = print_endline (pr_interp "eg1" eg1) (* should be I *)
let _ = print_endline (pr_interp "eg2" eg2) (* should be K *)
let _ = print_endline (pr_interp "eg3" eg3) (* should be K *)

(* running examples on stack machine *)
let _ = run eg1 (* should be I *)
let _ = run eg2 (* should be K *)
let _ = run eg2 (* should be K *)

(* WIP *)
(* boolean logic in SKI combinator calculus *)
(* let z = s k s k *)
let t1 = T (T (K, T(T(K, I), I)), I)
(* K (K I I) I
 * K I I
 * *)
let t = K
let f = T (S, K)
    (* T (T (T (S, K), S), K) *)
let ifte b t e = T (T (b, t), e)
(* let nt = T(f, t) *)
let nt = function
  | K -> T (T (K, f), t)
  | T (S, K) -> T (T (T (S, K), T (S, K)), K)
  | _ -> failwith "not a boolean"
(* (SK) (SK) (K) (T) (F) *)
let t2 = ifte t (I) (K)
let t3 = ifte f (I) (K)
let t4 = ifte (nt t) (I) (K)
(*                       F           T *)
let t5 = ifte (T (T (f, (T (S, K))), K)) (I) (K)
(* let t5 = T (f, nt) *)
(* let t5 = T ((T(f, f), t)) *)
(* let _ = print_endline (pr_interp "t1" t1) (1* should be I *1) *)
(* let _ = print_endline (pr_interp "t2" t2) (1* should be I *1) *)
(* let _ = print_endline (pr_interp "t3" t3) (1* should be K *1) *)
(* let _ = print_endline (pr_interp "t4" t4) (1* should be k *1) *)
(* let _ = print_endline (pr_interp "t5" t5) (1* should be I *1) *)
