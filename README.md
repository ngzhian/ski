An experiment in SKI combinator calculus, below are the accompanying blog posts,
originally on [my blog](https://blog.ngzhian.com):

1. [SKI combinators - AST and Evaluating](https://blog.ngzhian.com/ski.html)
2. [SKI combinators - Lambda to SKI](https://blog.ngzhian.com/ski2.html)

---

# SKI combinators - AST and Evaluating

S, K, and I are the name of three combinators.
Perhaps surprisingly, these combinators together is sufficient to
form a Turing-complete language [^1],
albeit very tedious to write.
Any expression in lambda calculus can be translated into the SKI combinator calculus via
a process called *abstraction elimination*, and that is what this post will be exploring.

[^1]: Wikipedia [Combinatory Logic](https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis)

## The SKI combinators

Combinators are functions without free variables, for example, in pseudo-Haskell syntax:
`id x = x` is a combinator that returns it's argument unchanged.
And here is what the SKI combinators do:

```
I x     = x
K x y   = x
S x y z = x z (y z)
```

I is the identity function, K behaves like a two argument identity function, returning
the first argument passed to it, S performs substitution (function application).
Here are some examples:

```
I I = I
K K I = K
S K S K = K K (S K) = K
```

## SKI abstract syntax tree

To be more precise, the SKI combinator calculus is made up of terms:
1. S, K, and I are terms
2. `(x y)` are terms if `x` and `y` are terms

Thus an expression in the SKI system can be visualized as a binary tree,
each leaf node being S, K, or I, and an inner node representing the parentheses.

Let's define an abstract syntax tree for an SKI expression like so:


```ocaml
type ski =
  | I
  | K
  | S
  | T of ski * ski
```

Thus the terms used in the examples above can be constructed as such:

```ocaml
T (I, I)               (* I I     *)
T (T (K, K), I)        (* K K I   *)
T (T (T (S, K), S), K) (* S K S K *)
```

With the abstract syntax tree, we can now try to reduce or interpret the SKI expressions.
We will be looking at two different ways of doing so, the first is by
interpreting recursively, the second is by running it as a stack machine.

## Interpreting

We interpret expressions by pattern matching on the structure of the abstract syntax tree:

```ocaml
let rec interp c =
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
```

## Stack machine

The idea for a stack machine based reduction of the SKI calculus is from [^2]

[^2]:http://yager.io/HaSKI/HaSKI.html

First we define a step function for the machine,
which works on the current term, and updates the stack based on the calculus rules.

```ocaml
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
```

Then a full run of an expression will be running the step function until we hit the end:

```ocaml
let run term =
  let rec go term stack =
    match step term stack with
    | End e -> e
    | Step (e, s') -> go e s'
  in
  go term []
```

Next up: translating terms in lambda calculus to SKI combinators.

## References

1. Wikipedia [SKI Combinator calculus](https://en.wikipedia.org/wiki/SKI_combinator_calculus)
2. Wikipedia [Combinatory Logic](https://en.wikipedia.org/wiki/Combinatory_logic)
3. [The SKI Combinator Calculus a universal formal system](http://people.cs.uchicago.edu/~odonnell/Teacher/Lectures/Formal_Organization_of_Knowledge/Examples/combinator_calculus/)
4. [eperdew's implementation in OCaml](https://github.com/eperdew/SKI/)
5. [bmjames' implementation in Erlang](https://gist.github.com/bmjames/745291/ab52ffdf8230bbec9bcf1059825ad6d3fd7186f5)
6. [yager's implementation in Haskell](http://yager.io/HaSKI/HaSKI.html)
7. [ac1235's implementation in Haskell's happy](https://github.com/ac1235/ski-combinator-calculus/blob/master/ski.y)

---

# SKI combinators - Lambda to SKI

In a [previous post](./ski.html),
we looked at what SKI combinators are, and how to encode and interpret them.
We also mentioned that these 3 combinators form a Turing-complete language,
because every lambda calculus term can be translated into an SKI combinator term.

> Source code is available [here](https://github.com/ngzhian/ski)

## Lambda Calculus

The [lambda calculus](https://en.wikipedia.org/wiki/Lambda_calculus)
is a simple Turing-complete language.

[^1]: Wikipedia [Combinatory Logic](https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis)


Lambda calculus is made up of three terms:

1. Variable, such as `x`,
2. Lambda abstraction, such as `fun x -> x`,
3. Application, such as `(y x)`.

```ocaml
(* lambda calculus AST *)
type name = string
type lambda =
  | Var of name
  | App of lambda * lambda
  | Abs of name * lambda
```

Here's an example lambda term,
representing the application of an identity function to an identity function:

```ocaml
App (Abs ('x', Var 'x'), Abs ('y', Var 'y'))
```

## Translating lambda to SKI

Let us conjure an ideal function that will do such a translation,
it should take a lambda term to an SKI term:

```ocaml
let convert (e : lambda) : ski = (??)
```

What this means is that we can either have a lambda term, or an ski term, with no in-betweens,
i.e. we cannot have a lambda term containing an ski term.

However, if we look at the translation rules,
we find that we will need a intermediate structure that can hold both lambda terms
and ski terms.

For example in clause 5, `T[λx.λy.E] => T[λx.T[λy.E]]`,
the translated term `T[λy.E]`, which by definition is an SKI term,
is the body of a lambda abstraction.

So it is helpful to define such a structure,
which allows lambda calculus terms and SKI terms to coexist:

```ocaml
(* Intermediate AST for converting lambda calculus into SKI combinators.
 * This is needed because when converting, intermediate terms can be
 * a mixture of both lambda terms and SKI terms, for example
 * a lambda expression with a SKI body, \x . K
 * *)
type ls =
  | Var of name
  | App of ls * ls
  | Abs of name * ls
  | Sl
  | Kl
  | Il
  | Tl of ls * ls
```

We will also need a helper function to determine if a variable is free in an expression:

```ocaml
(* Is n free in the expression e? *)
let free n (e : ls) =
  (* Get free variables of an expression *)
  let rec fv (e : ls) = match e with
    | Var n -> [n]
    | App (e1, e2) -> fv e1 @ fv e2
    | Abs (n, e) -> List.filter (fun x -> x != n) (fv e)
    | Tl (e1, e2) -> fv e1 @ fv e2
    | _ -> []
  in
  List.mem n (fv e)
```

The core translation algorithm then follows the translation scheme
described in the
[Wikipedia article](https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis).
We make use of the intermediate structure, `ls`, when translating.
The signature of this structure doesn't say much, it looks like an identity function,
but the assumption is that the input term is converted from a lambda term,
made up of `Var`, `App`, and `Abs`, and the output term will only contain
`Sl`, `Kl`, `Il`, and `Tl`, i.e. the terms that can be converted
directly into the SKI combinators.

```ocaml
(* This is the core algorithm to translate ls terms (made up of lambda)
 * into ls terms (made up of SKI combinators).
 * The clauses described here follows the rules of the T function described at
 * https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis
 * *)
let rec translate (e : ls) : ls = match e with
  (* clause 1. *)
  | Var x ->
    Var x
  (* clause 2. *)
  | App (e1, e2) ->
    App (translate e1, translate e2)
  (* clause 3. *)
  | Abs (x, e) when not (free x e) ->
    App (Kl, translate e)
  (* clause 4. *)
  | Abs (n, Var n') ->
    (* lambda x : x becomes identity *)
    if n = n'
    then Il
    else failwith "error"
  (* clause 5. *)
  | Abs (x, Abs (y, e)) ->
    if free x e
    then translate (Abs (x, translate (Abs (y, e))))
    else failwith "error"
  (* clause 6. *)
  | Abs (x, App (e1, e2)) ->
    if free x e1 || free x e2
    (* then App (Sl, App (translate (Abs (x, e1)), translate (Abs (x, e2)))) *)
    then App (App (Sl, (translate (Abs (x, e1)))), translate (Abs (x, e2)))
    else failwith "error"
  | Kl -> Kl
  | Sl -> Sl
  | Il -> Il
  | _ ->
    failwith "no matches"
```

Finally we can write the top level `convert` function we imagined earlier:

```ocaml
(* Converts a lambda term into an SKI term *)
let convert (e : lambda) : ski =
  (* Convert lambda term into intermediate ls term *)
  let rec ls_of_lambda (e : lambda) =
    match e with
    | Var x -> Var x
    | App (e1, e2) -> App (ls_of_lambda e1, ls_of_lambda e2)
    | Abs (x, e) -> Abs (x, ls_of_lambda e)
  in
  (* Convert intermediate ls term into ski term *)
  let rec ski_of_ls (e : ls) : ski =
    match e with
    | Var _ -> failwith "should not have Var anymore"
    | Abs _ -> failwith "should not have Abs anymore"
    | App (e1, e2) -> T (ski_of_ls e1, ski_of_ls e2)
    | Sl  -> S
    | Kl  -> K
    | Il  -> I
    | Tl (e1, e2) -> T (ski_of_ls e1, ski_of_ls e2)
  in
  (* convert lambda term into ls term *)
  let ls_term = ls_of_lambda e in
  (* translate ls term of lambda into ls term of combinators *)
  let ls_comb = translate ls_term in
  (* convert ls term into ski *)
  ski_of_ls ls_comb
```

Let's try it with the example given by Wikipedia:

```ocaml
(* Example lambda terms *)
let l2 : lambda = Abs ("x", Abs ("y", App (Var "y", Var "x")))

let _ = print_endline (string_of_ski (convert l2))
```

The output `T(T(S,T(K,T(S,I))),T(T(S,T(K,K)),I))`, is the same as `(S (K (S I)) (S (K K) I))`.

## References

1. Wikipedia [SKI Combinator calculus](https://en.wikipedia.org/wiki/SKI_combinator_calculus)
2. Wikipedia [Combinatory Logic](https://en.wikipedia.org/wiki/Combinatory_logic)
3. Wikipedia [Lambda Calculus](https://en.wikipedia.org/wiki/Lambda_calculus#Free_variables)
