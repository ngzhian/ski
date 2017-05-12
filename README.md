An experiment in SKI combinator calculus, below is the accompanying blog post,
originally on [my blog](https://blog.ngzhian.com/ski.html)

---

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
