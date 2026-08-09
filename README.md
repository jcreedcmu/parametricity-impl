# Parametricity Implementation

I'm trying to work out a comfortably minimal modal type theory for
(non-iterated) internalized parametricity. This repository currently
has an attempted implementation, based on some very nice and
understandable haskell code in
https://github.com/AndrasKovacs/elaboration-zoo

Some version of it is described in
https://jcreedcmu.github.io/posts/2026-07-11/

## Files

An emacs major mode is in `etc`.

Tests cases are in `tests`.

## Running Tests

```shell
lake test
```

## Syntax

Looking at `tests/parametricity/60-fracture.tt` for example:

```
let fore : (A : U) (a : A) -> Glue{x :- A}, [x in A] =
 \A a. glue a with fib a;
let back : (A : U) (g : Glue{x :- A}, [x in A]) -> A =
 \A g. unfib g with unglue g;

let zig : (A : U) (a : A) (P : A -> U)
    -> P (back A (fore A a)) -> P a =
 \A g P p. p;

let zag : (A : U) (g : Glue{x :- A}, [x in A]) (P : (Glue{x :- A}, [x in A]) -> U)
    -> P (fore A (back A g)) -> P g =
 \A g P p. p;

U
```

Let-expressions are `let x : A = M; N`. Lambda can be written with a backslash.
$\Pi$-quantification is done like `(a : A) ->`. The universe of types
is named `U`. Since this is just a prototype, we have `U : U`.

Glue types are written `Glue{x :- A}, B`. The intro form is `glue M with N`,
the elim is `unglue M`.

Fiber types are written `[M in A]`. The intro form is `fib M`, the
elim is `unfib M with N`.

Every test file is named `*.tt` and contains a single expression to be
typechecked. The test runner normalizes them and compares them to the
corresponding `*.tt.golden` file.
