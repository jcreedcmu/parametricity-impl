/-
Pretty-printing of core terms, a transliteration of the reference's `prettyTm`
(see haskell-impl/Main.hs). Reproduces its precedence scheme, `fresh`-renaming of
shadowed binders, and the `goLam`/`goPi` grouping loops byte-for-byte, so `nf`-mode
output matches the golden corpus.

Split per width (`prettyW`/`prettyN`), mutually recursive through the cross-width
formers (`glueTy`/`glue`/`unfib` embed narrow subterms; `unglue`/`fibTy`/`fib` embed
wide ones).
-/
import Parametricity.Basic

set_option linter.constructorNameAsVariable false

partial def fresh (ns : List Name) (x : Name) : Name :=
  if x == "_" then "_"
  else if ns.contains x then fresh ns (x ++ "'")
  else x

-- printing precedences
def atomp : Int := 3  -- U, var
def appp  : Int := 2  -- application
def pip   : Int := 1  -- pi
def letp  : Int := 0  -- let, lambda

/-- Wrap in parens if expression precedence is lower than enclosing precedence. -/
def parIf (b : Bool) (s : String) : String := if b then "(" ++ s ++ ")" else s

mutual
partial def prettyW (p : Int) (ns : List Name) : WTm → String
  | .var x   => ns[x.toNat]!
  | .app t u => parIf (appp < p) (prettyW appp ns t ++ " " ++ prettyW atomp ns u)
  | .lam x t =>
      let x := fresh ns x
      parIf (letp < p) ("λ " ++ x ++ goLamW (x :: ns) t)
  | .univ       => "U"
  | .baseTy     => "Base"
  | .base       => "base"
  | .pi x a b =>
      if x == "_" then
        parIf (pip < p) (prettyW appp ns a ++ " → " ++ prettyW pip ("_" :: ns) b)
      else
        let x := fresh ns x
        parIf (pip < p) (piBindW ns x a ++ goPiW (x :: ns) b)
  | .letE x a t u =>
      let x := fresh ns x
      parIf (letp < p)
        ("let " ++ x ++ " : " ++ prettyW letp ns a
          ++ "\n    = " ++ prettyW letp ns t
          ++ "\n;\n" ++ prettyW letp (x :: ns) u)
  | .glueTy x a b =>
      let x := fresh ns x
      parIf (letp < p)
        ("Glue{" ++ x ++ " :- " ++ prettyN letp ns a ++ "}, " ++ prettyN letp (x :: ns) b)
  | .glue m n =>
      parIf (letp < p) ("glue " ++ prettyN appp ns m ++ " with " ++ prettyN letp ns n)
  | .unfib m n =>
      parIf (letp < p) ("unfib " ++ prettyN appp ns m ++ " with " ++ prettyN letp ns n)

partial def prettyN (p : Int) (ns : List Name) : NTm → String
  | .var x   => ns[x.toNat]!
  | .app t u => parIf (appp < p) (prettyN appp ns t ++ " " ++ prettyN atomp ns u)
  | .lam x t =>
      let x := fresh ns x
      parIf (letp < p) ("λ " ++ x ++ goLamN (x :: ns) t)
  | .univ       => "U"
  | .baseTy     => "Base"
  | .base       => "base"
  | .pi x a b =>
      if x == "_" then
        parIf (pip < p) (prettyN appp ns a ++ " → " ++ prettyN pip ("_" :: ns) b)
      else
        let x := fresh ns x
        parIf (pip < p) (piBindN ns x a ++ goPiN (x :: ns) b)
  | .letE x a t u =>
      let x := fresh ns x
      parIf (letp < p)
        ("let " ++ x ++ " : " ++ prettyN letp ns a
          ++ "\n    = " ++ prettyN letp ns t
          ++ "\n;\n" ++ prettyN letp (x :: ns) u)
  | .unglue m => parIf (appp < p) ("unglue " ++ prettyW atomp ns m)
  | .fibTy m a => "[" ++ prettyN letp ns m ++ " in " ++ prettyW letp ns a ++ "]"
  | .fib m => parIf (appp < p) ("fib " ++ prettyW atomp ns m)

partial def piBindW (ns : List Name) (x : Name) (a : WTm) : String :=
  "(" ++ x ++ " : " ++ prettyW letp ns a ++ ")"

partial def goLamW (ns : List Name) : WTm → String
  | .lam x t => let x := fresh ns x; " " ++ x ++ goLamW (x :: ns) t
  | t        => ". " ++ prettyW letp ns t

partial def goPiW (ns : List Name) : WTm → String
  | .pi x a b =>
      if x == "_" then
        " → " ++ prettyW appp ns a ++ " → " ++ prettyW pip ("_" :: ns) b
      else
        let x := fresh ns x
        piBindW ns x a ++ goPiW (x :: ns) b
  | b => " → " ++ prettyW pip ns b

partial def piBindN (ns : List Name) (x : Name) (a : NTm) : String :=
  "(" ++ x ++ " : " ++ prettyN letp ns a ++ ")"

partial def goLamN (ns : List Name) : NTm → String
  | .lam x t => let x := fresh ns x; " " ++ x ++ goLamN (x :: ns) t
  | t        => ". " ++ prettyN letp ns t

partial def goPiN (ns : List Name) : NTm → String
  | .pi x a b =>
      if x == "_" then
        " → " ++ prettyN appp ns a ++ " → " ++ prettyN pip ("_" :: ns) b
      else
        let x := fresh ns x
        piBindN ns x a ++ goPiN (x :: ns) b
  | b => " → " ++ prettyN pip ns b
end
