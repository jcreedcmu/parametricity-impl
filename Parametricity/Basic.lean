/-!
# Basic Definitions

Core syntax and value data types.

The two judgment levels of the theory (wide and narrow) are reflected in
separate syntactic sorts: `WTm`/`NTm` for terms, `WVal`/`NVal` for values.
-/

/-! ## Core data types -/

abbrev Name := String
abbrev Ix := Int   -- de Bruijn index
abbrev Lvl := Int  -- de Bruijn level
abbrev Pos := Nat  -- byte offset into source

/-- Surface syntax -/
inductive Raw where
  | var (x : Name)                          -- x
  | lam (x : Name) (t : Raw)                -- \x. t
  | app (t u : Raw)                         -- t u
  | univ                                    -- U
  | baseTy                                  -- Base
  | base                                    -- base
  | pi (x : Name) (a b : Raw)               -- (x : A) → B
  | letE (x : Name) (a t body : Raw)        -- let x : A = t; body
  | glueTy (x : Name) (a b : Raw)           -- Glue{x ÷ A}, B
  | glue (m n : Raw)                        -- glue M with N
  | unglue (m : Raw)                        -- unglue M
  | fibTy (m a : Raw)                       -- [M in A]
  | fib (m : Raw)                           -- fib M
  | unfib (m n : Raw)                       -- unfib M with N
  | srcPos (pos : Pos) (t : Raw)            -- source position for error reporting
  deriving Repr, Inhabited

mutual
/-- Wide term formers -/
inductive WTm where
  | var (x : Ix)
  | app (t u : WTm)
  | lam (x : Name) (t : WTm)
  | pi (x : Name) (a b : WTm)
  | univ
  | baseTy
  | base
  | letE (x : Name) (a t body : WTm)
  | glueTy (x : Name) (a b : NTm)           -- Glue{x :- A}, B
  | glue (m n : NTm)                        -- glue M with N
  | unfib (m n : NTm)                       -- unfib M with N
/-- Narrow term formers -/
inductive NTm where
  | var (x : Ix)
  | app (t u : NTm)
  | lam (x : Name) (t : NTm)
  | pi (x : Name) (a b : NTm)
  | univ
  | baseTy
  | base
  | letE (x : Name) (a t body : NTm)
  | unglue (m : WTm)                        -- unglue M
  | fibTy (m : NTm) (a : WTm)               -- [M in A]
  | fib (m : WTm)                           -- fib M
end

instance : Inhabited WTm := ⟨.univ⟩
instance : Inhabited NTm := ⟨.univ⟩

/-! ## Values -/

mutual
inductive WVal where
  | vvar (l : Lvl)
  | vapp (t u : WVal)
  | vlam (x : Name) (c : WClosure)
  | vpi (x : Name) (a : WVal) (c : WClosure)
  | vu
  | vbaseTy
  | vbase
  | vglueTy (x : Name) (a : NVal) (c : NClosure)
  | vglue (m n : NVal)
  | vunfib (m n : NVal)
inductive NVal where
  | vvar (l : Lvl)
  | vapp (t u : NVal)
  | vlam (x : Name) (c : NClosure)
  | vpi (x : Name) (a : NVal) (c : NClosure)
  | vu
  | vbaseTy
  | vbase
  | vunglue (t : WVal)                      -- neutral (t a wide neutral)
  | vfibTy (m : NVal) (a : WVal)
  | vfib (m : WVal)
inductive WClosure where | mk (env : List EnvEntry) (t : WTm)
inductive NClosure where | mk (env : List EnvEntry) (t : NTm)

/-- A per-slot-tagged environment entry: a variable's value lives at its home
width. -/
inductive EnvEntry where
  | wide (v : WVal)
  | narrow (v : NVal)
end

abbrev WTy := WVal
abbrev NTy := NVal
/-- The evaluation environment, indexed by de Bruijn level (head = most recent). -/
abbrev Env := List EnvEntry

instance : Inhabited WVal := ⟨.vu⟩
instance : Inhabited NVal := ⟨.vu⟩
instance : Inhabited EnvEntry := ⟨.wide .vu⟩

/-- Erasure on terms, `⌊·⌋ : WTm → NTm`. Usually a homomorphism, but the term formers
that pass to narrow content just return some of their narrow content. -/
def eraseTm : WTm → NTm
  | .var x           => .var x
  | .app t u         => .app (eraseTm t) (eraseTm u)
  | .lam x t         => .lam x (eraseTm t)
  | .pi x a b        => .pi x (eraseTm a) (eraseTm b)
  | .univ            => .univ
  | .baseTy          => .baseTy
  | .base            => .base
  | .letE x a t body => .letE x (eraseTm a) (eraseTm t) (eraseTm body)
  | .glueTy _ a _    => a            -- ⌊Glue{x÷A}, B⌋ = A
  | .glue m _        => m            -- ⌊glue M with N⌋ = M
  | .unfib m _       => m            -- ⌊unfib M with N⌋ = M

/-- Erasure on closures. -/
def eraseClosure : WClosure → NClosure
  | .mk env t => .mk env (eraseTm t)

/-- Erasure on values, `⌊·⌋ : WVal → NVal`. The value-level
counterpart of `eraseTm`. -/
def eraseVal : WVal → NVal
  | .vvar l        => .vvar l
  | .vapp t u      => .vapp (eraseVal t) (eraseVal u)
  | .vlam x c      => .vlam x (eraseClosure c)
  | .vpi x a c     => .vpi x (eraseVal a) (eraseClosure c)
  | .vu            => .vu
  | .vbaseTy       => .vbaseTy
  | .vbase         => .vbase
  | .vglueTy _ a _ => a             -- ⌊Glue{x÷A}, B⌋ = A
  | .vglue m _     => m             -- ⌊glue M with N⌋ = M
  | .vunfib m _    => m             -- ⌊unfib M with N⌋ = M

/-- Project an entry as a wide value. Should only ever be called on a
wide entry. -/
def EnvEntry.asWide : EnvEntry → WVal
  | .wide v   => v
  | .narrow _ => panic! "internal error: narrow entry used at the wide judgment"

/-- Project an entry as a narrow value. -/
def EnvEntry.asNarrow : EnvEntry → NVal
  | .wide v   => eraseVal v
  | .narrow v => v
