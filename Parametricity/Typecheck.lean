import Parametricity.Basic
import Parametricity.Pretty

/-! ## Evaluation -/

def lvl2Ix (l x : Lvl) : Ix := l - x - 1

mutual
partial def cappW : WClosure → WVal → WVal
  | .mk env t, u => evalW (.wide u :: env) t

partial def cappN : NClosure → NVal → NVal
  | .mk env t, u => evalN (.narrow u :: env) t

partial def evalW (env : Env) : WTm → WVal
  | .var x        => (env[x.toNat]!).asWide
  | .app t u      => match evalW env t, evalW env u with
                       | .vlam _ c, u => cappW c u
                       | t, u         => .vapp t u
  | .lam x t      => .vlam x (.mk env t)
  | .pi x a b     => .vpi x (evalW env a) (.mk env b)
  | .univ         => .vu
  | .baseTy       => .vbaseTy
  | .base         => .vbase
  | .letE _ _ t u => evalW (.wide (evalW env t) :: env) u
  | .glueTy x a b => .vglueTy x (evalN env a) (.mk env b)
  | .glue m n     => .vglue (evalN env m) (evalN env n)
  | .unfib m n    => match evalN env n with                 -- fiber β
                       | .vfib k => k
                       | vn      => .vunfib (evalN env m) vn

partial def evalN (env : Env) : NTm → NVal
  | .var x        => (env[x.toNat]!).asNarrow                -- erases a wide entry
  | .app t u      => match evalN env t, evalN env u with
                       | .vlam _ c, u => cappN c u
                       | t, u         => .vapp t u
  | .lam x t      => .vlam x (.mk env t)
  | .pi x a b     => .vpi x (evalN env a) (.mk env b)
  | .univ         => .vu
  | .baseTy       => .vbaseTy
  | .base         => .vbase
  | .letE _ _ t u => evalN (.narrow (evalN env t) :: env) u
  | .unglue m     => match evalW env m with                 -- glue β
                       | .vglue _ n => n
                       | t          => .vunglue t
  | .fibTy m a    => .vfibTy (evalN env m) (evalW env a)
  | .fib m        => .vfib (evalW env m)
end

mutual
partial def quoteW (l : Lvl) : WVal → WTm
  | .vvar x        => .var (lvl2Ix l x)
  | .vapp t u      => .app (quoteW l t) (quoteW l u)
  | .vlam x c      => .lam x (quoteW (l + 1) (cappW c (.vvar l)))
  | .vpi x a c     => .pi x (quoteW l a) (quoteW (l + 1) (cappW c (.vvar l)))
  | .vu            => .univ
  | .vbaseTy       => .baseTy
  | .vbase         => .base
  | .vglueTy x a c => .glueTy x (quoteN l a) (quoteN (l + 1) (cappN c (.vvar l)))
  | .vglue m n     => .glue (quoteN l m) (quoteN l n)
  | .vunfib m n    => .unfib (quoteN l m) (quoteN l n)

partial def quoteN (l : Lvl) : NVal → NTm
  | .vvar x        => .var (lvl2Ix l x)
  | .vapp t u      => .app (quoteN l t) (quoteN l u)
  | .vlam x c      => .lam x (quoteN (l + 1) (cappN c (.vvar l)))
  | .vpi x a c     => .pi x (quoteN l a) (quoteN (l + 1) (cappN c (.vvar l)))
  | .vu            => .univ
  | .vbaseTy       => .baseTy
  | .vbase         => .base
  | .vunglue t     => .unglue (quoteW l t)
  | .vfibTy m a    => .fibTy (quoteN l m) (quoteW l a)
  | .vfib m        => .fib (quoteW l m)
end

def nfW (env : Env) (t : WTm) : WTm := quoteW (env.length : Int) (evalW env t)
def nfN (env : Env) (t : NTm) : NTm := quoteN (env.length : Int) (evalN env t)

/-! ## Conversion

Type-directed βη conversion. Every comparison is done at a type. The η
rule works according to that type. The two levels reference each
other, so `convW` and `convN` are mutually recursive. -/

def appW : WVal → WVal → WVal
  | .vlam _ c, u => cappW c u
  | t, u         => .vapp t u

def appN : NVal → NVal → NVal
  | .vlam _ c, u => cappN c u
  | t, u         => .vapp t u

/-- Semantic fiber elimination -/
def unfibW (m : NVal) : NVal → WVal
  | .vfib k => k
  | t       => .vunfib m t

/-- Semantic glue elimination -/
def unglueN : WVal → NVal
  | .vglue _ n => n
  | t          => .vunglue t

mutual
/-- Compare wide `t`, `u` at wide type `ty`; `tys` gives free-variable types. -/
partial def convW (tys : Env) (ty : WVal) (t u : WVal) : Bool :=
  let l : Lvl := (tys.length : Int)
  match ty with
  | .vpi _ a b =>                                    -- function η
      let x := WVal.vvar l
      convW (.wide a :: tys) (cappW b x) (appW t x) (appW u x)
  | .vglueTy _ a b =>                                -- glue η (compares narrow parts)
      let et := eraseVal t
      let eu := eraseVal u
      convN tys a et eu && convN tys (cappN b et) (unglueN t) (unglueN u)
  | _ =>                                             -- U or a neutral type: no η
      convStructW tys t u

/-- Compare narrow `t`, `u` at narrow type `ty`. -/
partial def convN (tys : Env) (ty : NVal) (t u : NVal) : Bool :=
  let l : Lvl := (tys.length : Int)
  match ty with
  | .vpi _ a b =>                                    -- function η
      let x := NVal.vvar l
      convN (.narrow a :: tys) (cappN b x) (appN t x) (appN u x)
  | .vfibTy m a =>                                   -- fiber η (compares wide unfibs)
      convW tys a (unfibW m t) (unfibW m u)
  | _ =>
      convStructN tys t u

partial def convStructW (tys : Env) (t u : WVal) : Bool :=
  let l : Lvl := (tys.length : Int)
  match t, u with
  | .vu, .vu => true
  | .vbaseTy, .vbaseTy => true
  | .vbase, .vbase => true
  | .vpi _ a b, .vpi _ a' b' =>
      convW tys .vu a a' && convW (.wide a :: tys) .vu (cappW b (.vvar l)) (cappW b' (.vvar l))
  | .vglueTy _ a b, .vglueTy _ a' b' =>
      convN tys .vu a a' && convN (.narrow a :: tys) .vu (cappN b (.vvar l)) (cappN b' (.vvar l))
  | _, _ => (convNeW tys t u).isSome

partial def convStructN (tys : Env) (t u : NVal) : Bool :=
  let l : Lvl := (tys.length : Int)
  match t, u with
  | .vu, .vu => true
  | .vbaseTy, .vbaseTy => true
  | .vbase, .vbase => true
  | .vpi _ a b, .vpi _ a' b' =>
      convN tys .vu a a' && convN (.narrow a :: tys) .vu (cappN b (.vvar l)) (cappN b' (.vvar l))
  | .vfibTy m a, .vfibTy m' a' =>
      convW tys .vu a a' && convN tys (eraseVal a) m m'
  | _, _ => (convNeN tys t u).isSome

/-- Compare wide neutral spines; return their (shared) wide type when equal. -/
partial def convNeW (tys : Env) (t u : WVal) : Option WVal :=
  match t, u with
  | .vvar x, .vvar x' =>
      if x == x' then (tys[(tys.length - 1 - x.toNat)]?).map (·.asWide) else none
  | .vapp t a, .vapp t' a' =>
      match convNeW tys t t' with
      | some (.vpi _ dom cod) => if convW tys dom a a' then some (cappW cod a) else none
      | _ => none
  | .vunfib m t, .vunfib m' t' =>
      match convNeN tys t t' with
      | some (.vfibTy _ a) => if convN tys (eraseVal a) m m' then some a else none
      | _ => none
  | _, _ => none

/-- Compare narrow neutral spines; return their (shared) narrow type when equal. -/
partial def convNeN (tys : Env) (t u : NVal) : Option NVal :=
  match t, u with
  | .vvar x, .vvar x' =>
      if x == x' then (tys[(tys.length - 1 - x.toNat)]?).map (·.asNarrow) else none
  | .vapp t a, .vapp t' a' =>
      match convNeN tys t t' with
      | some (.vpi _ dom cod) => if convN tys dom a a' then some (cappN cod a) else none
      | _ => none
  | .vunglue t, .vunglue t' =>
      match convNeW tys t t' with
      | some (.vglueTy _ _ b) => some (cappN b (eraseVal t))
      | _ => none
  | _, _ => none
end

/-! ## Elaboration -/

/-- The kind of a context hypothesis: ordinary `x : A`, weak
`x :- A`, or strong `x :: A`. -/
inductive HypKind | ord | weak | strong
  deriving Repr, DecidableEq, BEq

/-- The judgment width axis. -/
inductive Width | narrow | wide
  deriving Repr, DecidableEq, BEq

/-- Elaboration context. -/
structure Ctx where
  env : Env
  types : List (Name × HypKind × EnvEntry)
  lvl : Lvl
  pos : Pos

def emptyCtx (pos : Pos) : Ctx := ⟨[], [], 0, pos⟩

/-- Extend with a wide-bound variable. -/
def bindW (x : Name) (a : WTy) (ctx : Ctx) (k : HypKind := .ord) : Ctx :=
  { ctx with env := .wide (.vvar ctx.lvl) :: ctx.env,
             types := (x, k, .wide a) :: ctx.types, lvl := ctx.lvl + 1 }

/-- Extend with a narrow-bound variable. -/
def bindN (x : Name) (a : NTy) (ctx : Ctx) (k : HypKind := .weak) : Ctx :=
  { ctx with env := .narrow (.vvar ctx.lvl) :: ctx.env,
             types := (x, k, .narrow a) :: ctx.types, lvl := ctx.lvl + 1 }

/-- Extend with a wide definition. -/
def defineW (x : Name) (v : WVal) (a : WTy) (ctx : Ctx) (k : HypKind := .ord) : Ctx :=
  { ctx with env := .wide v :: ctx.env, types := (x, k, .wide a) :: ctx.types, lvl := ctx.lvl + 1 }

/-- Extend with a narrow definition. -/
def defineN (x : Name) (v : NVal) (a : NTy) (ctx : Ctx) (k : HypKind := .weak) : Ctx :=
  { ctx with env := .narrow v :: ctx.env, types := (x, k, .narrow a) :: ctx.types, lvl := ctx.lvl + 1 }

/-! ### Context operations -/

/-- demote: `x : A ↦ x :- ⌊A⌋`; weak/strong unchanged. -/
def demoteCtx (c : Ctx) : Ctx :=
  { c with types := c.types.map (fun (x, k, e) =>
      match k, e with
      | .ord, .wide a => (x, .weak, .narrow (eraseVal a))
      | _, _          => (x, k, e)) }

/-- promote: `x : A ↦ x :: A`; weak/strong unchanged. -/
def promoteCtx (c : Ctx) : Ctx :=
  { c with types := c.types.map (fun (x, k, e) =>
      match k with | .ord => (x, .strong, e) | _ => (x, k, e)) }

/-- Variable types by level. -/
def Ctx.varTys (ctx : Ctx) : Env := ctx.types.map (·.2.2)

/-- Typechecking monad. For now just an error annotated with the current source position. -/
abbrev CheckT := Except (String × Pos)

def showValW (ctx : Ctx) (v : WVal) : String :=
  prettyW 0 (ctx.types.map (·.1)) (quoteW ctx.lvl v)

def showValN (ctx : Ctx) (v : NVal) : String :=
  prettyN 0 (ctx.types.map (·.1)) (quoteN ctx.lvl v)

/-- Variable lookup at a wide judgment: ordinary and strong variables are usable
(with their wide type); a weak variable is a type error. -/
def lookupVarW (ctx : Ctx) (x : Name) : CheckT (WTm × WTy) :=
  let rec go (i : Ix) : List (Name × HypKind × EnvEntry) → CheckT (WTm × WTy)
    | [] => .error (s!"variable out of scope: {x}", ctx.pos)
    | (x', k, e) :: tys =>
        if x == x' then
          match k with
          | .weak => .error (s!"weak variable '{x}' (:-) cannot be used while building a wide expression", ctx.pos)
          | .ord | .strong => .ok (.var i, e.asWide)
        else go (i + 1) tys
  go 0 ctx.types

/-- Variable lookup at a narrow judgment: weak and strong variables are usable
(if strong, we take its erased type); an ordinary variable is an invariant violation. -/
def lookupVarN (ctx : Ctx) (x : Name) : CheckT (NTm × NTy) :=
  let rec go (i : Ix) : List (Name × HypKind × EnvEntry) → CheckT (NTm × NTy)
    | [] => .error (s!"variable out of scope: {x}", ctx.pos)
    | (x', k, e) :: tys =>
        if x == x' then
          match k with
          | .ord => panic! s!"internal error: ordinary variable '{x}' (:) present in a narrow judgment"
          | .weak | .strong => .ok (.var i, e.asNarrow)
        else go (i + 1) tys
  go 0 ctx.types

mutual
/-- Check a `Raw` against a wide type, producing a `WTm`. -/
partial def checkW (ctx : Ctx) (t : Raw) (a : WTy) : CheckT WTm := do
  match t, a with
  | .srcPos pos t, a => checkW { ctx with pos := pos } t a
  | .lam x t, .vpi _ a b =>
      .lam x <$> checkW (bindW x a ctx) t (cappW b (.vvar ctx.lvl))
  | .glue m n, .vglueTy _ a b => do
      let m ← checkN (demoteCtx ctx) m a
      let vm := evalN ctx.env m
      let n ← checkN (promoteCtx ctx) n (cappN b vm)
      pure (.glue m n)
  | .letE x aT t u, a' => do
      let aT ← checkW ctx aT .vu
      let va := evalW ctx.env aT
      let t ← checkW ctx t va
      let vt := evalW ctx.env t
      let u ← checkW (defineW x vt va ctx) u a'
      pure (.letE x aT t u)
  | t, a => do
      let (t, tty) ← inferW ctx t
      unless convW ctx.varTys .vu tty a do
        .error
          (s!"type mismatch\n\nexpected type:\n\n  {showValW ctx a}\n\ninferred type:\n\n  {showValW ctx tty}\n",
           ctx.pos)
      pure t

/-- Infer a wide type for a `Raw`, producing a `WTm`. -/
partial def inferW (ctx : Ctx) : Raw → CheckT (WTm × WTy)
  | .srcPos pos t => inferW { ctx with pos := pos } t
  | .var x => lookupVarW ctx x
  | .univ => pure (.univ, .vu)   -- U : U
  | .baseTy => pure (.baseTy, .vu)   -- Base : U
  | .base => pure (.base, .vbaseTy)  -- base : Base
  | .app t u => do
      let (t, tty) ← inferW ctx t
      match tty with
      | .vpi _ a b => do
          let u ← checkW ctx u a
          pure (.app t u, cappW b (evalW ctx.env u))
      | tty =>
          .error (s!"Expected a function type, instead inferred:\n\n  {showValW ctx tty}", ctx.pos)
  | .lam .. => .error ("Can't infer type for lambda expression", ctx.pos)
  | .pi x a b => do
      let a ← checkW ctx a .vu
      let b ← checkW (bindW x (evalW ctx.env a) ctx) b .vu
      pure (.pi x a b, .vu)
  | .letE x a t u => do
      let a ← checkW ctx a .vu
      let va := evalW ctx.env a
      let t ← checkW ctx t va
      let vt := evalW ctx.env t
      let (u, uty) ← inferW (defineW x vt va ctx) u
      pure (.letE x a t u, uty)
  | .glueTy x a b => do
      let a ← checkN (demoteCtx ctx) a .vu
      let va := evalN ctx.env a
      let b ← checkN (bindN x va (promoteCtx ctx)) b .vu
      pure (.glueTy x a b, .vu)
  | .glue .. => .error ("Can't infer type for glue; annotate it or check it against a Glue type", ctx.pos)
  | .unfib m n => do
      let (n, nty) ← inferN (promoteCtx ctx) n
      match nty with
      | .vfibTy m0 a =>
          let m ← checkN (demoteCtx ctx) m (eraseVal a)
          let vm := evalN ctx.env m
          unless convN (demoteCtx ctx).varTys (eraseVal a) vm m0 do
            .error
              (s!"unfib's basepoint disagrees with the fiber type\n\nfiber basepoint:\n\n  {showValN ctx m0}\n\ngiven basepoint:\n\n  {showValN ctx vm}\n",
               ctx.pos)
          pure (.unfib m n, a)
      | nty =>
          .error (s!"unfib expects a fiber type [_ in _], instead inferred:\n\n  {showValN ctx nty}", ctx.pos)
  | .unglue _ => .error ("unglue is a narrow-only form, but the current judgment is wide", ctx.pos)
  | .fibTy .. => .error ("[_ in _] is a narrow-only form, but the current judgment is wide", ctx.pos)
  | .fib _ => .error ("fib is a narrow-only form, but the current judgment is wide", ctx.pos)

/-- Check a `Raw` against a narrow type, producing an `NTm`. -/
partial def checkN (ctx : Ctx) (t : Raw) (a : NTy) : CheckT NTm := do
  match t, a with
  | .srcPos pos t, a => checkN { ctx with pos := pos } t a
  | .lam x t, .vpi _ a b =>
      .lam x <$> checkN (bindN x a ctx) t (cappN b (.vvar ctx.lvl))
  | .letE x aT t u, a' => do
      let aT ← checkN ctx aT .vu
      let va := evalN ctx.env aT
      let t ← checkN ctx t va
      let vt := evalN ctx.env t
      let u ← checkN (defineN x vt va ctx) u a'
      pure (.letE x aT t u)
  | t, a => do
      let (t, tty) ← inferN ctx t
      unless convN ctx.varTys .vu tty a do
        .error
          (s!"type mismatch\n\nexpected type:\n\n  {showValN ctx a}\n\ninferred type:\n\n  {showValN ctx tty}\n",
           ctx.pos)
      pure t

/-- Infer a narrow type for a `Raw`, producing an `NTm`. -/
partial def inferN (ctx : Ctx) : Raw → CheckT (NTm × NTy)
  | .srcPos pos t => inferN { ctx with pos := pos } t
  | .var x => lookupVarN ctx x
  | .univ => pure (.univ, .vu)
  | .baseTy => pure (.baseTy, .vu)
  | .base => pure (.base, .vbaseTy)
  | .app t u => do
      let (t, tty) ← inferN ctx t
      match tty with
      | .vpi _ a b => do
          let u ← checkN ctx u a
          pure (.app t u, cappN b (evalN ctx.env u))
      | tty =>
          .error (s!"Expected a function type, instead inferred:\n\n  {showValN ctx tty}", ctx.pos)
  | .lam .. => .error ("Can't infer type for lambda expression", ctx.pos)
  | .pi x a b => do
      let a ← checkN ctx a .vu
      let b ← checkN (bindN x (evalN ctx.env a) ctx) b .vu
      pure (.pi x a b, .vu)
  | .letE x a t u => do
      let a ← checkN ctx a .vu
      let va := evalN ctx.env a
      let t ← checkN ctx t va
      let vt := evalN ctx.env t
      let (u, uty) ← inferN (defineN x vt va ctx) u
      pure (.letE x a t u, uty)
  | .unglue m => do
      let (m, mty) ← inferW ctx m
      match mty with
      | .vglueTy _ _ b =>
          let em := eraseVal (evalW ctx.env m)
          pure (.unglue m, cappN b em)
      | mty =>
          .error (s!"unglue expects a Glue type, instead inferred:\n\n  {showValW ctx mty}", ctx.pos)
  | .fibTy m a => do
      let a ← checkW ctx a .vu
      let va := evalW ctx.env a
      let m ← checkN ctx m (eraseVal va)
      pure (.fibTy m a, .vu)
  | .fib m => do
      let (m, a) ← inferW ctx m
      let em := eraseVal (evalW ctx.env m)
      pure (.fib m, .vfibTy em a)
  | .glueTy .. => .error ("Glue is a wide-only form, but the current judgment is narrow", ctx.pos)
  | .glue .. => .error ("glue is a wide-only form, but the current judgment is narrow", ctx.pos)
  | .unfib .. => .error ("unfib is a wide-only form, but the current judgment is narrow", ctx.pos)
end
