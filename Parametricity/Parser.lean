/-
The surface-syntax parser, built with `Std.Internal.Parsec`.
Source positions are captured as byte offsets via `withPos` and converted to line/col only at error-display time.
-/
import Parametricity.Basic
import Std.Internal.Parsec

open Std.Internal.Parsec Std.Internal.Parsec.String

abbrev P := Std.Internal.Parsec.String.Parser

/-- Current byte offset into the source. -/
def getOffset : P Nat := fun it => .success it it.2.offset.byteIdx

/-- Whitespace + `--` line comments + `{- -}` block comments (megaparsec `L.space`). -/
partial def skipLineComment : P Unit := do
  match ← peek? with
  | some c => if c == '\n' then pure () else skip *> skipLineComment
  | none => pure ()

partial def skipBlockComment : P Unit :=
  (attempt (skipString "-}"))
  <|> (do match ← peek? with
          | some _ => skip *> skipBlockComment
          | none => pure ())

partial def spc : P Unit := do
  match ← peek? with
  | some c =>
      if c == ' ' || c == '\n' || c == '\t' || c == '\r' then
        skip *> spc
      else if c == '-' then
        (attempt (skipString "--") *> skipLineComment *> spc) <|> pure ()
      else if c == '{' then
        (attempt (skipString "{-") *> skipBlockComment *> spc) <|> pure ()
      else pure ()
  | none => pure ()

def lexeme (p : P α) : P α := p <* spc
def symbol (s : String) : P String := lexeme (pstring s)
def lchar (c : Char) : P Char := lexeme (pchar c)
def parens (p : P α) : P α := lchar '(' *> p <* lchar ')'
def pArrow : P String := symbol "→" <|> symbol "->"

def keyword (x : String) : Bool :=
  x == "let" || x == "in" || x == "λ" || x == "U"
  || x == "Base" || x == "base"
  || x == "Glue" || x == "glue" || x == "unglue"
  || x == "fib" || x == "unfib" || x == "with"

def pIdent : P Name := attempt do
  let x ← many1Chars (satisfy Char.isAlphanum)
  if keyword x then fail "keyword" else pure ()
  spc
  pure x

def pKeyword (kw : String) : P Unit := do
  let _ ← pstring kw
  (many1Chars (satisfy Char.isAlphanum) *> failure) <|> spc

def withPos (p : P Raw) : P Raw := do
  let o ← getOffset
  let t ← p
  pure (.srcPos o t)

def pBinder : P Name := pIdent <|> symbol "_"

def foldl1App : List Raw → Raw
  | t :: rest => rest.foldl .app t
  | [] => panic! "foldl1App: empty"

mutual
partial def pFibTy : P Raw := do
  let _ ← lchar '['
  let m ← pRaw
  pKeyword "in"
  let a ← pRaw
  let _ ← lchar ']'
  pure (.fibTy m a)

partial def pAtom : P Raw :=
  withPos ((Raw.var <$> pIdent) <|> (pKeyword "U" *> pure Raw.univ)
           <|> (pKeyword "Base" *> pure Raw.baseTy) <|> (pKeyword "base" *> pure Raw.base)
           <|> pFibTy) <|> parens pRaw

partial def pSpine : P Raw := do
  let atoms ← many1 pAtom
  pure (foldl1App atoms.toList)

partial def pLam : P Raw := do
  let _ ← lchar 'λ' <|> lchar '\\'
  let xs ← many1 pBinder
  let _ ← lchar '.'
  let t ← pRaw
  pure (xs.foldr .lam t)

partial def pPi : P Raw := do
  let dom ← many1 (parens (do
    let xs ← many1 pBinder
    let _ ← lchar ':'
    let a ← pRaw
    pure (xs, a)))
  let _ ← pArrow
  let cod ← pRaw
  pure (dom.foldr (fun (xs, a) t => xs.foldr (fun x acc => .pi x a acc) t) cod)

partial def funOrSpine : P Raw := do
  let sp ← pSpine
  let arr? ← (Option.some <$> pArrow) <|> pure none
  match arr? with
  | none => pure sp
  | some _ => .pi "_" sp <$> pRaw

partial def pLet : P Raw := do
  pKeyword "let"
  let x ← pBinder
  let _ ← symbol ":"
  let a ← pRaw
  let _ ← symbol "="
  let t ← pRaw
  let _ ← symbol ";"
  let u ← pRaw
  pure (.letE x a t u)

partial def pGlueTy : P Raw := attempt do
  pKeyword "Glue"
  let _ ← lchar '{'
  let x ← pBinder
  let _ ← symbol ":-"
  let a ← pRaw
  let _ ← lchar '}'
  let _ ← lchar ','
  let b ← pRaw
  pure (.glueTy x a b)

partial def pGlue : P Raw := attempt do
  pKeyword "glue"
  let m ← pSpine
  pKeyword "with"
  let n ← pRaw
  pure (.glue m n)

partial def pUnglue : P Raw := attempt do
  pKeyword "unglue"
  let m ← pSpine
  pure (.unglue m)

partial def pFib : P Raw := attempt do
  pKeyword "fib"
  let m ← pSpine
  pure (.fib m)

partial def pUnfib : P Raw := attempt do
  pKeyword "unfib"
  let m ← pSpine
  pKeyword "with"
  let n ← pRaw
  pure (.unfib m n)

partial def pRaw : P Raw :=
  withPos (pLam <|> pLet <|> pGlueTy <|> pGlue <|> pUnglue <|> pFib <|> pUnfib
           <|> attempt pPi <|> funOrSpine)
end

def pSrc : P Raw := spc *> pRaw <* eof
