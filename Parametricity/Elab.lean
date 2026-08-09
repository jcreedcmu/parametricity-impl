/-
Elaboration helpers, for testing and IO.
-/
import Parametricity.Basic
import Parametricity.Pretty
import Parametricity.Typecheck
import Parametricity.Parser

/-- Convert a byte offset into 1-based (line, column), counting columns by character. -/
def offsetToLineCol (file : String) (ofs : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut col := 1
  let mut b := 0
  for c in file.toList do
    if b ≥ ofs then break
    if c == '\n' then
      line := line + 1
      col := 1
    else
      col := col + 1
    b := b + c.utf8Size
  return (line, col)

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- Render an elaboration error exactly as the CLI prints it to stdout. -/
def renderError (file : String) (err : String × Pos) : String :=
  let (msg, ofs) := err
  let (linum, colnum) := offsetToLineCol file ofs
  let lnum := toString linum
  let lpad := spaces lnum.length
  let srcLine := (file.splitOn "\n").getD (linum - 1) ""
  s!"(stdin):{linum}:{colnum}:\n"
    ++ s!"{lpad} |\n"
    ++ s!"{lnum} | {srcLine}\n"
    ++ s!"{lpad} | {spaces (colnum - 1)}^\n"
    ++ s!"{msg}\n"

/-- Elaborate a source string in `nf` mode -/
def elabNf (file : String) (width : Width := .wide) : String :=
  match pSrc.run file with
  | .error e => e ++ "\n"
  | .ok t =>
    match width with
    | .wide =>
      match inferW (emptyCtx 0) t with
      | .error err => renderError file err
      | .ok (t, a) =>
          prettyW 0 [] (nfW [] t) ++ "\n  :\n" ++ prettyW 0 [] (quoteW 0 a) ++ "\n"
    | .narrow =>
      match inferN (emptyCtx 0) t with
      | .error err => renderError file err
      | .ok (t, a) =>
          prettyN 0 [] (nfN [] t) ++ "\n  :\n" ++ prettyN 0 [] (quoteN 0 a) ++ "\n"

/-- Elaborate a source string in `type` mode -/
def elabType (file : String) (width : Width := .wide) : String :=
  match pSrc.run file with
  | .error e => e ++ "\n"
  | .ok t =>
    match width with
    | .wide =>
      match inferW (emptyCtx 0) t with
      | .error err => renderError file err
      | .ok (_, a) => prettyW 0 [] (quoteW 0 a) ++ "\n"
    | .narrow =>
      match inferN (emptyCtx 0) t with
      | .error err => renderError file err
      | .ok (_, a) => prettyN 0 [] (quoteN 0 a) ++ "\n"
