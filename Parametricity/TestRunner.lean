/-
Native golden-test runner: elaborates every `tests/*/ *.tt` case in a single Lean
process (no per-test `lake exe` fork) and diffs against the `.tt.golden` file.

  lake exe test              # compare
  ACCEPT=1 lake exe test     # (re)generate goldens

Mirrors `scripts/run-tests.sh`: compares stdout with trailing newlines stripped,
prints PASS/FAIL/NOGOLD per case, and exits nonzero if any case fails.

Each case elaborates at the wide judgment by default; a `-- width: narrow` comment
line in the `.tt` file switches it to narrow.
-/
import Parametricity.Elab

/-- Strip trailing newlines, matching bash `$(...)` command-substitution semantics
so comparisons are insensitive to a final-newline mismatch. -/
def dropTrailingNewlines (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (· == '\n') |>.reverse)

/-- All `*.tt` test inputs under `tests/`, sorted for stable output. -/
def collectTests (dir : System.FilePath) : IO (Array System.FilePath) := do
  let all ← System.FilePath.walkDir dir
  pure <| (all.filter (·.extension == some "tt")).qsort (·.toString < ·.toString)

/-- Judgment width a test elaborates at. Opt into narrow with a `-- width: narrow`
directive line (a comment, so the parser ignores it); default is wide. -/
def readWidth (file : String) : Width :=
  if (file.splitOn "\n").any (·.trimAscii == "-- width: narrow") then .narrow else .wide

def main : IO UInt32 := do
  let accept := (← IO.getEnv "ACCEPT") == some "1"
  let tests ← collectTests "tests"
  let mut pass := 0
  let mut fail := 0
  let mut accepted := 0
  for f in tests do
    let name := f.toString
    let golden := name ++ ".golden"
    let src ← IO.FS.readFile f
    let actual := elabNf src (readWidth src)
    if accept then
      IO.FS.writeFile golden (dropTrailingNewlines actual ++ "\n")
      IO.println s!"ACCEPT {name}"
      accepted := accepted + 1
    else if !(← System.FilePath.pathExists golden) then
      IO.println s!"NOGOLD {name} (run with ACCEPT=1 first)"
      fail := fail + 1
    else
      let expected ← IO.FS.readFile golden
      if dropTrailingNewlines actual == dropTrailingNewlines expected then
        IO.println s!"PASS  {name}"
        pass := pass + 1
      else
        IO.println s!"FAIL  {name}"
        IO.println "--- expected ---"
        for l in (dropTrailingNewlines expected).splitOn "\n" do IO.println l
        IO.println "--- actual ---"
        for l in (dropTrailingNewlines actual).splitOn "\n" do IO.println l
        fail := fail + 1
  IO.println ""
  if accept then
    IO.println s!"accepted {accepted} goldens"
    return 0
  else
    IO.println s!"{pass} passed, {fail} failed"
    return (if fail == 0 then 0 else 1)
