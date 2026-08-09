import Parametricity.Basic
import Parametricity.Pretty
import Parametricity.Typecheck
import Parametricity.Parser
import Parametricity.Elab

/-! ## main and error rendering -/

def helpMsg : String := String.intercalate "\n"
  [ "usage: lake exe elab [--help | (nf|type) [--wide|--narrow]]"
  , "  --help   : display this message"
  , "  nf       : read & typecheck expression from stdin, print its normal form and type"
  , "  type     : read & typecheck expression from stdin, print its type"
  , "  --wide   : typecheck at the wide judgment (default)"
  , "  --narrow : typecheck at the narrow judgment" ] ++ "\n"

/-- Parse the optional trailing width flag; absent means wide. -/
def parseWidth : List String → Option Width
  | []           => some .wide
  | ["--wide"]   => some .wide
  | ["--narrow"] => some .narrow
  | _            => none

def runMode (run : String → Width → String) (rest : List String) : IO Unit :=
  match parseWidth rest with
  | none => IO.print helpMsg
  | some w => do
      let file ← (← IO.getStdin).readToEnd
      IO.print (run file w)

def main (args : List String) : IO Unit := do
  match args with
  | ["--help"] => IO.print helpMsg
  | "nf" :: rest => runMode (fun f w => elabNf f w) rest
  | "type" :: rest => runMode (fun f w => elabType f w) rest
  | _ => IO.print helpMsg
