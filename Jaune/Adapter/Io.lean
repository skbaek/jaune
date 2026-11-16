-- Adapter/Io.lean : `IO` helpers of the runner front ends.
--
-- Adapter module (see `scripts/layering.json`). Option-to-`IO` lifts, the
-- `IO` failure and guard helpers, hex-prefix stripping in `IO` and the JSON file
-- reader are used only by `Main.lean`, `Jaune/T8n.lean` and `TraceMain.lean`.
-- Relocated unchanged from `Jaune/Basic.lean`, goal `jaune-shape-and-names-v1`,
-- unit W0, so that the specification module holds no runner code.
import Jaune.Basic

namespace Jaune

open Jaune _root_.List _root_.Nat

def Option.toIO {ξ} (o : Option ξ)
  (msg : String := "error : option-to-IO lift failed, input is 'none'") :
  IO ξ := do
  match o with
  | none => throw (IO.Error.userError msg)
  | some x => pure x

def IO.throw {ξ} (s : String) : IO ξ := MonadExcept.throw <| IO.Error.userError s

def IO.remove0x (s : String) : IO String :=
  match s.toList with
  | '0' :: 'x' :: cs => return String.ofList cs
  | _ => IO.throw "prefix not 0x"

def IO.guard (φ : Prop) [Decidable φ] (msg : String) : IO Unit :=
  if φ then return () else IO.throw msg

def readJsonFile (filename : System.FilePath) : IO Lean.Json := do
  let contents ← IO.FS.readFile filename
  match Lean.Json.parse contents with
  | .ok json => pure json
  | .error err => throw (IO.userError err)

end Jaune

