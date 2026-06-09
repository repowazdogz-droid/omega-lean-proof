/- Scratch executable: JSON file → `jcsEncode` (NOT a shipped root).
   Uses `Lean.Json` only for test corpus I/O; profile values live in `OmegaJson`. -/
import Lean.Data.Json
import OmegaJCS.Types
import OmegaJCS.Encode

open Lean Json OmegaJCS

private def jsonNumToInt (n : JsonNumber) : Option Int :=
  if n.exponent = 0 then some n.mantissa else none

private def sortKvsUtf16 (kvs : List (String × OmegaJson)) : List (String × OmegaJson) :=
  kvs.mergeSort fun a b => utf16LtBool a.1 b.1

private partial def jsonToOmega (j : Json) : Except String OmegaJson :=
  match j with
  | .null => .ok .null
  | .bool b => .ok (.bool b)
  | .num n =>
      match jsonNumToInt n with
      | some i => .ok (.int i)
      | none => .error "non-integer number"
  | .str s => .ok (.str s)
  | .arr elems =>
      match elems.toList.mapM jsonToOmega with
      | .ok xs => .ok (.arr xs)
      | .error e => .error e
  | .obj tree =>
      match tree.toList.mapM (fun (k, v) => jsonToOmega v |>.map (k, ·)) with
      | .ok kvs => .ok (.obj (sortKvsUtf16 kvs))
      | .error e => .error e

def main (args : List String) : IO Unit := do
  let path := args.getD 0 ""
  if path.isEmpty then
    IO.eprintln "usage: jcsDump <file.json>"
    return
  let content ← IO.FS.readFile path
  match Json.parse content with
  | .error e => IO.eprintln s!"parse error: {e}"
  | .ok j =>
      match jsonToOmega j with
      | .error e => IO.eprintln s!"profile error: {e}"
      | .ok v => IO.println (jcsEncode v)
