import Huffman
open Huffman

/-- `lake env lean --run scripts/PackFile.lean <input> <output.z>` -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [inp, out] =>
      match ← packFile inp out with
      | .ok () => IO.println s!"packed {inp} -> {out}"; pure 0
      | .error e => IO.eprintln s!"pack error: {e}"; pure 1
  | _ => IO.eprintln "usage: PackFile <input> <output.z>"; pure 2
