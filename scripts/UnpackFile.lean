import Huffman
open Huffman

/-- `lake env lean --run scripts/UnpackFile.lean <input.z> <output>` -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [inp, out] =>
      match ← unpackFile inp out with
      | .ok () => IO.println s!"unpacked {inp} -> {out}"; pure 0
      | .error e => IO.eprintln s!"unpack error: {e}"; pure 1
  | _ => IO.eprintln "usage: UnpackFile <input.z> <output>"; pure 2
