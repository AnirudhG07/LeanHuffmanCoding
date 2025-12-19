import Cli
import Huffman.HuffmanTree
open Cli

-- This has already been defined. You can change the example as per your wish.
-- def _eg : AlphaNumList Char := [('a', 45),('b', 13),('c', 12),('d', 16),('e', 9),('f', 5)]


-- #eval HfmnTree.tree _eg
-- #eval HfmnTree.encodedList _eg
-- #eval Huffman.leastEncodedData _eg -- 224


def runExampleCmd (p : Parsed) : IO UInt32 := do
  let input   : String       := p.positionalArg! "input" |>.as! String
  let outputs : Array String := p.variableArgsAs! String
  IO.println <| "Input: " ++ input
  IO.println <| "Outputs: " ++ toString outputs

  if p.hasFlag "verbose" then
    IO.println "Flag `--verbose` was set."
  if p.hasFlag "invert" then
    IO.println "Flag `--invert` was set."
  if p.hasFlag "optimize" then
    IO.println "Flag `--optimize` was set."

  let priority : Nat := p.flag! "priority" |>.as! Nat
  IO.println <| "Flag `--priority` always has at least a default value: " ++ toString priority

  if p.hasFlag "module" then
    let moduleName : ModuleName := p.flag! "module" |>.as! ModuleName
    IO.println <| s!"Flag `--module` was set to `{moduleName}`."

  if let some setPathsFlag := p.flag? "set-paths" then
    IO.println <| toString <| setPathsFlag.as! (Array String)
  return 0

def installCmd := `[Cli|
  installCmd NOOP;
  "installCmd provides an example for a subcommand without flags or arguments that does nothing.
  Versions can be omitted."
]

def testCmd := `[Cli|
  testCmd NOOP;
  "testCmd provides another example for a subcommand without flags or arguments that does nothing."
]

def exampleCmd : Cmd := `[Cli|
  exampleCmd VIA runExampleCmd; ["0.0.1"]
  "This string denotes the description of `exampleCmd`."

  FLAGS:
    verbose;                    "Declares a flag `--verbose`. This is the description of the flag."
    i, invert;                  "Declares a flag `--invert` with an associated short alias `-i`."
    o, optimize;                "Declares a flag `--optimize` with an associated short alias `-o`."
    p, priority : Nat;          "Declares a flag `--priority` with an associated short alias `-p`
                                that takes an argument of type `Nat`."
    module : ModuleName;        "Declares a flag `--module` that takes an argument of type `ModuleName`
                                which be can used to reference Lean modules like `Init.Data.Array`
                                or Lean files using a relative path like `Init/Data/Array.lean`."
    "set-paths" : Array String; "Declares a flag `--set-paths`
                                that takes an argument of type `Array String`.
                                Quotation marks allow the use of hyphens."

  ARGS:
    input : String;      "Declares a positional argument <input>
                         that takes an argument of type `String`."
    ...outputs : String; "Declares a variable argument <output>...
                         that takes an arbitrary amount of arguments of type `String`."

  SUBCOMMANDS:
    installCmd;
    testCmd

  -- The EXTENSIONS section denotes features that
  -- were added as an external extension to the library.
  -- `./Cli/Extensions.lean` provides some commonly useful examples.
  EXTENSIONS:
    author "Anirudh Gupta";
    defaultValues! #[("priority", "0")]
]

def main (args : List String) : IO UInt32 :=
  exampleCmd.validate args
