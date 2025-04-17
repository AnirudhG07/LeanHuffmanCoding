import Huffmann.HuffmannTree

abbrev Pixel := Nat  -- grayscale 0-255
abbrev Freq := Nat
abbrev PixelFreqList := List (Pixel × Freq)

-- Instance for Nat since Pixel = Nat
instance : HfmnType Pixel where
  default := 0
  decEq := inferInstance

-- Simulate reading an image (in real code, use an image library)
def readImage (_ : String) : List Pixel := 
  [128, 0, 255, 128, 128, 0]  -- Example grayscale pixels

-- Calculate frequencies from pixel list
def buildFrequencyTable (pixels : List Pixel) : PixelFreqList :=
  let counts := pixels.foldl (fun acc p => 
    match acc.find? (fun (x, _) => x == p) with
    | some (_, c) => (p, c + 1) :: acc.filter (fun (x, _) => x != p)
    | none => (p, 1) :: acc
  ) []
  counts.reverse

-- Compress using Huffman codes
def compressImage (pixels : List Pixel) (table : List (Pixel × BoolList)) : List Bool :=
  pixels.foldl (fun acc px =>
    match table.find? (·.1 == px) with
    | some (_, code) => acc ++ code
    | none => acc  -- Shouldn't happen if table is complete
  ) []

-- Decompress using Huffman tree
partial def decompressImage (bits : List Bool) (tree : HfmnTree Pixel) : List Pixel :=
  let rec walk (remaining : List Bool) (current : HfmnTree Pixel) (acc : List Pixel) :=
    match current with
    | HfmnTree.Leaf val _ _ => 
      match remaining with
      | [] => acc ++ [val]
      | _ => walk remaining tree (acc ++ [val])
    | HfmnTree.Node l r =>
      match remaining with
      | true :: bs => walk bs r acc
      | false :: bs => walk bs l acc
      | [] => acc
  walk bits tree []

-- Complete workflow
def processImage (imagePath : String) : List Pixel :=
  let pixels := readImage imagePath
  let freqs := buildFrequencyTable pixels
  let tree := HfmnTree.tree freqs
  let table := HfmnTree.encodedList freqs
  let compressed := compressImage pixels table
  decompressImage compressed tree
--
-- def main : IO Unit := do
--   let result := processImage "sample.png"  -- Simulated path
--   IO.println "Original: [128, 0, 255, 128, 128, 0]"
--   IO.println s!"Result: {result}"
