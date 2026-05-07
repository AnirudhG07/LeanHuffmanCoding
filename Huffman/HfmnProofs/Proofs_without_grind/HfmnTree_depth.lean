import Huffman.HfmnTree_prefixfreeness

variable {α : Type} [DecidableEq α] [Inhabited α] [Ord α] [HfmnType α]

instance [Inhabited α] [DecidableEq α] : HfmnType α where
  default := default

def HfmnTree.depthAux (tree: HfmnTree α) (c: α) (d: Int) : Int :=
  match tree with
  | HfmnTree.Leaf c' _ =>
    -- The decidability of equality has been invoked previously for the type α
    if c = c' then d else -1
  | HfmnTree.Node l r  =>
    let leftDepth := depthAux l c (d + 1)
    if leftDepth != -1 then leftDepth else depthAux r c (d + 1)

-- #eval HfmnTree.depthAux (HfmnTree.tree eg₁) 'd' 0

