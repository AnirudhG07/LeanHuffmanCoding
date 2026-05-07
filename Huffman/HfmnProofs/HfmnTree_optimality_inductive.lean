import Huffman.HfmnProofs.HfmnInductiveOptimum

set_option linter.unusedSectionVars false

namespace HfmnTreeInductiveOptimality

/--
Compact entrypoint theorem for the direct inductive optimality route.
This is the same mathematical statement as `optimum_huffman` in the integrated
inductive development.
-/
theorem optimum_huffman_main {α : Type} [DecidableEq α]
  (ts : Forest α)
  (h_consistent_ts : consistentF ts)
  (h_height : heightF ts = 0)
  (h_sorted : sortedByWeight ts)
  (hne : ts ≠ []) :
  optimum (huffman ts hne) :=
  optimum_huffman ts h_consistent_ts h_height h_sorted hne

end HfmnTreeInductiveOptimality
