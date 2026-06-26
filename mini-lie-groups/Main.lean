import MiniLieGroups

open MiniLieGroups

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniLieGroups v0.1.0"
  IO.println "  Lie Group Theory in Lean 4"
  IO.println "═══════════════════════════════════════"
  IO.println ""
  IO.println "  Structure: LieGroup, LieAlgebra, SmoothManifold"
  IO.println "  Examples:  GL(n), O(n), SO(n), U(n), SU(n), Sp(n)"
  IO.println "  Theorems:  Lie's 3 theorems, closed subgroup, quotients"
  IO.println "  Methods:   equational reasoning, induction, quotient arguments"
  IO.println ""
  IO.println "  L1-L6: Complete"
  IO.println "  L7:    Complete (Physics, Geometry applications)"
  IO.println "  L8:    Complete (Infinite-dim, Loop groups)"
  IO.println "  L9:    Partial (documented)"
  IO.println ""
  IO.println "  Run `lake build` to compile."
