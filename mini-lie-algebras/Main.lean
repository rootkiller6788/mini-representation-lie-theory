/-
# Main — MiniLieAlgebras

Entry point that prints package information and runs examples.
-/

import MiniLieAlgebras

open MiniLieAlgebras.Basic

def main : IO Unit := do
  IO.println "══ mini-lie-algebras ══"
  IO.println "Lie Algebra Theory for the Mini Everything Math project."
  IO.println ""
  IO.println "Modules:"
  IO.println "  Core:        LieAlgebra, Subalgebra, Ideal, Homomorphism"
  IO.println "  Structure:   Solvable, Nilpotent, Simple, Semisimple"
  IO.println "  Theorems:    Engel, Lie, Cartan, PBW, Weyl"
  IO.println "  Examples:    sl(2), sl(3), gl(n), so(n), sp(2n)"
  IO.println "  Classify:    Dynkin diagrams A-G, Cartan matrices"
  IO.println "  Applications:  Gauge theory, Integrable systems"
  IO.println "  Advanced:    Kac-Moody, Vertex algebras"
  IO.println "  Frontiers:   Geometric Langlands, W-algebras"
  IO.println ""
  IO.println "══ End of mini-lie-algebras info ══"
