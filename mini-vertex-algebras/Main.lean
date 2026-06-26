import MiniVertexAlgebras

open MiniVertexAlgebras

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════"
  IO.println "  MiniVertexAlgebras v0.1.0"
  IO.println "  Vertex Algebras and Vertex Operator Algebras"
  IO.println "═══════════════════════════════════════════════"
  IO.println "  Core: Vertex Algebra, VOA, fields, modes, Borcherds identity"
  IO.println "  Structures: VOA, modules, intertwining ops, subalgebras"
  IO.println "  Theorems: Goddard uniqueness, Dong's lemma, associativity"
  IO.println "  Examples: Heisenberg (free boson), Virasoro, Lattice, Commutative"
  IO.println "  Applications: Conformal Field Theory, Representation Theory"
  IO.println "  Advanced: Chiral algebras, W-algebras, Geometric Langlands"
  IO.println ""
  IO.println "  Dependencies: mini-object-kernel, mini-axiom-kernel, mini-logic-kernel"
  IO.println "  Run `lake env lean --run Test/Smoke.lean` for verification."
