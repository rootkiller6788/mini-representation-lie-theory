import MiniQuantumGroups

open MiniQuantumGroups

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniQuantumGroups v0.1.0"
  IO.println "  Quantum Groups: U_q(g), Hopf Algebras, R-matrices"
  IO.println "═══════════════════════════════════════"
  IO.println s!"  q-Calculus: q-numbers, q-factorials, q-binomials"
  IO.println s!"  U_q(sl_2): generators E,F,K,K⁻¹ with q-relations"
  IO.println s!"  R-Matrix: Yang-Baxter equation solutions"
  IO.println s!"  Quantum Plane: yx = q xy noncommutative algebra"
  IO.println s!"  M_q(2), SL_q(2): quantum matrix groups"
  IO.println s!"  Hopf Structure: coproduct, counit, antipode"
  IO.println s!"  Constructions: tensor products, Drinfeld double, FRT"
  IO.println s!"  Invariants: Jones polynomial, Kauffman bracket"
  IO.println s!"  Applications: Knot theory, TQFT, anyon computing"
  IO.println ""
  IO.println "  Examples:"
  IO.println s!"    qNumber 2 5 = {qNumber 2 5}"
  IO.println s!"    qFactorial 2 4 = {qFactorial 2 4}"
  IO.println s!"    qBinomial 2 6 3 = {qBinomial 2 6 3}"
  IO.println s!"    qExp 2 1 5 = {qExp 2 1 5}"
  IO.println ""
  IO.println "  See README.md for knowledge coverage and course alignment."
  IO.println "  Depends on: mini-object-kernel"
