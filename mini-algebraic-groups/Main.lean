import MiniAlgebraicGroups

open MiniAlgebraicGroups

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniAlgebraicGroups v0.1.0"
  IO.println "  Algebraic Groups Sub-Package"
  IO.println "═══════════════════════════════════════"
  IO.println s!"  linear algebraic group: subgroup of GL(n) defined by polynomial equations"
  IO.println s!"  GL(n), SL(n), Sp(2n), SO(n): classical algebraic groups"
  IO.println s!"  Ga (additive group), Gm (multiplicative group): basic building blocks"
  IO.println s!"  torus: diagonal matrices with nonzero entries"
  IO.println s!"  unipotent group: upper triangular matrices with 1s on diagonal"
  IO.println s!"  Borel subgroup: maximal connected solvable subgroup"
  IO.println s!"  root data: combinatorial classification of reductive groups"
  IO.println s!"  Dynkin diagrams: A_n, B_n, C_n, D_n, E_6, E_7, E_8, F_4, G_2"
  IO.println s!"  Lie-Kolchin theorem: connected solvable group is triangularizable"
  IO.println s!"  Borel fixed point theorem: solvable group on complete variety has fixed point"
  IO.println s!"  Jordan decomposition: semisimple + unipotent in affine algebraic groups"
  IO.println ""
  IO.println "  Self-contained: no external dependencies"
  IO.println "  Run lake build to compile."
