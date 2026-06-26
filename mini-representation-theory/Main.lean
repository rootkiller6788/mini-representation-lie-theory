/-
# Main - MiniRepresentationTheory

Entry point that prints package information.
-/

import MiniRepresentationTheory

open MiniRepresentationTheory

def main : IO Unit := do
  IO.println "══ mini-representation-theory ══"
  IO.println "Representation Theory for the Mini Math Kernel project."
  IO.println ""
  IO.println "Modules:"
  IO.println "  Core: Basic, Objects, Laws"
  IO.println "  Morphisms: Hom, Duality"
  IO.println "  Properties: Irreducibility, Characters"
  IO.println "  Theorems: SchurLemma, HighestWeight, WeylCharacter"
  IO.println "  Examples: sl2, sl3"
  IO.println "  Applications: Physics"
  IO.println "  Advanced: VermaModules (Category O, BGG resolution)"
  IO.println ""
  IO.println "══ End of mini-representation-theory info ══"