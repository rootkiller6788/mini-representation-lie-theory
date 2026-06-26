import MiniCharacterTheory

open MiniCharacterTheory

def main : IO Unit := do
  IO.println "═══════════════════════════════════════"
  IO.println "  MiniCharacterTheory v0.1.0"
  IO.println "  Character Theory of Finite Groups"
  IO.println "═══════════════════════════════════════"
  IO.println "  FiniteGroup: group operations on Fin n"
  IO.println "  Complex: real + imaginary pair"
  IO.println "  Representation: group homomorphism to GL(n, Complex)"
  IO.println "  Character: trace of representation (class function)"
  IO.println "  IrreducibleCharacter: character of irreducible representation"
  IO.println "  CharacterTable: matrix of irreducible character values"
  IO.println "  Pillar theorems: Orthogonality, Frobenius Reciprocity, Burnside p^a q^b"
  IO.println "  Inner product of characters: <chi, psi> = (1/|G|) sum chi(g) conj(psi(g))"
  IO.println "  Induction and restriction of characters"
  IO.println "  Tensor products, symmetric powers, exterior powers of characters"
  IO.println ""
  IO.println "  Depends on: mini-object-kernel, mini-axiom-kernel, mini-logic-kernel"
  IO.println "  Run `lake env lean --run Test/Smoke.lean` for tests."
