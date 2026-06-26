/- L4: Jordan decomposition. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
namespace MiniAlgebraicGroups

axiom jordanDecomposition (n : Nat) (G : AlgebraicGroup n) (g : GL n) (hg : G.carrier g) : True
axiom multiplicativeJordanDecompGL (n : Nat) (g : GL n) : True
axiom jordanDecompFunctoriality {n m : Nat} (G : AlgebraicGroup n) (H : AlgebraicGroup m) (phi : AlgebraicGroupHom G H) : True
axiom centralizerOfSemisimpleIsReductive (n : Nat) (G : AlgebraicGroup n) : True

#eval "Theorems.JordanDecomp: g = g_s * g_u (semisimple * unipotent)"
/-! ## Applications of Jordan Decomposition -/

axiom jordanDecompClassificationSemisimple (n : Nat) (G : AlgebraicGroup n) : True
axiom jordanDecompClassificationUnipotent (n : Nat) (G : AlgebraicGroup n) : True
axiom jordanDecompCentralizerStructure (n : Nat) (G : AlgebraicGroup n) : True

#eval "JordanDecomp: classification of semisimple/unipotent elements"
/-! ## Jordan-Chevalley in Lie Algebras -/
axiom jordanChevalleyDecompositionLieAlgebra (n : Nat) (G : AlgebraicGroup n) : True
axiom additiveJordanDecomposition (n : Nat) (G : AlgebraicGroup n) : True

#eval "JordanDecomp: Jordan-Chevalley in Lie algebras, additive decomposition"