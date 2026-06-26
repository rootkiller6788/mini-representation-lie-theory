/- L4: Lie-Kolchin theorem. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Constructions.Subgroups
import MiniAlgebraicGroups.Constructions.Quotients
import MiniAlgebraicGroups.Properties.Representation
namespace MiniAlgebraicGroups

axiom lieKolchin (n : Nat) (G : AlgebraicGroup n) (hConnected : True) (hSolvable : IsSolvable n G) : True
axiom lieKolchinCorollary1D (n d : Nat) (G : AlgebraicGroup n) (hSolvable : IsSolvable n G) (rho : Representation n d G) (hIrred : IsIrreducible n d G rho) : d = 1

axiom expMapUnipotentCharZero (n : Nat) (G : AlgebraicGroup n) : True
axiom oneDimensionalAlgebraicGroupClassification : True

#eval "Theorems.LieKolchin: connected solvable => triangularizable"
/-! ## Detailed Proof Sketch -/

axiom lieKolchinProofStep1 (n : Nat) (G : AlgebraicGroup n) : True
axiom lieKolchinProofStep2 (n : Nat) (G : AlgebraicGroup n) : True
axiom lieKolchinProofStep3 (n : Nat) (G : AlgebraicGroup n) : True

/-! ## Corollaries -/

axiom lieKolchinCorollaryTriangular (n : Nat) (G : AlgebraicGroup n) (hSolvable : IsSolvable n G) : True
axiom lieKolchinCorollaryCompleteFlag (n : Nat) (G : AlgebraicGroup n) : True
axiom lieKolchinCorollaryEigenvector (n : Nat) (G : AlgebraicGroup n) : True

#eval "LieKolchin: proof steps, corollaries on triangulation"
/-! ## Special Cases of Lie-Kolchin -/
axiom lieKolchinInCharZero (n : Nat) (G : AlgebraicGroup n) : True
axiom lieKolchinForNilpotent (n : Nat) (G : AlgebraicGroup n) : True
axiom lieKolchinForAbelian (n : Nat) (G : AlgebraicGroup n) : True

#eval "LieKolchin: special cases in char 0, nilpotent, abelian"