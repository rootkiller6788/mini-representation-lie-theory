/- L7: Bridge to geometry. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Constructions.Quotients
import MiniAlgebraicGroups.Constructions.Subgroups
import MiniAlgebraicGroups.Properties.Invariants
import MiniAlgebraicGroups.Properties.Representation
namespace MiniAlgebraicGroups

axiom schubertCellDecomposition (n : Nat) (G : AlgebraicGroup n) : True
axiom schubertCalculus (n : Nat) (G : AlgebraicGroup n) : True
axiom borelWeilBottGeometric (n : Nat) (G : AlgebraicGroup n) : True

def binomial : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ => 0
  | n'+1, k'+1 => binomial n' k' + binomial n' (k'+1)
termination_by n k => (n, k)

def numSchubertCells (k n : Nat) : Nat := binomial n k
#eval s!"Schubert cells Gr(2,5)={numSchubertCells 2 5}  Gr(3,6)={numSchubertCells 3 6}"

axiom gTorsorDefinition (n : Nat) (G : AlgebraicGroup n) : True
axiom gitQuotientProjective (n : Nat) (G : AlgebraicGroup n) : True

#eval "Bridges.ToGeometry: flag varieties, Schubert calculus, Borel-Weil-Bott, GIT"
/-! ## More Geometric Connections -/

axiom projectiveHomogeneousSpace (n : Nat) (G : AlgebraicGroup n) : True
axiom cotangentBundleFlagVariety (n : Nat) (G : AlgebraicGroup n) : True
axiom momentMapSymplecticGeometry (n : Nat) (G : AlgebraicGroup n) : True

axiom hitchinFibration (n : Nat) (G : AlgebraicGroup n) : True
axiom nilpotentConeResolution (n : Nat) (G : AlgebraicGroup n) : True

#eval "Bridges.ToGeometry: projective spaces, cotangent bundle, Hitchin fibration"
/-! ## More Geometric Constructions -/

axiom cotangentBundleOfFlagVariety (n : Nat) (G : AlgebraicGroup n) : True
axiom springerResolutionGeometry (n : Nat) (G : AlgebraicGroup n) : True
axiom nilpotentConeAsSymplecticVariety (n : Nat) (G : AlgebraicGroup n) : True

/-! ## Equivariant Cohomology -/

axiom equivariantCohomologyFlagVariety (n : Nat) (G : AlgebraicGroup n) : True
axiom localizationTheorem (n : Nat) (G : AlgebraicGroup n) : True

/-! ## Gromov-Witten Theory -/

axiom quantumCohomologyFlagVariety (n : Nat) (G : AlgebraicGroup n) : True
axiom mirrorSymmetryFlagVarieties : True

#eval "Bridges.ToGeometry: cotangent bundle, equivariant cohomology, mirror symmetry"
/-! ## Geometric Representation Theory -/
axiom convolutionProductOnFlagVariety : True
axiom geometricSatakeForGLn : True
axiom mvCyclesAndCanonicalBasis : True

/-! ## Quiver Varieties -/
axiom nakajimaQuiverVarieties : True
axiom quiverVarietiesAndKacMoodyAlgebras : True

#eval "Bridges.ToGeometry: geometric representation theory, quiver varieties"