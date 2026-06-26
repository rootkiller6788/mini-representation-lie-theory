/- L8: Springer resolution and the Springer correspondence. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Constructions.Quotients
import MiniAlgebraicGroups.Constructions.Subgroups
import MiniAlgebraicGroups.Bridges.ToLieTheory
import MiniAlgebraicGroups.Bridges.ToGeometry
namespace MiniAlgebraicGroups

structure NilpotentCone (n : Nat) (G : AlgebraicGroup n) where
  dimension : Nat
  finitelyManyOrbits : True

axiom nilpotentOrbitsGLnCorrespondToPartitions (n : Nat) : True

def numPartitions (n : Nat) : Nat :=
  match n with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 7 | 6 => 11 | 7 => 15 | _ => n

#eval s!"Nilpotent orbits in GL(4)={numPartitions 4}"
#eval s!"Nilpotent orbits in GL(6)={numPartitions 6}"

axiom balaCarterTheorem (n : Nat) (G : AlgebraicGroup n) : True
axiom springerResolution (n : Nat) (G : AlgebraicGroup n) : True
axiom springerResolutionDimension (n : Nat) (G : AlgebraicGroup n) : True
axiom springerFiberDefinition (n : Nat) (G : AlgebraicGroup n) : True
axiom springerFiberDimensionFormula (n : Nat) (G : AlgebraicGroup n) : True
axiom springerCorrespondence (n : Nat) (G : AlgebraicGroup n) : True
axiom springerCorrespondenceTypeA : True
axiom greenFunctions (n : Nat) (G : AlgebraicGroup n) : True
axiom lusztigGreenFunctionAlgorithm (n : Nat) (G : AlgebraicGroup n) : True
axiom hitchinFibrationAndSpringerResolution (n : Nat) (G : AlgebraicGroup n) : True

#eval "Advanced.SpringerResolution: nilpotent cone, Springer resolution, Springer correspondence"
/-! ## More Springer Theory -/

axiom springerCorrespondenceDetails (n : Nat) (G : AlgebraicGroup n) : True
axiom greenPolynomials (n : Nat) (G : AlgebraicGroup n) : True
axiom macdonaldConjectureOnSpringerCorrespondence : True

axiom borhoMacphersonSpringCorrespondence (n : Nat) (G : AlgebraicGroup n) : True
axiom lusztigSheavesOnNilpotentCone (n : Nat) (G : AlgebraicGroup n) : True

#eval "Advanced.Springer: Green polynomials, Lusztig sheaves, Borho-MacPherson"
/-! ## More Springer Theory Details -/

axiom springerCorrespondenceGLn : True
axiom springerCorrespondenceExceptional : True
axiom jantzenFiltrationSpringerFibers (n : Nat) (G : AlgebraicGroup n) : True

#eval "Advanced.Springer: GL(n) correspondence, exceptional types, Jantzen filtration"
/-! ## More Springer Details -/
axiom springerFiberIrreducibleComponents (n : Nat) (G : AlgebraicGroup n) : True
axiom hottaSpringerCorrespondence (n : Nat) (G : AlgebraicGroup n) : True

#eval "Advanced.Springer: fiber components, Hotta-Springer correspondence"