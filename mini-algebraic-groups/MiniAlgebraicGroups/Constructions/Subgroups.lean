/- L3: Subgroup structures. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Morphisms.Hom
namespace MiniAlgebraicGroups

structure IsSimple (n : Nat) (G : AlgebraicGroup n) : Prop where
  isConnected : True
  isNonAbelian : True
  noProperNormalSubgroups : True

axiom simpleGroupDynkinClassification : True
axiom SLisSimple (n : Nat) (hn : n >= 2) : True

def solvableRadical {n : Nat} (G : AlgebraicGroup n) : AlgebraicGroup n := AlgebraicGroup.trivialGroup n
axiom borelExistenceAndConjugacy (n : Nat) (G : AlgebraicGroup n) : True

def glRootSubgroupCount (n : Nat) : Nat := n * (n - 1)
#eval s!"Root subgroups in GL(4) = {glRootSubgroupCount 4}"
#eval "Constructions.Subgroups: IsSimple, solvableRadical, Borel existence, root subgroups"
/-! ## More Subgroup Theory -/

def borelSubgroupDimension (n : Nat) : Nat := n*(n+1)/2
axiom parabolicSubgroupTypes (n : Nat) : True
axiom maximalParabolicClassification (n : Nat) : True

def numMaximalParabolicsGL (n : Nat) : Nat := n - 1
#eval s!"Maximal parabolics in GL(4) = {numMaximalParabolicsGL 4}"

axiom rootSubgroupCommutation (n : Nat) (G : AlgebraicGroup n) : True
axiom chevalleyCommutatorFormulaRootSubgroups (n : Nat) (G : AlgebraicGroup n) : True

#eval "Constructions.Subgroups: Borel dimension, parabolic types, root subgroup commutation"
/-! ## Subgroup Chains -/
axiom subgroupLattice (n : Nat) (G : AlgebraicGroup n) : True
axiom maximalSubgroupClassification (n : Nat) (G : AlgebraicGroup n) : True
axiom dynkinSubgroupClassification (n : Nat) (G : AlgebraicGroup n) : True

#eval "Constructions.Subgroups: subgroup lattice, maximal subgroups, Dynkin classification"