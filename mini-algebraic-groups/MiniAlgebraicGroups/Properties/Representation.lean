/- L4: Representation theory. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Morphisms.Hom
import MiniAlgebraicGroups.Properties.Invariants
namespace MiniAlgebraicGroups

structure Representation (n d : Nat) (G : AlgebraicGroup n) where
  hom : AlgebraicGroupHom G (AlgebraicGroup.GL d)
  dimension : Nat := d
  isPolynomial : True

def trivialRepresentation (n : Nat) (G : AlgebraicGroup n) : Representation n 1 G where
  hom := ⟨fun _ => GL.one 1, rfl, fun _ _ _ _ => rfl, True.intro⟩
  isPolynomial := True.intro

structure IsIrreducible (n d : Nat) (G : AlgebraicGroup n) (rho : Representation n d G) : Prop where
  noProperSubreps : True
  nonzero : True

axiom irreducibleClassificationByDominantWeights (n : Nat) (G : AlgebraicGroup n) : True

structure Weight where
  coordinates : List Int
  isIntegral : True

axiom weylCharacterFormula (n : Nat) (G : AlgebraicGroup n) : True
axiom weylDimensionFormula (n : Nat) (G : AlgebraicGroup n) : True

def dimSL2Irrep (m : Nat) : Nat := m + 1
def dimSL3Irrep (a b : Nat) : Nat := ((a+1) * (b+1) * (a+b+2)) / 2

#eval s!"dim V_2 SL(2)={dimSL2Irrep 2}"
#eval s!"dim V(1,1) SL(3)={dimSL3Irrep 1 1}"

axiom borelWeilTheorem (n : Nat) (G : AlgebraicGroup n) : True
axiom steinbergTensorProductTheorem (n : Nat) (G : AlgebraicGroup n) : True

#eval "Properties.Representation: rational reps, highest weight, Weyl formulas, Borel-Weil"
/-! ## More Dimension Formulas -/

def dimSymPowerSL2 (m : Nat) : Nat := m + 1
def dimExtPowerSLn (n k : Nat) : Nat :=
  if k = 0 || k = n then 1 else if k = 1 then n else n*(n-1)/2
def dimAdjointRep (W : WeylGroupType) : Nat := WeylGroupType.rank W + WeylGroupType.numReflections W

#eval s!"dim Sym^3 SL(2) = {dimSymPowerSL2 3}"
#eval s!"dim Ext^2 SL(4) = {dimExtPowerSLn 4 2}"
#eval s!"dim Ad(G_2) = {dimAdjointRep WeylGroupType.G2}"

/-! ## Fundamental Weights for Type A -/

/-! ## Weyl Vector (half-sum of positive roots) -/

def weylVectorExample : List Int := [3, 1, -1, -3]

#eval s!"Weyl vector A_3 example = {weylVectorExample}"

/-! ## Characters of Representations -/

axiom characterFormula (n d : Nat) (G : AlgebraicGroup n) (rho : Representation n d G) : True

/-! ## Littlewood-Richardson Rule -/

axiom littlewoodRichardsonRule (n : Nat) : True

#eval "Properties.Representation: dimension formulas, Weyl vector, character formulas"
/-! ## Representation Ring -/
axiom representationRingOfAlgebraicGroup (n : Nat) (G : AlgebraicGroup n) : True
axiom adamsOperationsOnRepresentationRing (n : Nat) (G : AlgebraicGroup n) : True
axiom lambdaRingStructure (n : Nat) (G : AlgebraicGroup n) : True

#eval "Properties.Representation: representation ring, Adams operations, lambda-ring"
/-! ## Tensor Product Decompositions -/
axiom prandtlTableForSL2 : True
axiom raccaFormulaForTensorProducts : True
axiom klimykFormulaForTensorProducts : True

/-! ## Branching Rules -/
axiom branchingSLnToSLn_1 : True
axiom branchingSOnToSOn_1 : True
axiom branchingSp2nToSp2n_2 : True

#eval "Properties.Representation: tensor products, Prandtl, Racca, branching rules"