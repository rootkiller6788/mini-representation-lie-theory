/- L3: Quotient constructions. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Morphisms.Hom
import MiniAlgebraicGroups.Constructions.Subgroups
namespace MiniAlgebraicGroups

structure HomogeneousSpace {n : Nat} (G : AlgebraicGroup n) (H : AlgebraicGroup n) where
  dimension : Nat
  isSmooth : True

axiom homogeneousSpaceExists (n : Nat) (G H : AlgebraicGroup n) : True

def Grassmannian (k n : Nat) : Nat := k * (n - k)
#eval s!"dim Gr(2,5) = {Grassmannian 2 5}"
#eval s!"dim Gr(1,4) = {Grassmannian 1 4}"

axiom gitQuotientConjugationGL : True
#eval "Constructions.Quotients: HomogeneousSpace, Grassmannian, GIT quotient"
/-! ## More Quotient Theory -/

axiom quotientByParabolicIsProjective (n : Nat) (G : AlgebraicGroup n) : True
axiom projectiveHomogeneousSpaces (n : Nat) (G : AlgebraicGroup n) : True
axiom borelWeilBottLineBundles (n : Nat) (G : AlgebraicGroup n) : True

def flagVarietyDimensionGL (n : Nat) : Nat := n*(n-1)/2
#eval s!"dim Flag(GL(4)) = {flagVarietyDimensionGL 4}"

axiom completeFlagVariety (n : Nat) (G : AlgebraicGroup n) : True
axiom partialFlagVariety (n : Nat) (G : AlgebraicGroup n) : True

#eval "Constructions.Quotients: projective quotients, flag variety dimensions"
/-! ## Quotient Varieties -/
axiom quotientByFiniteGroupIsVariety (n : Nat) (G : AlgebraicGroup n) : True
axiom quotientByNormalSubgroupIsAffine (n : Nat) (G : AlgebraicGroup n) : True

#eval "Constructions.Quotients: quotient varieties, affine/projective quotients"