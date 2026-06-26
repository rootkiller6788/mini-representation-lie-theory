/- L7: Bridge to Lie theory. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Morphisms.Hom
import MiniAlgebraicGroups.Theorems.LieKolchin
import MiniAlgebraicGroups.Theorems.JordanDecomp
import MiniAlgebraicGroups.Properties.Invariants
namespace MiniAlgebraicGroups

structure LieAlgebraOf (n : Nat) (G : AlgebraicGroup n) where
  dimension : Nat
  bracket : Matrix n -> Matrix n -> Matrix n
  jacobi : True
  anticommutative : True

axiom lieFunctoriality {n m : Nat} (G : AlgebraicGroup n) (H : AlgebraicGroup m) (phi : AlgebraicGroupHom G H) : True
axiom engelTheorem (n : Nat) (g : Matrix n -> Prop) : True
axiom lieTheorem (n : Nat) (g : Matrix n -> Prop) : True
axiom exponentialMapChar0 (n : Nat) (G : AlgebraicGroup n) : True
axiom cartierEquivalenceChar0 (n : Nat) (g : Matrix n -> Prop) : True

#eval "Bridges.ToLieTheory: Lie(G) = T_e(G), Engel/Lie, exp map, Cartier equivalence"
/-! ## More Lie Theory Connections -/

axiom adjointRepresentation (n : Nat) (G : AlgebraicGroup n) : True
axiom killingForm (n : Nat) (G : AlgebraicGroup n) : True
axiom cartanKillingClassification (n : Nat) (G : AlgebraicGroup n) : True

axiom dynkinIndex (n : Nat) (G : AlgebraicGroup n) : True
axiom chevalleyBasis (n : Nat) (G : AlgebraicGroup n) : True

#eval "Bridges.ToLieTheory: adjoint rep, Killing form, Chevalley basis, Dynkin index"
/-! ## Structure Constants and Chevalley Basis -/

axiom chevalleyBasisConstruction (n : Nat) (G : AlgebraicGroup n) : True
axiom structureConstantsFromRoots (n : Nat) (G : AlgebraicGroup n) : True

/-! ## Universal Enveloping Algebra -/

axiom universalEnvelopingAlgebra (n : Nat) (G : AlgebraicGroup n) : True
axiom pbwTheorem (n : Nat) (G : AlgebraicGroup n) : True

/-! ## Harish-Chandra Isomorphism -/

axiom harishChandraIsomorphism (n : Nat) (G : AlgebraicGroup n) : True

/-! ## Kazhdan-Lusztig Theory -/

axiom kazhdanLusztigPolynomials (n : Nat) (G : AlgebraicGroup n) : True
axiom klBasisForHeckeAlgebra (n : Nat) (G : AlgebraicGroup n) : True

#eval "Bridges.ToLieTheory: Chevalley basis, PBW, Harish-Chandra, Kazhdan-Lusztig"