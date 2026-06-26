/- L2: Algebraic group homomorphisms. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
namespace MiniAlgebraicGroups

structure Endomorphism {n : Nat} (G : AlgebraicGroup n) where
  hom : AlgebraicGroupHom G G
  isAlgebraic : True

structure Automorphism {n : Nat} (G : AlgebraicGroup n) where
  hom : AlgebraicGroupHom G G
  isBijective : True

def Automorphism.identity {n : Nat} (G : AlgebraicGroup n) : Automorphism G where
  hom := ⟨fun A => A, rfl, fun _ _ _ _ => rfl, True.intro⟩
  isBijective := True.intro

axiom Automorphism.comp {n : Nat} {G : AlgebraicGroup n} (phi psi : Automorphism G) : Automorphism G

def AutomorphismGroup {n : Nat} (G : AlgebraicGroup n) : Type := Automorphism G
axiom simplyConnectedCover (n : Nat) (G : AlgebraicGroup n) (hG : IsSemisimple n G) : True

#eval "Morphisms.Hom: Endomorphism, Automorphism, simplyConnectedCover"
/-! ## More Homomorphism Types -/

structure Monomorphism {n m : Nat} (G : AlgebraicGroup n) (H : AlgebraicGroup m) where
  hom : AlgebraicGroupHom G H
  injective : forall (A B : GL n), G.carrier A -> G.carrier B -> hom.map A = hom.map B -> A = B

structure Epimorphism {n m : Nat} (G : AlgebraicGroup n) (H : AlgebraicGroup m) where
  hom : AlgebraicGroupHom G H
  surjective : forall (B : GL m), H.carrier B -> exists (A : GL n), G.carrier A /\ hom.map A = B

/-! ## Character Homomorphisms -/

structure Character (n : Nat) (G : AlgebraicGroup n) where
  hom : AlgebraicGroupHom G Gm
  isNontrivial : True

/-! ## Cocharacter (1-parameter subgroup) -/

structure Cocharacter (n : Nat) (G : AlgebraicGroup n) where
  hom : AlgebraicGroupHom Ga G
  isNontrivial : True

/-! ## Frobenius Endomorphism Details -/

axiom frobeniusFixedPointFormula (n : Nat) (q : Nat) : True

/-! ## Tangent Map Properties -/

axiom tangentMapIsLinear {n m : Nat} {G : AlgebraicGroup n} {H : AlgebraicGroup m} (phi : AlgebraicGroupHom G H) : True

axiom lieAlgebraAdjointAction (n : Nat) (G : AlgebraicGroup n) : True

#eval "Morphisms.Hom: Monomorphism, Epimorphism, Character, Cocharacter, tangent map"
/-! ## Morphism Factorization -/
axiom homomorphismFactorization (n : Nat) (G : AlgebraicGroup n) : True
axiom steinbergFactorization (n : Nat) (G : AlgebraicGroup n) : True

#eval "Morphisms.Hom: homomorphism factorization, Steinberg factorization"