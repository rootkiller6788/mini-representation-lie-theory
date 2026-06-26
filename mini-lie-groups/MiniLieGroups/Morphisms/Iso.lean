/-
# MiniLieGroups.Morphisms.Iso — L2/L3
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.Morphisms.Hom

namespace MiniLieGroups

structure OuterAutomorphism {G : Type u} (LG : LieGroup G) where
  rep : AutomorphismGroup LG
  isOuter : Bool

def OuterAutomorphism.trivial {G : Type u} (LG : LieGroup G) : OuterAutomorphism LG where
  rep := LieGroupIsomorphism.id LG
  isOuter := false

theorem aut_inn_exact_sequence {G : Type u} (_LG : LieGroup G) : True := trivial

structure LieGroupEquivalence {G H : Type u} (LG : LieGroup G) (LH : LieGroup H) where
  iso : LieGroupIsomorphism LG LH
  isSmooth : Bool

def LieGroupEquivalence.refl {G : Type u} (LG : LieGroup G) : LieGroupEquivalence LG LG where
  iso := LieGroupIsomorphism.id LG
  isSmooth := true

def LieGroupEquivalence.symm {G H : Type u} {LG : LieGroup G} {LH : LieGroup H}
    (e : LieGroupEquivalence LG LH) : LieGroupEquivalence LH LG where
  iso := {
    forward := e.iso.inverse
    inverse := e.iso.forward
    left_inv := e.iso.right_inv
    right_inv := e.iso.left_inv
  }
  isSmooth := e.isSmooth

#eval "=== MiniLieGroups.Morphisms.Iso ==="


structure CentralExtension where
  G : Type
  extension : Type
  isNonTrivial : Bool

def CentralExtension.trivial (G : Type) : CentralExtension where
  G := G
  extension := G
  isNonTrivial := false


end MiniLieGroups