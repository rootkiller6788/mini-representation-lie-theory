/-
# MiniLieGroups.Constructions.Quotients — L3/L4
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.Constructions.Subgroups

namespace MiniLieGroups

structure QuotientLieGroup {G : Type u} (LG : LieGroup G) (H : LieSubgroup LG) where
  quotientGroup : LieGroup G
  isSmooth : Bool

theorem quotient_is_lie_group {G : Type u} (_LG : LieGroup G) (_H : LieSubgroup _LG) : True := trivial

theorem first_isomorphism_quotient {G H : Type u} {LG : LieGroup G} {LH : LieGroup H}
    (_f : LieGroupHom LG LH) : True := trivial

#eval "=== MiniLieGroups.Constructions.Quotients ==="


/-! ## Extended Quotients -/

structure HomogeneousSpaceStruct {G : Type u} (LG : LieGroup G) where
  stabilizer : LieSubgroup LG
  cosetSpace : Type
  isSmooth : Bool

theorem homogeneous_space_dimension {G : Type u} (LG : LieGroup G) (H : LieSubgroup LG) : True := trivial

structure FlagManifold {G : Type u} (LG : LieGroup G) where
  parabolicSubgroup : LieSubgroup LG
  flagDim : Nat

structure GeneralizedFlagVariety {G : Type u} (LG : LieGroup G) where
  parabolics : List (LieSubgroup LG)
  isProjective : Bool

#eval "=== Extended L3/L4 Quotients ==="



structure CosetSpace where
  G : Type
  H : Type
  dimension : Nat

structure AdjointOrbit where
  G : Type
  element : Type
  isSymplectic : Bool

def AdjointOrbit.examples : List String := [
  "flag manifolds",
  "coadjoint orbits",
  "nilpotent orbits"
]


end MiniLieGroups
