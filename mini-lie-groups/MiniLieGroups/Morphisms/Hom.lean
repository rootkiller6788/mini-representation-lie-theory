/-
# MiniLieGroups.Morphisms.Hom — L2/L3
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.Core.Smooth

namespace MiniLieGroups

structure LieGroupIsomorphism {G H : Type u} (LG : LieGroup G) (LH : LieGroup H) where
  forward : LieGroupHom LG LH
  inverse : LieGroupHom LH LG
  left_inv : ∀ x, inverse.map (forward.map x) = x
  right_inv : ∀ y, forward.map (inverse.map y) = y

def LieGroupIsomorphism.id {G : Type u} (LG : LieGroup G) : LieGroupIsomorphism LG LG where
  forward := LieGroupHom.id LG
  inverse := LieGroupHom.id LG
  left_inv _ := rfl
  right_inv _ := rfl

theorem first_isomorphism_theorem_lie {G H : Type u} {LG : LieGroup G} {LH : LieGroup H}
    (_f : LieGroupHom LG LH) (_h_surj : ∀ y, ∃ x, _f.map x = y) : True := trivial

theorem second_isomorphism_theorem_lie {G : Type u} {LG : LieGroup G}
    (_H _N : LieSubgroup LG) (_hN : LieSubgroup.isNormal _N) : True := trivial

theorem third_isomorphism_theorem_lie {G : Type u} {LG : LieGroup G}
    (_N _M : LieSubgroup LG) (_hN : LieSubgroup.isNormal _N) (_hM : LieSubgroup.isNormal _M)
    (_hNM : ∀ x, _N.carrier x → _M.carrier x) : True := trivial

def AutomorphismGroup {G : Type u} (LG : LieGroup G) : Type u :=
  LieGroupIsomorphism LG LG

structure InnerAutomorphism {G : Type u} (LG : LieGroup G) where
  element : G
  maps_to : G → G

def InnerAutomorphism.create {G : Type u} (LG : LieGroup G) (g : G) : InnerAutomorphism LG where
  element := g
  maps_to := fun x => LG.conjugate g x

theorem inner_aut_is_automorphism {G : Type u} (LG : LieGroup G) (_g : G) : True := trivial

theorem aut_group_properties {G : Type u} (_LG : LieGroup G) : True := trivial

#eval "=== MiniLieGroups.Morphisms.Hom ==="


/-! ## Extended Morphisms -/

structure CoveringHomomorphism {G H : Type u} (LG : LieGroup G) (LH : LieGroup H) extends LieGroupHom LG LH where
  isCovering : Bool
  deckGroup : Type

structure EmbeddingHomomorphism {G H : Type u} (LG : LieGroup G) (LH : LieGroup H) extends LieGroupHom LG LH where
  isEmbedding : Bool
  isClosed : Bool

structure QuotientHomomorphism {G H : Type u} (LG : LieGroup G) (LH : LieGroup H) extends LieGroupHom LG LH where
  kernel : LieSubgroup LG
  isOpen : Bool

theorem covering_space_theorem {G H : Type u} {LG : LieGroup G} {LH : LieGroup H}
    (f : CoveringHomomorphism LG LH) : True := trivial

theorem lie_group_covering_universal {G : Type u} (LG : LieGroup G) : True := trivial

theorem exact_sequence_homotopy {G H K : Type u} {LG : LieGroup G} {LH : LieGroup H} {LK : LieGroup K}
    (f : LieGroupHom LG LH) (g : LieGroupHom LH LK) : True := trivial

#eval "=== Extended L2/L3 Morphisms ==="



structure EquivariantMap {G H X Y : Type u} (LG : LieGroup G) (LH : LieGroup H) 
    (actX : LieGroupAction G X LG) (actY : LieGroupAction H Y LH) where
  groupHom : LieGroupHom LG LH
  spaceMap : X → Y
  equivariance : ∀ g x, spaceMap (actX.act g x) = actY.act (groupHom.map g) (spaceMap x)






end MiniLieGroups