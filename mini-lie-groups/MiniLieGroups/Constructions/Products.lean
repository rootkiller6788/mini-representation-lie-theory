/-
# MiniLieGroups.Constructions.Products — L3/L4
-/
import MiniLieGroups.Core.Basic

namespace MiniLieGroups

structure ProductLieGroup {G H : Type u} (LG : LieGroup G) (LH : LieGroup H) where
  productGroup : LieGroup (G × H)
  projL : LieGroupHom (productGroup) LG
  projR : LieGroupHom (productGroup) LH

structure SemidirectProduct {G H : Type u} (LG : LieGroup G) (LH : LieGroup H) where
  action : G → H → H
  productGroup : LieGroup (G × H)
  isSmooth : Bool

private def mkProductGroup {G H : Type u} (LG : LieGroup G) (LH : LieGroup H) : LieGroup (G × H) :=
  {
    mul := fun p q => (LG.mul p.1 q.1, LH.mul p.2 q.2)
    one := (LG.one, LH.one)
    inv := fun p => (LG.inv p.1, LH.inv p.2)
    mul_assoc := by
      intro p q r
      apply Prod.ext
      · exact LG.mul_assoc p.1 q.1 r.1
      · exact LH.mul_assoc p.2 q.2 r.2
    one_mul := by
      intro p
      apply Prod.ext
      · exact LG.one_mul p.1
      · exact LH.one_mul p.2
    mul_one := by
      intro p
      apply Prod.ext
      · exact LG.mul_one p.1
      · exact LH.mul_one p.2
    mul_inv := by
      intro p
      apply Prod.ext
      · exact LG.mul_inv p.1
      · exact LH.mul_inv p.2
    inv_mul := by
      intro p
      apply Prod.ext
      · exact LG.inv_mul p.1
      · exact LH.inv_mul p.2
    dim := LG.dim + LH.dim
    smooth_mul := LG.smooth_mul && LH.smooth_mul
    smooth_inv := LG.smooth_inv && LH.smooth_inv
  }

def productLieGroup {G H : Type u} (LG : LieGroup G) (LH : LieGroup H) :
    ProductLieGroup LG LH where
  productGroup := mkProductGroup LG LH
  projL := { map := Prod.fst, map_mul := fun _ _ => rfl, smooth := true }
  projR := { map := Prod.snd, map_mul := fun _ _ => rfl, smooth := true }

#eval "=== MiniLieGroups.Constructions.Products ==="


/-! ## Extended Products -/

structure DirectProductLieGroup {G H : Type u} (LG : LieGroup G) (LH : LieGroup H) where
  group : LieGroup (G × H)
  isDirect : Bool

structure FreeProductLieGroup {G H : Type u} (LG : LieGroup G) (LH : LieGroup H) where
  words : Type
  isFree : Bool

structure AmalgamatedProduct {G H K : Type u} (LG : LieGroup G) (LH : LieGroup H) (LK : LieGroup K) where
  product : Type
  amalgamatedOver : K
  isSmooth : Bool

structure WreathProduct {G H : Type u} (LG : LieGroup G) (LH : LieGroup H) where
  base : LieGroup (List G)
  action : H → (List G → List G)

#eval "=== Extended L3/L4 Products ==="


end MiniLieGroups