/-
# MiniLieGroups.Proofs.Techniques — L5: 3 proof methods
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.LieAlgebra.Definition

namespace MiniLieGroups

theorem identity_unique_equational {G : Type u} (LG : LieGroup G) (e : G)
    (h : ∀ x, LG.mul e x = x) : e = LG.one := by
  calc
    e = LG.mul e LG.one := by rw [LG.mul_one]
    _ = LG.one := by rw [h LG.one]

theorem inverse_unique_equational {G : Type u} (LG : LieGroup G) (a b : G)
    (h : LG.mul a b = LG.one) : b = LG.inv a :=
  LG.inv_unique a b h

theorem power_add_induction {G : Type u} (LG : LieGroup G) (g : G) (m n : Nat)
    : LG.mul (LieGroup.power LG g m) (LieGroup.power LG g n)
      = LieGroup.power LG g (m + n) := by
  induction m with
  | zero => simp [LieGroup.power, LG.one_mul]
  | succ m ih =>
    simp [LieGroup.power, LG.mul_assoc, ih, Nat.succ_add]

theorem quotient_map_well_defined {G H : Type u} {LG : LieGroup G} {LH : LieGroup H}
    (f : LieGroupHom LG LH) (x y : G) (hker : LieGroupHom.ker f (LG.mul x (LG.inv y))) :
    f.map x = f.map y := by
  dsimp [LieGroupHom.ker] at hker
  have h : LH.mul (f.map x) (LH.inv (f.map y)) = LH.one := by
    calc
      LH.mul (f.map x) (LH.inv (f.map y))
          = f.map (LG.mul x (LG.inv y)) := by rw [f.map_mul, LieGroupHom.map_inv f y]
      _ = LH.one := hker
  have hcalc : LH.mul (LH.mul (f.map x) (LH.inv (f.map y))) (f.map y)
              = LH.mul LH.one (f.map y) := by rw [h]
  calc
    f.map x = LH.mul (f.map x) LH.one := by rw [LH.mul_one]
    _ = LH.mul (f.map x) (LH.mul (LH.inv (f.map y)) (f.map y)) := by rw [LH.inv_mul]
    _ = LH.mul (LH.mul (f.map x) (LH.inv (f.map y))) (f.map y) := by rw [← LH.mul_assoc]
    _ = LH.mul LH.one (f.map y) := by rw [hcalc]
    _ = f.map y := by rw [LH.one_mul]

#eval "=== MiniLieGroups.Proofs.Techniques ==="













end MiniLieGroups
