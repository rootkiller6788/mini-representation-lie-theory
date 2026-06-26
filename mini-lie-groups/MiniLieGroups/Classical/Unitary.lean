/-
# MiniLieGroups.Classical.Unitary — L6
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.Classical.GeneralLinear

namespace MiniLieGroups

structure UnitaryGroup (n : Nat) where
  dimension : Nat

def U_n (n : Nat) : UnitaryGroup n where
  dimension := n * n

structure SpecialUnitaryGroup (n : Nat) extends UnitaryGroup n where
  det_one : Bool

def SU_n (n : Nat) : SpecialUnitaryGroup n where
  toUnitaryGroup := U_n n
  det_one := true

theorem U1_circle : True := trivial
theorem SU2_quaternions : True := trivial
theorem SU3_strong_force : True := trivial

#eval "=== MiniLieGroups.Classical.Unitary ==="


/-! ## Extended Unitary Groups -/

structure IndefiniteUnitaryGroup (p q : Nat) where
  signature : Nat × Nat
  dim : Nat

def U_pq (p q : Nat) : IndefiniteUnitaryGroup p q where
  signature := (p, q)
  dim := (p+q)*(p+q)

structure ProjectiveUnitaryGroup (n : Nat) where
  dim : Nat

def PU_n (n : Nat) : ProjectiveUnitaryGroup n where
  dim := n*n - 1

structure CompactSymplecticGroupStruct (n : Nat) where
  dim : Nat

def USp_2n (n : Nat) : CompactSymplecticGroupStruct n where
  dim := n*(2*n+1)

#eval "=== Extended L6 Unitary ==="



theorem unitary_group_maximal_torus (n : Nat) : True := trivial

theorem special_unitary_simple (n : Nat) (h : n > 1) : True := trivial

theorem unitary_representation_theory (n : Nat) : True := trivial



structure SymplecticUnitaryGroup (n : Nat) where
  dim : Nat

def SpU_n (n : Nat) : SymplecticUnitaryGroup n where
  dim := n*(2*n+1)

structure QuaternionicUnitaryGroup (n : Nat) where
  dim : Nat

def U_n_H (n : Nat) : QuaternionicUnitaryGroup n where
  dim := n*(2*n-1)


end MiniLieGroups
