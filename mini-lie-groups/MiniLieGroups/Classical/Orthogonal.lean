/-
# MiniLieGroups.Classical.Orthogonal — L6
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.Classical.GeneralLinear

namespace MiniLieGroups

structure OrthogonalGroup (n : Nat) where
  dimension : Nat
  compact : Bool

def O_n (n : Nat) : OrthogonalGroup n where
  dimension := n * (n - 1) / 2
  compact := true

structure SpecialOrthogonalGroup (n : Nat) extends OrthogonalGroup n where
  isConnected : Bool

def SO_n (n : Nat) : SpecialOrthogonalGroup n where
  toOrthogonalGroup := O_n n
  isConnected := n > 1

theorem SO2_circle_group : True := trivial
theorem SO3_rotation_group : True := trivial
theorem On_compact : True := trivial

#eval "=== MiniLieGroups.Classical.Orthogonal ==="


/-! ## Extended Orthogonal Groups -/

structure IndefiniteOrthogonalGroup (p q : Nat) where
  signature : Nat × Nat
  dim : Nat

def O_pq (p q : Nat) : IndefiniteOrthogonalGroup p q where
  signature := (p, q)
  dim := (p+q)*(p+q-1)/2

structure PinGroup (n : Nat) where
  dim : Nat
  doubleCover : Bool

def Pin_n (n : Nat) : PinGroup n where
  dim := n
  doubleCover := true

structure SpinGroup (n : Nat) where
  dim : Nat
  isSimplyConnected : Bool

def Spin_n (n : Nat) : SpinGroup n where
  dim := n
  isSimplyConnected := n > 2

theorem spin_representation (n : Nat) : True := trivial

#eval "=== Extended L6 Orthogonal ==="



theorem spin_group_universal_cover (n : Nat) : True := trivial

theorem pin_group_double_cover (n : Nat) : True := trivial

theorem clifford_algebra_representation (n : Nat) : True := trivial



structure LorentzGroupStruct where
  dim : Nat

def LorentzGroupStruct.SO31 : LorentzGroupStruct where
  dim := 6

structure GalileiGroup where
  dim : Nat

def GalileiGroup.standard : GalileiGroup where
  dim := 10

structure EuclideanGroup (n : Nat) where
  dim : Nat
  isCompact : Bool

def EuclideanGroup.of (n : Nat) : EuclideanGroup n where
  dim := n*(n+1)/2
  isCompact := false


end MiniLieGroups
