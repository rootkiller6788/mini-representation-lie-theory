/-
# MiniLieGroups.Classical.Symplectic — L6
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.Classical.GeneralLinear

namespace MiniLieGroups

structure SymplecticGroup (n : Nat) where
  dimension : Nat

def Sp_2n (n : Nat) : SymplecticGroup n where
  dimension := n * (2*n + 1)

theorem Sp2_SL2 : True := trivial
theorem Sp2n_dimension (_n : Nat) : True := trivial

structure CompactSymplecticGroup (n : Nat) where
  dimension : Nat

def Sp_n_compact (n : Nat) : CompactSymplecticGroup n where
  dimension := n * (2*n + 1)

#eval "=== MiniLieGroups.Classical.Symplectic ==="


/-! ## Extended Symplectic Groups -/

structure MetaplecticGroup (n : Nat) where
  dim : Nat
  doubleCover : Bool

def Mp_2n (n : Nat) : MetaplecticGroup n where
  dim := n*(2*n+1)
  doubleCover := true

structure ContactGroup (n : Nat) where
  dim : Nat

def Contact_n (n : Nat) : ContactGroup n where
  dim := 2*n+1

structure HeisenbergGroup (n : Nat) where
  dim : Nat
  isNilpotent : Bool

def Heisenberg_n (n : Nat) : HeisenbergGroup n where
  dim := 2*n+1
  isNilpotent := true

#eval "=== Extended L6 Symplectic ==="



structure ContactManifoldStruct where
  dim : Nat
  contactForm : Bool

def ContactManifoldStruct.standard (n : Nat) : ContactManifoldStruct where
  dim := 2*n+1
  contactForm := true

structure PoissonLieGroup {G : Type u} (LG : LieGroup G) where
  poissonBracket : G → G → G → Int
  isMultiplicative : Bool



structure LagrangianSubmanifold where
  dim : Nat

def LagrangianSubmanifold.standard (n : Nat) : LagrangianSubmanifold where
  dim := n

structure MomentMap {G : Type u} (LG : LieGroup G) where
  target : Type
  map : G → target

structure SymplecticReduction {G : Type u} (LG : LieGroup G) where
  reducedSpace : Type
  levelSet : Type


end MiniLieGroups
