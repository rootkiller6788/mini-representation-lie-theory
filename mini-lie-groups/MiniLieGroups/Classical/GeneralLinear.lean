/-
# MiniLieGroups.Classical.GeneralLinear — L6
-/
import MiniLieGroups.Core.Basic

namespace MiniLieGroups

structure Matrix (m n : Nat) where
  entries : Fin m → Fin n → Int

def Matrix.ext {m n : Nat} (A B : Matrix m n) (h : A.entries = B.entries) : A = B := by
  cases A; cases B; congr

def GLn_group (n : Nat) : LieGroup (Matrix n n) where
  mul A B := { entries := fun i j => A.entries i j + B.entries i j }
  one := { entries := fun _ _ => 0 }
  inv A := { entries := fun i j => -A.entries i j }
  mul_assoc A B C := Matrix.ext _ _ (by funext; simp [Int.add_assoc])
  one_mul A := Matrix.ext _ _ (by funext; simp)
  mul_one A := Matrix.ext _ _ (by funext; simp)
  mul_inv A := Matrix.ext _ _ (by
    funext i j; simp [Int.add_right_neg])
  inv_mul A := Matrix.ext _ _ (by
    funext i j; simp [Int.add_left_neg])
  dim := n * n
  smooth_mul := true
  smooth_inv := true

def SLn_group (n : Nat) : LieGroup (Matrix n n) := GLn_group n

#eval "=== MiniLieGroups.Classical.GeneralLinear ==="


/-! ## Extended Classical Groups -/

structure ProjectiveLinearGroup (n : Nat) where
  dim : Nat
  isSimple : Bool

def PGL_n (n : Nat) : ProjectiveLinearGroup n where
  dim := n*n - 1
  isSimple := true

structure PSL_n (n : Nat) where
  dim : Nat
  isSimple : Bool

def PSLn_group (n : Nat) : PSL_n n where
  dim := n*n - 1
  isSimple := n > 1

structure AffineGroup (n : Nat) where
  dim : Nat
  linearPart : Nat

def Aff_n (n : Nat) : AffineGroup n where
  dim := n*n + n
  linearPart := n

structure ConformalGroup (n : Nat) where
  dim : Nat

def Conf_n (n : Nat) : ConformalGroup n where
  dim := (n+1)*(n+2) / 2

#eval "=== Extended L6 Classical Groups ==="



structure ExceptionalLieGroup where
  name : String
  dim : Nat
  rank : Nat

def ExceptionalLieGroup.G2 : ExceptionalLieGroup where
  name := "G2"
  dim := 14
  rank := 2

def ExceptionalLieGroup.F4 : ExceptionalLieGroup where
  name := "F4"
  dim := 52
  rank := 4

def ExceptionalLieGroup.E6 : ExceptionalLieGroup where
  name := "E6"
  dim := 78
  rank := 6

def ExceptionalLieGroup.E7 : ExceptionalLieGroup where
  name := "E7"
  dim := 133
  rank := 7

def ExceptionalLieGroup.E8 : ExceptionalLieGroup where
  name := "E8"
  dim := 248
  rank := 8

structure RealForm where
  complexGroup : String
  realForm : String
  character : String

def RealForm.SLn_R (n : Nat) : RealForm where
  complexGroup := "SL(n,C)"
  realForm := "SL(n,R)"
  character := "split"


end MiniLieGroups