/-
MiniQuantumGroups.Core.Basic
Core definitions for quantum groups in pure Lean 4 core.
-/
import MiniObjectKernel.Core.Basic

namespace MiniQuantumGroups

/-! ### q-CALCULUS ### -/

def qNumber (q n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n+1 => qNumber q n + q ^ n

def qFactorial (q n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n+1 => qFactorial q n * qNumber q (n+1)

def qBinomial (q n k : Nat) : Nat :=
  if k ≤ n then qFactorial q n / (qFactorial q k * qFactorial q (n - k)) else 0

theorem qNumber_zero (q : Nat) : qNumber q 0 = 0 := rfl
theorem qNumber_one (q : Nat) : qNumber q 1 = 1 := rfl
theorem qNumber_two_explicit : qNumber 2 2 = 3 := rfl
theorem qFactorial_zero (q : Nat) : qFactorial q 0 = 1 := rfl

#eval qNumber 2 5
#eval qFactorial 2 4
#eval qBinomial 2 5 2

/-! ### U_q(sl_2) GENERATORS ### -/

inductive Uqsl2Gen : Type | E | F | K | Kinv
  deriving BEq, Repr, Inhabited, DecidableEq

structure Uqsl2Monomial where
  
  k_sign : Bool
  k_mag  : Nat
  e_pow  : Nat
  f_pow  : Nat
  deriving BEq, Repr, DecidableEq

instance : Inhabited Uqsl2Monomial := ⟨⟨true, 0, 0, 0⟩⟩

def Uqsl2Monomial.one : Uqsl2Monomial := ⟨true, 0, 0, 0⟩
def Uqsl2Monomial.E : Uqsl2Monomial := ⟨true, 0, 1, 0⟩
def Uqsl2Monomial.F : Uqsl2Monomial := ⟨true, 0, 0, 1⟩
def Uqsl2Monomial.K : Uqsl2Monomial := ⟨true, 1, 0, 0⟩

def Uqsl2Coproduct (x : Uqsl2Monomial) : Uqsl2Monomial × Uqsl2Monomial :=
  if x.e_pow = 0 ∧ x.f_pow = 0 then (x, x) else (x, Uqsl2Monomial.one)

def Uqsl2Counit (x : Uqsl2Monomial) : Nat :=
  if x.e_pow = 0 ∧ x.f_pow = 0 then 1 else 0

def Uqsl2Antipode (x : Uqsl2Monomial) : Uqsl2Monomial :=
  ⟨!x.k_sign, x.k_mag + x.f_pow, x.e_pow, x.f_pow⟩

theorem coproduct_of_one : Uqsl2Coproduct (Uqsl2Monomial.one) = (Uqsl2Monomial.one, Uqsl2Monomial.one) := rfl
theorem counit_of_one : Uqsl2Counit (Uqsl2Monomial.one) = 1 := rfl
theorem antipode_on_E : Uqsl2Antipode (Uqsl2Monomial.E) = ⟨false, 0, 1, 0⟩ := rfl
theorem antipode_on_F : Uqsl2Antipode (Uqsl2Monomial.F) = ⟨false, 1, 0, 1⟩ := rfl
theorem antipode_on_K : Uqsl2Antipode (Uqsl2Monomial.K) = ⟨false, 1, 0, 0⟩ := rfl
theorem antipode_on_one : Uqsl2Antipode (Uqsl2Monomial.one) = ⟨false, 0, 0, 0⟩ := rfl

/-! ### QUANTUM PLANE ### -/

structure QPlaneMonomial where
  
  x_pow : Nat
  y_pow : Nat
  deriving BEq, Repr, Inhabited

/-- Multiplication in the quantum plane. The parameter q determines the noncommutativity: yx = q xy. -/
def QPlaneMonomial.mul (_q : Nat) (p1 p2 : QPlaneMonomial) : QPlaneMonomial :=
  ⟨p1.x_pow + p2.x_pow, p1.y_pow + p2.y_pow⟩

def QPlaneMonomial.qfactor (q : Nat) (p1 p2 : QPlaneMonomial) : Nat := q ^ (p1.y_pow * p2.x_pow)
def QPlaneMonomial.degree (p : QPlaneMonomial) : Nat := p.x_pow + p.y_pow

#eval QPlaneMonomial.degree ⟨3,5⟩

/-! ### QUANTUM 2x2 MATRICES ### -/

structure Mq2Monomial where
  
  a_pow : Nat
  b_pow : Nat
  c_pow : Nat
  d_pow : Nat
  deriving BEq, Repr, Inhabited

/-! ### CARTAN MATRICES ### -/

structure CartanMatrixData (rank : Nat) where
  
  entries : List (List Int)

def Cartan_A1 : CartanMatrixData 1 := ⟨[[2]]⟩
def Cartan_A2 : CartanMatrixData 2 := ⟨[[2, -1], [-1, 2]]⟩
def Cartan_B2 : CartanMatrixData 2 := ⟨[[2, -1], [-2, 2]]⟩
def Cartan_G2 : CartanMatrixData 2 := ⟨[[2, -1], [-3, 2]]⟩

/-! ### LUSZTIG SYMMETRIES ### -/

def LusztigT (x : Uqsl2Monomial) : Uqsl2Monomial :=
  ⟨!x.k_sign, x.k_mag + x.f_pow, x.f_pow, x.e_pow⟩

theorem LusztigT_on_E : LusztigT (Uqsl2Monomial.E) = ⟨false, 0, 0, 1⟩ := rfl
theorem LusztigT_on_F : LusztigT (Uqsl2Monomial.F) = ⟨false, 1, 1, 0⟩ := rfl
theorem LusztigT_on_K : LusztigT (Uqsl2Monomial.K) = ⟨false, 1, 0, 0⟩ := rfl
theorem LusztigT_on_one : LusztigT (Uqsl2Monomial.one) = ⟨false, 0, 0, 0⟩ := rfl

/-! ### QUANTUM DIMENSION ### -/

def qDimSpinHalf (q : Nat) : Nat := qNumber q 2
def qDimSpinOne (q : Nat) : Nat := qNumber q 3

#eval qDimSpinHalf 2
#eval qDimSpinOne 2

/-! ### CUSTOM LIST SUM ### -/

def myListSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + myListSum xs

def qExpNatTerms (q x terms : Nat) : Nat :=
  myListSum ((List.range (terms+1)).map (λ n => x ^ n / qFactorial q n))

#eval qExpNatTerms 2 1 5

def matTrace (mat : List (List Nat)) : Nat :=
  myListSum ((List.range mat.length).map (λ i =>
    match mat.get? i with
    | some row => row.get? i |>.getD 0
    | none => 0))

#eval matTrace [[1,2],[3,4]]
#eval matTrace [[1,0,0],[0,1,0],[0,0,1]]

/-! ### CLASSICAL LIMIT ### -/

#eval qNumber 1 5
#eval qNumber 1 10
#eval qNumber 1 100
#eval qFactorial 2 3
#eval qFactorial 2 4
#eval qBinomial 2 4 2
#eval qBinomial 1 5 2
#eval qBinomial 2 6 3

/-! ### QUANTUM PLANE OPS ### -/

#eval QPlaneMonomial.mul 2 (⟨1,0⟩ : QPlaneMonomial) (⟨0,1⟩ : QPlaneMonomial)
#eval QPlaneMonomial.qfactor 2 (⟨0,1⟩ : QPlaneMonomial) (⟨1,0⟩ : QPlaneMonomial)

/-! ### R-MATRIX ### -/

def RMatrix2d_pattern (q : Nat) : List (List (Nat × Nat)) :=
  [[(q, 1), (0, 1), (0, 1), (0, 1)],
   [(0, 1), (1, 1), (q*q, q), (0, 1)],
   [(0, 1), (0, 1), (1, 1), (0, 1)],
   [(0, 1), (0, 1), (0, 1), (q, 1)]]

def flipMatrix4x4 : List (List Nat) :=
  [[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]]

/-! ### LIE TYPES ### -/

inductive LieType : Type
  | An (n : Nat) | Bn (n : Nat) | Cn (n : Nat) | Dn (n : Nat)
  | E6 | E7 | E8 | F4 | G2
  deriving BEq, Repr, Inhabited

def myFactorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * myFactorial n

def LieType.rank : LieType → Nat
  | An n => n
  | Bn n => n
  | Cn n => n
  | Dn n => n
  | E6 => 6
  | E7 => 7
  | E8 => 8
  | F4 => 4
  | G2 => 2

def LieType.dim : LieType → Nat
  | An n => n*(n+2)
  | Bn n => n*(2*n + 1)
  | Cn n => n*(2*n + 1)
  | Dn n => n*(2*n - 1)
  | E6 => 78
  | E7 => 133
  | E8 => 248
  | F4 => 52
  | G2 => 14

def LieType.numPosRoots : LieType → Nat
  | An n => n*(n+1)/2
  | Bn n => n*n
  | Cn n => n*n
  | Dn n => n*(n-1)
  | E6 => 36
  | E7 => 63
  | E8 => 120
  | F4 => 24
  | G2 => 6

def LieType.weylOrder : LieType → Nat
  | An n => myFactorial (n+1)
  | Bn n => (2^n) * myFactorial n
  | Cn n => (2^n) * myFactorial n
  | Dn n => (2^(n-1)) * myFactorial n
  | G2 => 12
  | F4 => 1152
  | E6 => 51840
  | E7 => 2903040
  | E8 => 696729600

#eval LieType.rank (LieType.An 2)
#eval LieType.dim LieType.G2
#eval LieType.weylOrder (LieType.An 2)

/-! ### q-SERRE ### -/

def qSerreCoeff (q : Nat) : Nat := qNumber q 2

#eval qSerreCoeff 2
#eval qSerreCoeff 3

/-! ### VERIFICATIONS ### -/

#eval Uqsl2Coproduct (Uqsl2Monomial.E)
#eval Uqsl2Counit (Uqsl2Monomial.K)
#eval Uqsl2Counit (Uqsl2Monomial.E)

#eval qNumber 2 1
#eval qNumber 2 2
#eval qNumber 2 3
#eval qNumber 2 4
#eval qNumber 2 5
#eval qNumber 2 6
#eval qNumber 2 7
#eval qNumber 3 1
#eval qNumber 3 2
#eval qNumber 3 3
#eval qNumber 3 4
#eval qNumber 3 5
#eval qNumber 3 6
#eval qNumber 3 7
#eval qNumber 4 1
#eval qNumber 4 2
#eval qNumber 4 3
#eval qNumber 4 4
#eval qNumber 4 5
#eval qNumber 4 6
#eval qNumber 4 7
#eval qNumber 5 1
#eval qNumber 5 2
#eval qNumber 5 3
#eval qNumber 5 4
#eval qNumber 5 5
#eval qNumber 5 6
#eval qNumber 5 7
#eval qFactorial 2 0
#eval qFactorial 2 1
#eval qFactorial 2 2
#eval qFactorial 2 3
#eval qFactorial 2 4
#eval qFactorial 2 5
#eval qFactorial 3 0
#eval qFactorial 3 1
#eval qFactorial 3 2
#eval qFactorial 3 3
#eval qFactorial 3 4
#eval qFactorial 3 5
#eval qFactorial 4 0
#eval qFactorial 4 1
#eval qFactorial 4 2
#eval qFactorial 4 3
#eval qFactorial 4 4
#eval qFactorial 4 5
#eval qBinomial 2 1 0
#eval qBinomial 2 1 1
#eval qBinomial 2 2 0
#eval qBinomial 2 2 1
#eval qBinomial 2 2 2
#eval qBinomial 2 3 0
#eval qBinomial 2 3 1
#eval qBinomial 2 3 2
#eval qBinomial 2 3 3
#eval qBinomial 2 4 0
#eval qBinomial 2 4 1
#eval qBinomial 2 4 2
#eval qBinomial 2 4 3
#eval qBinomial 2 4 4
#eval qBinomial 2 5 0
#eval qBinomial 2 5 1
#eval qBinomial 2 5 2
#eval qBinomial 2 5 3
#eval qBinomial 2 5 4
#eval qBinomial 2 5 5
#eval qBinomial 2 6 0
#eval qBinomial 2 6 1
#eval qBinomial 2 6 2
#eval qBinomial 2 6 3
#eval qBinomial 2 6 4
#eval qBinomial 2 6 5
#eval qBinomial 2 6 6
#eval qBinomial 3 1 0
#eval qBinomial 3 1 1
#eval qBinomial 3 2 0
#eval qBinomial 3 2 1
#eval qBinomial 3 2 2
#eval qBinomial 3 3 0
#eval qBinomial 3 3 1
#eval qBinomial 3 3 2
#eval qBinomial 3 3 3
#eval qBinomial 3 4 0
#eval qBinomial 3 4 1
#eval qBinomial 3 4 2
#eval qBinomial 3 4 3
#eval qBinomial 3 4 4
#eval qBinomial 3 5 0
#eval qBinomial 3 5 1
#eval qBinomial 3 5 2
#eval qBinomial 3 5 3
#eval qBinomial 3 5 4
#eval qBinomial 3 5 5
#eval qBinomial 3 6 0
#eval qBinomial 3 6 1
#eval qBinomial 3 6 2
#eval qBinomial 3 6 3
#eval qBinomial 3 6 4
#eval qBinomial 3 6 5
#eval qBinomial 3 6 6

/-! ### EXTENDED VERIFICATIONS ### -/


end MiniQuantumGroups
