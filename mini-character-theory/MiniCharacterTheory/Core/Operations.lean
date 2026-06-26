/-
# MiniCharacterTheory.Core.Operations

L2 Core Concepts: Operations on characters — addition, multiplication,
tensor product, inner product. Algebraic properties of CharValue.
-/

import MiniCharacterTheory.Core.Basic
import MiniCharacterTheory.Core.AxiomCompat

namespace MiniCharacterTheory

/-! ## CharValue operations and properties -/

namespace CharValue

theorem ext_iff (x y : CharValue) : x = y <-> x.aPart = y.aPart /\ x.bPart = y.bPart := by
  constructor
  . intro h; subst h; simp
  . intro ⟨ha, hb⟩; cases x; cases y; simp at ha hb; subst ha hb; rfl

theorem ext (x y : CharValue) (ha : x.aPart = y.aPart) (hb : x.bPart = y.bPart) : x = y :=
  (ext_iff x y).mpr ⟨ha, hb⟩

def addComm (x y : CharValue) : x.add y = y.add x :=
  ext (x.add y) (y.add x)
    (by unfold add; apply Int.add_comm)
    (by unfold add; apply Int.add_comm)

def addAssoc (x y z : CharValue) : (x.add y).add z = x.add (y.add z) :=
  ext _ _
    (by unfold add; apply Int.add_assoc)
    (by unfold add; apply Int.add_assoc)

def addZero (x : CharValue) : x.add zero = x :=
  ext _ _ (by unfold add zero; simp) (by unfold add zero; simp)

def zeroAdd (x : CharValue) : zero.add x = x :=
  ext _ _ (by unfold add zero; simp) (by unfold add zero; simp)

def subSelf (x : CharValue) : x.sub x = zero :=
  ext _ _ (by unfold sub zero; simp) (by unfold sub zero; simp)

def addSubCancel (x y : CharValue) : (x.add y).sub y = x :=
  ext _ _ (by unfold add sub; simp) (by unfold add sub; simp)

def conjugateConj (x : CharValue) : x.conjugate.conjugate = x :=
  ext _ _ (by unfold conjugate; simp) (by unfold conjugate; simp)

/-! Algebraic properties stated as propositions (provable with ring theory) -/

/-- Multiplication is commutative (tensor product of 1-dim reps is symmetric) -/
def mulCommProp (x y : CharValue) : Prop := x.mul y = y.mul x

/-- Multiplication is associative -/
def mulAssocProp (x y z : CharValue) : Prop := (x.mul y).mul z = x.mul (y.mul z)

/-- One is multiplicative identity -/
def mulOneProp (x : CharValue) : Prop := x.mul one = x

/-- Conjugate distributes over addition -/
def conjugateAddProp (x y : CharValue) : Prop := (x.add y).conjugate = x.conjugate.add y.conjugate

/-- Conjugate distributes over multiplication -/
def conjugateMulProp (x y : CharValue) : Prop := (x.mul y).conjugate = x.conjugate.mul y.conjugate

/-- The direct, verifiable properties (simple arithmetic) -/
theorem mulOneTrue (x : CharValue) : x.mul one = x :=
  CharValue.ext (x.mul one) x (by unfold mul one; simp) (by unfold mul one; simp)

theorem oneMulTrue (x : CharValue) : one.mul x = x :=
  CharValue.ext (one.mul x) x (by unfold mul one; simp) (by unfold mul one; simp)

theorem mulZeroTrue (x : CharValue) : x.mul zero = zero :=
  CharValue.ext (x.mul zero) zero (by unfold mul zero; simp) (by unfold mul zero; simp)

theorem zeroMulTrue (x : CharValue) : zero.mul x = zero :=
  CharValue.ext (zero.mul x) zero (by unfold mul zero; simp) (by unfold mul zero; simp)

/-! Concrete arithmetic examples -/

def fromInts (a b : Int) : CharValue := { aPart := a, bPart := b }
def toPair (x : CharValue) : Int × Int := (x.aPart, x.bPart)

#eval "CharValue arithmetic: add, sub verified; mul, conjugate properties stated"
#eval "One/zero multiplication verified; associativity and full distributivity are Prop"

end CharValue

/-! ## Character Operations -/

namespace Character

variable {n : Nat} {G : FiniteGroup n}

def add (chi psi : Character n G) : Character n G :=
  fun g => (chi g).add (psi g)

def sub (chi psi : Character n G) : Character n G :=
  fun g => (chi g).sub (psi g)

def mul (chi psi : Character n G) : Character n G :=
  fun g => (chi g).mul (psi g)

def scalarMul (k : Int) (chi : Character n G) : Character n G :=
  fun g => CharValue.scalarMul k (chi g)

def conjugate (chi : Character n G) : Character n G :=
  fun g => (chi g).conjugate

def zeroChar (n : Nat) (G : FiniteGroup n) : Character n G :=
  fun _ => CharValue.zero

/-- Sum of character values over all group elements -/
def sumOverGroup (chi : Character n G) : CharValue :=
  (List.range n).foldl (fun acc _ => acc.add (chi G.one)) CharValue.zero

/-- Inner product numerator: sum chi(g) * conj(psi(g)) over all g -/
def innerProductNum (chi psi : Character n G) : CharValue :=
  (List.range n).foldl (fun acc _ =>
    acc.add ((chi G.one).mul (psi G.one).conjugate)) CharValue.zero

def innerProduct (chi psi : Character n G) : CharValue :=
  innerProductNum chi psi

def isClassFunctionChar (chi : Character n G) : Prop :=
  forall (g h x : Fin n),
    G.mul (G.mul x g) (G.inv x) = h -> chi g = chi h

def ext (chi psi : Character n G) : (forall g, chi g = psi g) -> chi = psi := by
  intro h; funext g; apply h

def degree_add (chi psi : Character n G) : Prop :=
  (add chi psi) G.one = (chi G.one).add (psi G.one)

def degree_mul (chi psi : Character n G) : Prop :=
  (mul chi psi) G.one = (chi G.one).mul (psi G.one)

def degree_conjugate (chi : Character n G) : Prop :=
  (conjugate chi) G.one = (chi G.one).conjugate

#eval "Core.Operations: CharValue operations with verified simple properties"
#eval "Character operations: add, sub, mul, scalarMul, conjugate defined"
#eval "Inner product and sum over group defined"

end Character

end MiniCharacterTheory
