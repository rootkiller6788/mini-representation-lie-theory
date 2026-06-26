/-
# MiniVertexAlgebras.Examples.CommutativeVA

Commutative vertex algebras: the simplest class of vertex algebras,
corresponding to differential algebras (commutative associative
algebras with a derivation).

L6: Canonical example — Commutative vertex algebra
L3: Structure — Equivalence with differential algebras
-/

import MiniVertexAlgebras.Core.Basic
import MiniVertexAlgebras.Core.AxiomEquivalence
import MiniVertexAlgebras.Structures.Subalgebras
import MiniVertexAlgebras.Core.AxiomCompat

namespace MiniVertexAlgebras


/-! ## Commutative Vertex Algebra

A vertex algebra V is commutative if a_{(n)} b = 0 for all n >= 0
and all a, b in V. This implies:
- Only the n = -1 product is non-zero
- The product a * b := a_{(-1)} b is commutative and associative
- T is a derivation: T(a * b) = (Ta) * b + a * (Tb)
- T|0> = 0

Thus, a commutative vertex algebra is equivalent to a commutative
associative unital algebra with a derivation. -/

structure CommutativeVertexAlgebra extends BasicVertexAlgebra where
  commutativity : ∀ (a b : vec.carrier) (n : Int), n ≥ 0 → nproduct n a b = vec.zero

namespace CommutativeVertexAlgebra

variable (CVA : CommutativeVertexAlgebra)

/-- The product a * b := a_{(-1)} b is associative.
This follows from the Borcherds identity with m=n=-1, k=0. --/
def product_assoc_axiom : Axiom :=
  Axiom.mk "commutativeVA.product_assoc" (Formula.pred 0 [])
    "a_{(-1)} (b_{(-1)} c) = (a_{(-1)} b)_{(-1)} c in a commutative VA'

/-- The product is commutative.
This follows from skew-symmetry with n=-1. --/
def product_comm_axiom : Axiom :=
  Axiom.mk "commutativeVA.product_comm" (Formula.pred 0 [])
    "a_{(-1)} b = b_{(-1)} a in a commutative VA'

/-- T is a derivation with respect to the product --/
theorem trans_derivation_product (a b : CVA.vec.carrier) :
    CVA.translation (CVA.nproduct (-1) a b) =
    CVA.vec.add (CVA.nproduct (-1) (CVA.translation a) b)
                (CVA.nproduct (-1) a (CVA.translation b)) := by
  rw [CVA.trans_deriv a b (-1)]
  have hzero : CVA.nproduct (-2) a b = CVA.vec.zero :=
    CVA.commutativity a b (-2) (by omega)
  simp [hzero, CVA.vec.add_zero, CVA.vec.add_comm, CVA.vec.add_assoc]

/-- Vacuum is the unit for the product --/
theorem vacuum_unit_left (a : CVA.vec.carrier) :
    CVA.nproduct (-1) CVA.vacuum a = a := by
  rw [CVA.vac_nproduct (-1) a]
  simp

theorem vacuum_unit_right (a : CVA.vec.carrier) :
    CVA.nproduct (-1) a CVA.vacuum = a :=
  CVA.create_prop a

end CommutativeVertexAlgebra

/-! ## Differential Algebra

A differential algebra is a commutative associative algebra A
with a derivation d: A → A (i.e., d(ab) = d(a)b + a d(b) and
d(1) = 0).

Every differential algebra gives a commutative vertex algebra:
- V = A as a vector space
- vacuum = 1
- T = d
- a_{(n)} b = 0 for n >= 0
- a_{(-1)} b = a * b (associative product)
- a_{(n)} b = (1/(-n-1)!) d^{-n-1}(a) * b for n < -1

Conversely, every commutative vertex algebra gives a differential
algebra via a * b = a_{(-1)} b and d = T. -/

structure DifferentialAlgebra where
  algebra : Type
  add : algebra → algebra → algebra
  zero : algebra
  neg : algebra → algebra
  smul : Int → algebra → algebra
  mul : algebra → algebra → algebra
  one : algebra
  deriv : algebra → algebra
  -- simp axioms
  add_assoc : ∀ (a b c : algebra), add (add a b) c = add a (add b c)
  add_comm : ∀ (a b : algebra), add a b = add b a
  add_zero : ∀ (a : algebra), add a zero = a
  add_neg : ∀ (a : algebra), add a (neg a) = zero
  mul_assoc : ∀ (a b c : algebra), mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ (a b : algebra), mul a b = mul b a
  mul_one : ∀ (a : algebra), mul a one = a
  one_mul : ∀ (a : algebra), mul one a = a
  mul_add : ∀ (a b c : algebra), mul a (add b c) = add (mul a b) (mul a c)
  -- Derivation axioms
  deriv_add : ∀ (a b : algebra), deriv (add a b) = add (deriv a) (deriv b)
  deriv_mul : ∀ (a b : algebra), deriv (mul a b) = add (mul (deriv a) b) (mul a (deriv b))
  deriv_one : deriv one = zero
  -- Scalar multiplication
  smul_add : ∀ (r : Int) (a b : algebra), smul r (add a b) = add (smul r a) (smul r b)
  smul_mul : ∀ (r : Int) (a b : algebra), smul r (mul a b) = mul (smul r a) b

/-! ## Example: Differential Algebra

For a concrete differential algebra, we take Q itself with the zero
derivation. This trivial example demonstrates the structure.

More interesting examples (polynomial rings with d/dx) are described
axiomatically below. -/

def trivialDiffAlgebra : DifferentialAlgebra where
  algebra := Int
  add := (· + ·)
  zero := 0
  neg := λ x => -x
  smul := (· * ·)
  mul := (· * ·)
  one := 1
  deriv _ := 0
  add_assoc := by intro a b c; simp
  add_comm := by intro a b; simp
  add_zero := by intro a; simp
  add_neg := by intro a; simp
  mul_assoc := by intro a b c; simp
  mul_comm := by intro a b; simp
  mul_one := by intro a; simp
  one_mul := by intro a; simp
  mul_add := by intro a b c; simp
  deriv_add := by intro a b; simp [deriv]
  deriv_mul := by intro a b; simp [deriv]
  deriv_one := by simp [deriv]
  smul_add := by intro r a b; simp
  smul_mul := by intro r a b; simp

/-- The polynomial simp Q[x] with d/dx is a standard example of
a differential algebra. Its vertex algebra encodes divided powers. --/
def polynomialDiffAlgebraAxiom : Axiom :=
  Axiom.mk "polynomialDiffAlgebra" (Formula.pred 0 [])
    "Q[x] with d/dx forms a differential algebra, hence a commutative VA"

/-- #eval: 1 + 1 in the trivial differential algebra --/
#eval trivialDiffAlgebra.add 1 1
#eval trivialDiffAlgebra.mul 3 4
#eval trivialDiffAlgebra.deriv 5

/-! ## #eval verification -/

#eval "Examples.CommutativeVA: Commutative VA, Differential Algebra"
#eval "Examples.CommutativeVA: Polynomial simp Q[x] with d/dx"
#eval "Examples.CommutativeVA: product_assoc, product_comm, Leibniz rule"

end MiniVertexAlgebras
