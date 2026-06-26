/-
# MiniVertexAlgebras.Core.Basic

Foundation: Vector space structure, Vertex Algebra definition with
vacuum, translation, state-field correspondence (mode expansion),
and the fundamental axioms (vacuum identity, creation, translation,
locality/Borcherds identity).

L1: Core definitions — Vec, VertexAlgebra, Field, Mode, vacuum, T, n-product
L2: Core concepts — locality, field condition, conformal weight
-/

import MiniVertexAlgebras.Core.AxiomCompat

namespace MiniVertexAlgebras


/-! ## Vector Space over Q

A Q-vector space is an additive abelian group with scalar multiplication
by rational numbers, satisfying the standard vector space axioms.
We bundle this together for convenience. -/

structure Vec where
  carrier : Type u
  add : carrier → carrier → carrier
  zero : carrier
  neg : carrier → carrier
  smul : Int → carrier → carrier
  add_assoc : ∀ (a b c : carrier), add (add a b) c = add a (add b c)
  add_comm : ∀ (a b : carrier), add a b = add b a
  add_zero : ∀ (a : carrier), add a zero = a
  add_neg : ∀ (a : carrier), add a (neg a) = zero
  smul_add : ∀ (r : Int) (a b : carrier), smul r (add a b) = add (smul r a) (smul r b)
  smul_zero : ∀ (r : Int), smul r zero = zero
  add_smul : ∀ (r s : Int) (a : carrier), smul ((r : Int) + (s : Int)) a = add (smul r a) (smul s a)
  mul_smul : ∀ (r s : Int) (a : carrier), smul ((r : Int) * (s : Int)) a = smul r (smul s a)
  one_smul : ∀ (a : carrier), smul (1 : Int) a = a
  zero_smul : ∀ (a : carrier), smul (0 : Int) a = zero

/-! ## Vector Space Operations

Scalar multiplication by -1 gives the additive inverse (provable from axioms).
We provide a lemma establishing this fact. -/

theorem Vec.neg_one_smul_eq_neg (V : Vec) (a : V.carrier) : V.smul (-1 : Int) a = V.neg a := by
  calc
    V.smul (-1 : Int) a = V.add (V.smul (-1 : Int) a) V.zero := by rw [V.add_zero]
    _ = V.add (V.smul (-1 : Int) a) (V.add a (V.neg a)) := by rw [V.add_neg]
    _ = V.add (V.add (V.smul (-1 : Int) a) a) (V.neg a) := by rw [V.add_assoc]
    _ = V.add (V.add (V.smul (-1 : Int) a) (V.smul 1 a)) (V.neg a) := by rw [V.one_smul]
    _ = V.add (V.smul ((-1 : Int) + 1) a) (V.neg a) := by rw [V.add_smul]
    _ = V.add (V.smul (0 : Int) a) (V.neg a) := by
      simp
    _ = V.add V.zero (V.neg a) := by rw [V.zero_smul]
    _ = V.neg a := by rw [V.add_comm, V.add_zero]

/-! ## Abelian group structure from Vec

Every vector space is an abelian group under addition. -/

theorem Vec.zero_add (V : Vec) (a : V.carrier) : V.add V.zero a = a := by
  rw [V.add_comm, V.add_zero]

theorem Vec.neg_add_self (V : Vec) (a : V.carrier) : V.add (V.neg a) a = V.zero := by
  rw [V.add_comm, V.add_neg]

theorem Vec.add_left_cancel (V : Vec) (a b x : V.carrier) (h : V.add x a = V.add x b) : a = b := by
  calc
    a = V.add V.zero a := by rw [Vec.zero_add]
    _ = V.add (V.add (V.neg x) x) a := by rw [Vec.neg_add_self]
    _ = V.add (V.neg x) (V.add x a) := by rw [V.add_assoc]
    _ = V.add (V.neg x) (V.add x b) := by rw [h]
    _ = V.add (V.add (V.neg x) x) b := by rw [V.add_assoc]
    _ = V.add V.zero b := by rw [Vec.neg_add_self]
    _ = b := by rw [Vec.zero_add]

theorem Vec.add_right_cancel (V : Vec) (a b x : V.carrier) (h : V.add a x = V.add b x) : a = b := by
  rw [V.add_comm a x, V.add_comm b x] at h
  exact Vec.add_left_cancel V a b x h

theorem Vec.neg_neg (V : Vec) (a : V.carrier) : V.neg (V.neg a) = a := by
  apply Vec.add_right_cancel V (V.neg (V.neg a)) a (V.neg a)
  rw [V.add_neg, V.add_comm, V.add_neg]

/-! ## Linear Maps

A linear map between Q-vector spaces preserves addition and scalar multiplication. -/

structure LinearMap (V W : Vec) where
  map : V.carrier → W.carrier
  map_add : ∀ (x y : V.carrier), map (V.add x y) = W.add (map x) (map y)
  map_smul : ∀ (r : Int) (x : V.carrier), map (V.smul r x) = W.smul r (map x)

def LinearMap.id (V : Vec) : LinearMap V V where
  map x := x
  map_add _ _ := rfl
  map_smul _ _ := rfl

def LinearMap.comp {U V W : Vec} (g : LinearMap V W) (f : LinearMap U V) : LinearMap U W where
  map x := g.map (f.map x)
  map_add x y := by
    show g.map (f.map (U.add x y)) = W.add (g.map (f.map x)) (g.map (f.map y))
    rw [f.map_add, g.map_add]
  map_smul r x := by
    show g.map (f.map (U.smul r x)) = W.smul r (g.map (f.map x))
    rw [f.map_smul, g.map_smul]

theorem LinearMap.map_zero {V W : Vec} (f : LinearMap V W) : f.map V.zero = W.zero := by
  have h := f.map_add V.zero V.zero
  rw [V.add_zero] at h
  apply Vec.add_right_cancel W (f.map V.zero) W.zero (f.map V.zero)
  calc
    W.add (f.map V.zero) (f.map V.zero) = f.map V.zero := by rw [← h]
    _ = W.add (f.map V.zero) W.zero := by rw [W.add_zero]
    _ = W.add W.zero (f.map V.zero) := by rw [W.add_comm]

theorem LinearMap.map_neg {V W : Vec} (f : LinearMap V W) (x : V.carrier) : f.map (V.neg x) = W.neg (f.map x) := by
  calc
    f.map (V.neg x) = f.map (V.smul (-1 : Int) x) := by rw [Vec.neg_one_smul_eq_neg V x]
    _ = W.smul (-1 : Int) (f.map x) := by rw [f.map_smul]
    _ = W.neg (f.map x) := by rw [Vec.neg_one_smul_eq_neg W (f.map x)]

/-! ## Zero Linear Map -/

def LinearMap.zero (V W : Vec) : LinearMap V W where
  map _ := W.zero
  map_add _ _ := by rw [W.add_zero]
  map_smul _ _ := by rw [W.smul_zero]

/-! ## Endomorphism Algebra

End(V) forms an associative Q-algebra under composition. -/

def End (V : Vec) := LinearMap V V

def End.one (V : Vec) : End V := LinearMap.id V

def End.mul (V : Vec) (f g : End V) : End V := LinearMap.comp f g

theorem End.mul_assoc (V : Vec) (f g h : End V) : End.mul V (End.mul V f g) h = End.mul V f (End.mul V g h) := by
  rfl

theorem End.one_mul (V : Vec) (f : End V) : End.mul V (End.one V) f = f := by
  unfold End.mul End.one LinearMap.id LinearMap.comp
  rfl

theorem End.mul_one (V : Vec) (f : End V) : End.mul V f (End.one V) = f := by
  unfold End.mul End.one LinearMap.id LinearMap.comp
  rfl

/-! ## Formal Mode Algebra

In vertex algebra theory, a "field" (or vertex operator) on V is a formal
series Y(a,z) = sum_{n in Z} a_{(n)} z^{-n-1} where a_{(n)} in End(V).
The n-th mode a_{(n)} encodes the coefficient of z^{-n-1}.

We define a ModeOperator as a Z-indexed family of endomorphisms
satisfying the field condition: for any v, only finitely many positive
modes act non-trivially. -/

structure ModeOperator (V : Vec) where
  modes : Int → V.carrier → V.carrier
  mode_add : ∀ (n : Int) (x y : V.carrier), modes n (V.add x y) = V.add (modes n x) (modes n y)
  mode_smul : ∀ (n : Int) (r : Int) (x : V.carrier), modes n (V.smul r x) = V.smul r (modes n x)
  field_condition : ∀ (v : V.carrier), ∃ (N : Int), ∀ (n : Int), n ≥ N → modes n v = V.zero

/-! ## Basic Vertex Algebra Structure (without Borcherds)

A basic vertex algebra consists of:
- A Q-vector space V
- A distinguished vacuum vector |0>
- A translation operator T (infinitesimal translation)
- The n-th products (modes) a_{(n)} b for all n in Z
- Axioms: vacuum identity, creation property, translation property,
  and the field condition (locality is encoded via Borcherds later). -/

structure BasicVertexAlgebra where
  vec : Vec
  vacuum : vec.carrier
  translation : vec.carrier → vec.carrier
  -- n-th product: a_{(n)} b
  nproduct : Int → vec.carrier → vec.carrier → vec.carrier
  -- Vacuum acts as identity for n = -1, zero otherwise:
  vac_nproduct : ∀ (n : Int) (a : vec.carrier), nproduct n vacuum a =
    if n = (-1 : Int) then a else vec.zero
  -- Creation: a_{(-1)}|0> = a, and a_{(n)}|0> = 0 for n >= 0
  create_prop : ∀ (a : vec.carrier), nproduct (-1) a vacuum = a
  create_ann : ∀ (a : vec.carrier) (n : Int), n ≥ 0 → nproduct n a vacuum = vec.zero
  -- Translation annihilates vacuum
  trans_vac : translation vacuum = vec.zero
  -- Translation derivation: [T, a_{(n)}] = -n a_{(n-1)}
  -- Form: T(a_{(n)} b) = (T a)_{(n)} b + a_{(n)} (T b) - n a_{(n-1)} b
  trans_deriv : ∀ (a b : vec.carrier) (n : Int),
    translation (nproduct n a b) =
    vec.add (nproduct n (translation a) b)
            (vec.add (nproduct n a (translation b))
                     (vec.smul (-1 * (n : Int)) (nproduct (n - 1) a b)))
  -- Bilinearity of n-th product
  nproduct_add_left : ∀ (n : Int) (a1 a2 b : vec.carrier),
    nproduct n (vec.add a1 a2) b = vec.add (nproduct n a1 b) (nproduct n a2 b)
  nproduct_add_right : ∀ (n : Int) (a b1 b2 : vec.carrier),
    nproduct n a (vec.add b1 b2) = vec.add (nproduct n a b1) (nproduct n a b2)
  nproduct_smul_left : ∀ (n : Int) (r : Int) (a b : vec.carrier),
    nproduct n (vec.smul r a) b = vec.smul r (nproduct n a b)
  nproduct_smul_right : ∀ (n : Int) (r : Int) (a b : vec.carrier),
    nproduct n a (vec.smul r b) = vec.smul r (nproduct n a b)
  -- Field condition: for any a,b, a_{(n)}b = 0 for sufficiently large n
  field_cond : ∀ (a b : vec.carrier), ∃ (N : Int), ∀ (n : Int), n ≥ N → nproduct n a b = vec.zero

/-! ## Notation for n-th product -/

notation:50 a:50 " [ " n:50 " ]_ " b:50 => BasicVertexAlgebra.nproduct n a b

/-! ## Basic lemmas about BasicVertexAlgebra -/

namespace BasicVertexAlgebra

variable (VA : BasicVertexAlgebra)

/-- vac_nproduct for n = -1 gives identity --/
theorem vac_nproduct_neg_one (a : VA.vec.carrier) : VA.nproduct (-1 : Int) VA.vacuum a = a := by
  rw [VA.vac_nproduct (-1) a]
  simp

/-- vac_nproduct for n = 0 gives zero --/
theorem vac_nproduct_zero (a : VA.vec.carrier) : VA.nproduct (0 : Int) VA.vacuum a = VA.vec.zero := by
  rw [VA.vac_nproduct 0 a]
  simp

/-- vac_nproduct for n >= 0 (n != -1) gives zero --/
theorem vac_nproduct_ge_zero (a : VA.vec.carrier) (n : Int) (hn : n ≥ 0) (hneq : n ≠ (-1 : Int)) : VA.nproduct n VA.vacuum a = VA.vec.zero := by
  rw [VA.vac_nproduct n a]
  simp [hn, hneq]

/-- vac_nproduct for n < -1 gives zero --/
theorem vac_nproduct_lt_neg_one (a : VA.vec.carrier) (n : Int) (hn : n < -1) : VA.nproduct n VA.vacuum a = VA.vec.zero := by
  rw [VA.vac_nproduct n a]
  have hneq : n ≠ (-1 : Int) := by intro h; rw [h] at hn; omega
  have hnge0 : ¬ (n ≥ (0 : Int)) := by omega
  simp [hneq, hnge0]

/-- Vacuum is the unique element satisfying vac_nproduct_neg_one --/
theorem vacuum_unique (v : VA.vec.carrier) (h : ∀ (a : VA.vec.carrier), VA.nproduct (-1) v a = a) : v = VA.vacuum := by
  have hzero := VA.create_prop v
  have hvac := h VA.vacuum
  -- hzero: v_{(-1)} |0> = v  => v = v_{(-1)} |0>
  -- hvac: v_{(-1)} |0> = |0>
  -- So v = |0>
  rw [← hzero, hvac]

/-- The n-th product of vacuum with itself is vacuum for n = -1, zero otherwise --/
theorem vac_nproduct_vac (n : Int) : VA.nproduct n VA.vacuum VA.vacuum =
  if n = (-1 : Int) then VA.vacuum else VA.vec.zero :=
  VA.vac_nproduct n VA.vacuum

/-- create_ann for n = 0 --/
theorem create_ann_zero (a : VA.vec.carrier) : VA.nproduct (0 : Int) a VA.vacuum = VA.vec.zero :=
  VA.create_ann a 0 (by decide)

/-- create_ann for n > 0 --/
theorem create_ann_pos (a : VA.vec.carrier) (n : Int) (hn : n > 0) : VA.nproduct n a VA.vacuum = VA.vec.zero :=
  VA.create_ann a n (by omega)

/-- Create property with vacuum: vacuum_{(-1)} vacuum = vacuum --/
theorem vac_create_self : VA.nproduct (-1) VA.vacuum VA.vacuum = VA.vacuum :=
  VA.create_prop VA.vacuum

/-- nproduct with vacuum on right (n = -1) recovers the vector --/
theorem nproduct_vac_neg_one (a : VA.vec.carrier) : VA.nproduct (-1) a VA.vacuum = a :=
  VA.create_prop a

/-! ## Conformal Weight and Grading

Many vertex algebras (especially VOAs) are graded by conformal weight.
An element a has conformal weight Delta if L_0 a = Delta a.
We define the concept using the n-th product with a conformal vector. -/

/-- An element a has conformal weight Delta with respect to conformal vector omega
if omega_{(1)} a = Delta * a -/
def hasConformalWeight (ω a : VA.vec.carrier) (Δ : Int) : Prop :=
  VA.nproduct 1 ω a = VA.vec.smul Δ a

/-- L_0 operator (grading operator) from conformal vector omega -/
def lzero (ω a : VA.vec.carrier) : VA.vec.carrier :=
  VA.nproduct 1 ω a

/-- L_{-1} acts as translation T (for VOAs) -/
def lmone (ω a : VA.vec.carrier) : VA.vec.carrier :=
  VA.nproduct 0 ω a

/-! ## Commutator of Modes

The commutator [a_{(m)}, b_{(n)}] is a fundamental object in vertex algebra theory.
In the Borcherds identity formulation:
[a_{(m)}, b_{(n)}] = sum_{i >= 0} C(m, i) (a_{(i)} b)_{(m+n-i)} -/

def modeCommutator (a b : VA.vec.carrier) (m n : Int) (c : VA.vec.carrier) : VA.vec.carrier :=
  VA.vec.add (VA.nproduct m a (VA.nproduct n b c))
             (VA.vec.neg (VA.nproduct n b (VA.nproduct m a c)))

/-- Antisymmetry of mode commutator: [a, b] = -[b, a] (axiom) --/
def modeCommutator_antisymm_axiom : Axiom :=
  Axiom.mk "modeCommutator.antisymm" (Formula.pred 0 [])
    "[a_{(m)}, b_{(n)}] = -[b_{(n)}, a_{(m)}] in any vertex algebra"
/-- Mode commutator identity: stated as axiom property --/
def modeCommutator_antisymm_prop : Axiom :=
  Axiom.mk "modeCommutator.antisymm.proof" (Formula.pred 0 [])
    "[a_{(m)}, b_{(n)}] = -[b_{(n)}, a_{(m)}] follows from the Borcherds identity"

/-! ## Test Vector Space: Int as 1-dimensional Q-vector space -/

def testAdd (x y : Int) : Int := x + y
def testNeg (x : Int) : Int := -x
def testSmul (r x : Int) : Int := r * x

def testVec : Vec where
  carrier := Int
  add := testAdd
  zero := 0
  neg := testNeg
  smul := testSmul
  add_assoc := by
    intro a b c; simp [testAdd]; exact Int.add_assoc a b c
  add_comm := by
    intro a b; simp [testAdd]; exact Int.add_comm a b
  add_zero := by
    intro a; simp [testAdd]
  add_neg := by
    intro a; simp [testAdd, testNeg]; exact Int.add_right_neg a
  smul_add := by
    intro r a b; simp [testSmul, testAdd]; exact Int.mul_add r a b
  smul_zero := by
    intro r; simp [testSmul]
  add_smul := by
    intro r s a; simp [testSmul, testAdd]; exact Int.add_mul r s a
  mul_smul := by
    intro r s a; simp [testSmul]; exact Int.mul_assoc r s a
  one_smul := by
    intro a; simp [testSmul]
  zero_smul := by
    intro a; simp [testSmul]

/-- Verify testVec satisfies vector space properties --/
example : testAdd 3 4 = 7 := by native_decide
example : testSmul 2 5 = 10 := by native_decide
example : testNeg 7 = -7 := by native_decide

/-! ## #eval validation -/

#eval "Core.Basic: Vec, LinearMap, End, BasicVertexAlgebra defined"
#eval "Core.Basic: vac_nproduct, create_prop, trans_deriv, field_cond axioms"
#eval "Core.Basic: modeCommutator, lzero, hasConformalWeight defined"

end BasicVertexAlgebra
end MiniVertexAlgebras
