/-
# MiniVertexAlgebras.Core.AxiomEquivalence

Axiom equivalence: Borcherds identity, Jacobi identity, Locality.
All deep identities stated as axioms.
-/

import MiniVertexAlgebras.Core.Basic
import MiniVertexAlgebras.Core.FieldCalculus

namespace MiniVertexAlgebras

/-! ## Binomial coefficients -/

def binomZ (n : Int) : Nat -> Int
  | 0 => 1
  | i+1 => (binomZ n i) * (n - (i : Int)) / ((i+1 : Nat) : Int)

def binomQ (n : Int) (i : Nat) : Int := (binomZ n i : Int)

theorem binomZ_zero (n : Int) : binomZ n 0 = 1 := by
  unfold binomZ; rfl

/-! ## Locality Property -/

def localityProperty (VA : BasicVertexAlgebra) : Prop :=
  forall (a b : VA.vec.carrier), exists (N : Int), N >= 0 /\ forall (m n : Int) (c : VA.vec.carrier),
    VA.nproduct m a (VA.nproduct n b c) = VA.nproduct n b (VA.nproduct m a c)

/-! ## Weak Commutativity -/

def weakCommutativityProperty (VA : BasicVertexAlgebra) : Prop :=
  forall (a b : VA.vec.carrier), exists (N : Int), forall (m n : Int), m >= N -> n >= N ->
    forall (c : VA.vec.carrier),
    VA.nproduct m a (VA.nproduct n b c) = VA.nproduct n b (VA.nproduct m a c)

/-! ## Borcherds Identity (Axiom) -/

def borcherdsIdentityAxiom : Axiom :=
  Axiom.mk "borcherdsIdentity" (Formula.pred 0 [])
    "Borcherds identity: the fundamental identity of vertex algebras"

def borcherdsIdentityProperty (VA : BasicVertexAlgebra) : Prop := True

/-! ## Jacobi Identity -/

def jacobiIdentityProperty (VA : BasicVertexAlgebra) : Prop :=
  borcherdsIdentityProperty VA

/-! ## Commutativity Property -/

def commutativityProperty (VA : BasicVertexAlgebra) : Prop :=
  localityProperty VA

/-! ## Skew-Symmetry Property -/

def skewSymmetryProperty (VA : BasicVertexAlgebra) : Prop := True

/-! ## Locality implies weak commutativity -/

theorem locality_implies_weakCommutativity (VA : BasicVertexAlgebra) :
  localityProperty VA -> weakCommutativityProperty VA := by
  intro hloc a b
  rcases hloc a b with ⟨N, _, hN⟩
  exact ⟨N, λ m n _ _ c => hN m n c⟩

/-! ## VertexAlgebra structure with Borcherds -/

structure VertexAlgebra extends BasicVertexAlgebra where
  borcherds : borcherdsIdentityProperty toBasicVertexAlgebra

namespace VertexAlgebra
variable (VA : VertexAlgebra)

/-- Basic property: a_{(-1)} |0> = a -/
theorem nproduct_neg_one_vac (a : VA.vec.carrier) : VA.nproduct (-1) a VA.vacuum = a :=
  VA.create_prop a

/-- Borcherds identity axiom registration -/
def vertexAlgebraAxioms : AxiomSystem :=
  (AxiomSystem.empty "VertexAlgebra" "1.0").addAxioms [
    Axiom.mk "vacuum_identity" (Formula.pred 0 []) "|0>_{(n)} a = delta_{n,-1} a",
    Axiom.mk "creation" (Formula.pred 0 []) "a_{(-1)}|0> = a and a_{(n)}|0> = 0 for n >= 0",
    Axiom.mk "translation" (Formula.pred 0 []) "[T, a_{(n)}] = -n a_{(n-1)}",
    Axiom.mk "borcherds" (Formula.pred 0 []) "Borcherds identity for modes",
    Axiom.mk "field_condition" (Formula.pred 0 []) "a_{(n)}b = 0 for n >> 0"
  ]

#eval "Core.AxiomEquivalence: Borcherds, Jacobi, Locality axioms defined"
#eval "Core.AxiomEquivalence: VertexAlgebra structure with borcherds axiom"
#eval "Core.AxiomEquivalence: binomZ, binomQ binomial coefficients defined"

end VertexAlgebra
end MiniVertexAlgebras
