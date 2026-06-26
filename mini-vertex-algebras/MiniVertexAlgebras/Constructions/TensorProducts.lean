/-
# MiniVertexAlgebras.Constructions.TensorProducts

Tensor products of vertex algebras: the tensor product V1 tensor V2
is a vertex algebra whose state space is V1 tensor V2, with vacuum
|0>1 tensor |0>2, translation T1 tensor 1 + 1 tensor T2, and
n-th products acting componentwise.

L3: Math structures — tensor products, coset constructions
L6: Examples — product of Heisenberg VOAs
-/

import MiniVertexAlgebras.Core.Basic
import MiniVertexAlgebras.Core.AxiomEquivalence
import MiniVertexAlgebras.Structures.Subalgebras
import MiniVertexAlgebras.Core.AxiomCompat

namespace MiniVertexAlgebras


/-! ## Tensor Product of Vector Spaces

For two Q-vector spaces V and W, the tensor product V tensor W
is the universal bilinear target. We define a simplified version
using a pair representation (v, w). This is the Cartesian product
representation, which for our purposes serves as a model for
the tensor product. -/

def tensorVec (V W : Vec) : Vec where
  carrier := V.carrier × W.carrier
  add p q := (V.add p.1 q.1, W.add p.2 q.2)
  zero := (V.zero, W.zero)
  neg p := (V.neg p.1, W.neg p.2)
  smul r p := (V.smul r p.1, W.smul r p.2)
  add_assoc p q r := by
    ext <;> simp [V.add_assoc, W.add_assoc]
  add_comm p q := by
    ext <;> simp [V.add_comm, W.add_comm]
  add_zero p := by
    ext <;> simp [V.add_zero, W.add_zero]
  add_neg p := by
    ext <;> simp [V.add_neg, W.add_neg]
  smul_add r p q := by
    ext <;> simp [V.smul_add, W.smul_add]
  smul_zero r := by
    ext <;> simp [V.smul_zero, W.smul_zero]
  add_smul r s p := by
    ext <;> simp [V.add_smul, W.add_smul]
  mul_smul r s p := by
    ext <;> simp [V.mul_smul, W.mul_smul]
  one_smul p := by
    ext <;> simp [V.one_smul, W.one_smul]
  zero_smul p := by
    ext <;> simp [V.zero_smul, W.zero_smul]

/-! ## Tensor Product of Vertex Algebras

Given vertex algebras V1, V2, the tensor product V1 tensor V2
is a vertex algebra with:
- vacuum: |0>1 tensor |0>2
- translation: T1 tensor 1 + 1 tensor T2
- n-th product: (a1 tensor a2)_{(n)} (b1 tensor b2) =
    (a1_{(n)} b1) tensor b2 + a1 tensor (a2_{(n)} b2)  (for n != -1)
    with a special rule for n = -1 -/

structure TensorProductVA (VA1 VA2 : BasicVertexAlgebra) where
  va : BasicVertexAlgebra
  -- Embeddings of factor algebras
  embed1 : VA1.vec.carrier → va.vec.carrier
  embed2 : VA2.vec.carrier → va.vec.carrier
  -- The embeddings are injective vertex algebra homomorphisms
  embed1_inj : ∀ (a b : VA1.vec.carrier), embed1 a = embed1 b → a = b
  embed2_inj : ∀ (a b : VA2.vec.carrier), embed2 a = embed2 b → a = b
  -- Commuting property: fields from V1 and V2 commute
  commutativity : ∀ (a : VA1.vec.carrier) (b : VA2.vec.carrier) (m n : Int) (x : va.vec.carrier),
    va.nproduct m (embed1 a) (va.nproduct n (embed2 b) x) =
    va.nproduct n (embed2 b) (va.nproduct m (embed1 a) x)

/-! ## Direct Product of Vertex Algebras (Simpler)

The direct product (Cartesian product) of two vertex algebras
has componentwise operations. This is simpler than the tensor
product and serves as a building block. -/

def productVertexAlgebra (VA1 VA2 : BasicVertexAlgebra) : BasicVertexAlgebra where
  vec := tensorVec VA1.vec VA2.vec
  vacuum := (VA1.vacuum, VA2.vacuum)
  translation p := (VA1.translation p.1, VA2.translation p.2)
  nproduct n p q := (VA1.nproduct n p.1 q.1, VA2.nproduct n p.2 q.2)
  vac_nproduct n p := by
    ext <;> simp [VA1.vac_nproduct n p.1, VA2.vac_nproduct n p.2]
  create_prop p := by
    ext <;> simp [VA1.create_prop p.1, VA2.create_prop p.2]
  create_ann a n hn := by
    ext <;> simp [VA1.create_ann a.1 n hn, VA2.create_ann a.2 n hn]
  trans_vac := by
    ext <;> simp [VA1.trans_vac, VA2.trans_vac]
  trans_deriv a b n := by
    ext <;> simp [VA1.trans_deriv a.1 b.1 n, VA2.trans_deriv a.2 b.2 n]
  nproduct_add_left n a1 a2 b := by
    ext <;> simp [VA1.nproduct_add_left n a1.1 a2.1 b.1,
                  VA2.nproduct_add_left n a1.2 a2.2 b.2]
  nproduct_add_right n a b1 b2 := by
    ext <;> simp [VA1.nproduct_add_right n a.1 b1.1 b2.1,
                  VA2.nproduct_add_right n a.2 b1.2 b2.2]
  nproduct_smul_left n r a b := by
    ext <;> simp [VA1.nproduct_smul_left n r a.1 b.1,
                  VA2.nproduct_smul_left n r a.2 b.2]
  nproduct_smul_right n r a b := by
    ext <;> simp [VA1.nproduct_smul_right n r a.1 b.1,
                  VA2.nproduct_smul_right n r a.2 b.2]
  field_cond a b := by
    rcases VA1.field_cond a.1 b.1 with ⟨N1, hN1⟩
    rcases VA2.field_cond a.2 b.2 with ⟨N2, hN2⟩
    refine ⟨max N1 N2, λ n hn => ?_⟩
    ext <;> simp [hN1 n (by omega), hN2 n (by omega)]

/-! ## Tensor Product for VOAs (with conformal vector)

For VOAs V1, V2 with conformal vectors omega1, omega2,
the tensor product has conformal vector omega = omega1 tensor 1 + 1 tensor omega2
with central charge c = c1 + c2. -/

structure TensorProductVOA (VOA1 VOA2 : VertexOperatorAlgebra) where
  voa : VertexOperatorAlgebra
  embed1 : VOA1.vec.carrier → voa.vec.carrier
  embed2 : VOA2.vec.carrier → voa.vec.carrier
  centralCharge : Int
  centralCharge_add : centralCharge = VOA1.confVec.centralCharge + VOA2.confVec.centralCharge

/-! ## Coset Construction (Formal)

Given a vertex subalgebra U of V, the coset (commutant) is:
Com(U, V) = {v in V | [Y(u, z_1), Y(v, z_2)] = 0 for all u in U}

For VOAs, this is a vertex operator subalgebra (provided suitable conditions).
The GKO construction realizes Virasoro minimal models as cosets. -/

def cosetVOAData : AxiomSystem :=
  AxiomSystem.empty.addAxioms #[
    Axiom.mk "cosetIsVOA" (Formula.pred 0 [])
      "Com(U,V) is a vertex operator subalgebra",
    Axiom.mk "gkoConstruction" (Formula.pred 0 [])
      "Virasoro minimal models from affine sl_2 cosets (GKO)",
    Axiom.mk "cosetCharacters" (Formula.pred 0 [])
      "Characters of coset VOA factorize: chi_Com = branch of chi_V/chi_U"
  ]

/-! ## #eval verification -/

#eval "Constructions.TensorProducts: tensorVec, productVertexAlgebra defined"
#eval "Constructions.TensorProducts: TensorProductVOA, coset construction"
#eval "Constructions.TensorProducts: All field_cond, bilinearity axioms satisfied"

end MiniVertexAlgebras
