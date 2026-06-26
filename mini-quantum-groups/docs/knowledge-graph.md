# Knowledge Graph — Mini-Quantum-Groups

## L1: Definitions (Complete)
- qNumber, qFactorial, qBinomial (Gaussian binomial coefficients)
- Coalgebra: comultiplication, counit, coassociativity
- Bialgebra: compatible algebra + coalgebra
- HopfAlgebra: bialgebra + antipode (Hopf axiom)
- QuasitriangularHopfAlgebra: universal R-matrix
- RibbonHopfAlgebra: ribbon element for knot invariants
- Uqsl2Gen: E, F, K, K⁻¹ generators
- Uqsl2Monomial: PBW basis K^i E^m F^n
- RMatrix: R-matrix for Yang-Baxter equation
- QuantumPlaneMonomial: x^a y^b with yx = q xy
- Mq2Monomial: a^p b^q c^r d^s for quantum 2×2 matrices
- SLq2Generator: generators of quantum SL(2)
- CartanMatrix: entries a_ij with a_ii = 2
- DrinfeldDouble: H ⊗ H* construction
- YangBaxterRMatrix: R₁₂R₁₃R₂₃ = R₂₃R₁₃R₁₂

## L2: Core Concepts (Complete)
- q-analogue: [n]_q → n as q → 1
- Non-cocommutativity: τ∘Δ ≠ Δ for q ≠ 1
- Universal R-matrix: R satisfies RΔ = Δ^{op}R
- Braided tensor category: Rep(U_q(g)) with braiding
- Lusztig automorphisms T_i: braid group action
- Quantum trace: tr_q = tr(K·)
- Quantum dimension: dim_q(V) = tr_q(id_V)
- Drinfeld twist: gauge equivalence of Hopf algebras
- Multiparameter deformation: independent q_i per simple root
- Jackson q-derivative: (f(qx)-f(x))/((q-1)x)

## L3: Math Structures (Complete)
- Hopf algebra structure on U_q(sl_2)
  - Δ(E) = E⊗1 + K⊗E, Δ(F) = F⊗K⁻¹ + 1⊗F, Δ(K) = K⊗K
  - ε(E)=ε(F)=0, ε(K)=1
  - S(E)=-K⁻¹E, S(F)=-FK, S(K)=K⁻¹
- PBW basis: {K^i E^m F^n | i∈ℤ, m,n∈ℕ}
- Tensor categories with braiding σ = flip ∘ R
- Representation theory: V_j spin-j representations
- Clebsch-Gordan decomposition: V_j ⊗ V_k ≅ ⊕ V_l
- FRT bialgebra A(R) from R-matrix
- Quantum double D(H) = H* ⊗ H
- Modular tensor category at root of unity
- Verlinde fusion algebra

## L4: Fundamental Theorems (Complete)
- Yang-Baxter equation: R₁₂R₁₃R₂₃ = R₂₃R₁₃R₁₂
- q-binomial theorem: (x+y)^n = Σ [n choose k]_q x^{n-k} y^k
- PBW theorem for U_q(sl_2): spanning + linear independence
- Quantum determinant centrality in M_q(2)
- Coproduct coassociativity: (Δ⊗id)Δ = (id⊗Δ)Δ
- Lusztig T_i involution property
- Antipode anti-homomorphism property
- Verlinde formula for fusion rules at root of unity

## L5: Proof Techniques (Complete - ≥3)
1. Direct algebraic computation (field_simp, ring, matrix ops)
2. #eval computational verification for specific parameters
3. Induction on n for q-identities
4. Omega for arithmetic/inequality reasoning
5. Categorical diagrammatic proofs (documented)
6. Combinatorial manipulation of q-series

## L6: Canonical Examples (Complete)
- U_q(sl_2) with q=2: q-numbers [5]_2=31, q-factorials, q-binomials
- Spin-1/2 representation: 2d E,F,K matrices
- Spin-1 representation: 3d matrices with qNumber q 2
- Quantum plane q=2: yx=2xy noncommutative demonstrations
- R-matrix 2d: explicit 4×4 matrix and Yang-Baxter check
- Jones polynomials: trefoil t+t³-t⁴, figure-8 t²-t+1-t⁻¹+t⁻²
- q-exponential: exp_2(1) ≈ numerical approximation
- Fibonacci anyon model from U_q(sl_2) at level k=2
- Quantum determinant: det_q = ad - q⁻¹bc

## L7: Applications (Complete - ≥2)
1. Knot Theory:
   - Jones polynomial from quantum groups
   - Kauffman bracket and skein relations
   - Reshetikhin-Turaev 3-manifold invariants
   - Braid group representations via R-matrices

2. Topological Quantum Computing:
   - Fibonacci anyons (universal TQC)
   - Braiding gates from R-matrices
   - Quantum algorithms for Jones polynomial

3. Quantum Integrable Systems:
   - Yang-Baxter equation and quantum inverse scattering
   - Reflection equation for boundaries

## L8: Advanced Topics (Partial+)
- Crystal bases (Kashiwara) and canonical bases (Lusztig)
- Quantum groups at roots of unity: restricted u_q(g)
- Affine quantum groups U_q(ĝ) (documented)
- Categorification: Khovanov homology from U_q(sl_2)
- qKZ equations and monodromy
- Double affine Hecke algebras (DAHA)

## L9: Research Frontiers (Partial)
- Logarithmic CFT and non-semisimple quantum groups
- Quantum geometric Langlands program
- Condensed mathematics approach to quantum groups
- Higher representation theory and (∞,2)-categories
- Categorical quantum groups (Khovanov-Lauda-Rouquier algebras)
- Factorization homology and quantum groups
- Derived algebraic geometry of quantum groups
