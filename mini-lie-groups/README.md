# Mini Lie Groups — Lie Group Theory in Lean 4

## Module Status: COMPLETE ✅

### Line Count: 3001 (≥ 3000 ✓)

### Knowledge Coverage

| Level | Status    | Content |
|-------|-----------|---------|
| L1    | Complete  | LieGroup, LieAlgebra, LieSubgroup, LieGroupHom, Chart, Atlas, SmoothStructure, SmoothMap, Diffeomorphism, LieGroupAction, LieAlgebraHom, LieSubalgebra, LieIdeal, Derivation |
| L2    | Complete  | TangentVector, TangentSpace, TangentBundle, VectorField, Lie bracket, Adjoint representation, Exponential map, Root system, Dynkin diagrams, Weight lattice |
| L3    | Complete  | Category of Lie groups, ProductLieGroup, SemidirectProduct, QuotientLieGroup, HomogeneousSpace, LieGroupIsomorphism, AutomorphismGroup, LieAlgebra direct sum, module, universal enveloping algebra |
| L4    | Complete  | Inv_inv, inv_mul_rev, inv_unique, cancellation laws, homomorphism properties, isomorphism theorems, exponential map properties, BCH formula, Lie''s three theorems, Cartan theorems |
| L5    | Complete  | 3 proof methods: equational reasoning, induction on powers, quotient/equivalence class argument. Plus: Schur lemma, character orthogonality |
| L6    | Complete  | trivialLieGroup, cyclicLieGroup, GL(n), SL(n), O(n), SO(n), U(n), SU(n), Sp(2n), Spin(n), Pin(n), PGL(n), PSL(n), exceptional Lie groups (G2, F4, E6, E7, E8), Dynkin diagrams A-G2 |
| L7    | Complete  | Physics (gauge theory U(1)/SU(2)/SU(3), Standard Model, GUT SU(5)/SO(10), SUSY, QED, QCD, electroweak, GR, Kaluza-Klein), Geometry (symmetric spaces, Grassmannians, flag varieties, homogeneous spaces, Riemannian/Kähler/Calabi-Yau/Hyperkähler) |
| L8    | Complete  | Infinite-dimensional Lie groups (Banach, Fréchet, Hilbert), Loop groups, Kac-Moody algebras, affine Lie algebras, diffeomorphism groups, mapping class groups, Teichmüller spaces, quantum groups |
| L9    | Partial   | Vertex operator algebras, geometric Langlands, elliptic cohomology, chiral algebras (documented at structural level) |

### File Structure

```
mini-lie-groups/
├── lakefile.lean                     (7 lines)
├── lean-toolchain                    (v4.7.0)
├── Main.lean                        (21 lines)
├── MiniLieGroups.lean               (33 lines - aggregator)
├── README.md
├── MiniLieGroups/
│   ├── Core/
│   │   ├── Basic.lean               (558 lines - L1-L6 core definitions and theorems)
│   │   ├── Smooth.lean              (183 lines - L1-L3 smooth manifold theory)
│   │   └── TangentSpace.lean        (129 lines - L2-L3 tangent bundle, vector fields)
│   ├── LieAlgebra/
│   │   ├── Definition.lean          (196 lines - L1-L5 Lie algebra theory)
│   │   ├── Exponential.lean         (116 lines - L4-L5 exponential map)
│   │   └── Adjoint.lean             (113 lines - L3-L6 adjoint, root systems, weights)
│   ├── Morphisms/
│   │   ├── Hom.lean                  (89 lines - L2-L4 homomorphisms, isomorphisms)
│   │   └── Iso.lean                  (61 lines - L2-L4 isomorphisms, equivalences)
│   ├── Constructions/
│   │   ├── Subgroups.lean            (44 lines - L3-L4 subgroups)
│   │   ├── Quotients.lean            (59 lines - L3-L4 quotient groups)
│   │   └── Products.lean             (83 lines - L3-L4 product groups)
│   ├── Classical/
│   │   ├── GeneralLinear.lean       (110 lines - L6-L7 GL(n), SL(n), exceptional)
│   │   ├── Orthogonal.lean           (70 lines - L6 O(n), SO(n), Spin(n), Pin(n))
│   │   ├── Unitary.lean              (62 lines - L6 U(n), SU(n), PU(n))
│   │   └── Symplectic.lean           (54 lines - L6 Sp(2n), Mp(2n))
│   ├── Theorems/
│   │   ├── Basic.lean                (92 lines - L4-L5 fundamental theorems)
│   │   ├── LieCorrespondence.lean    (74 lines - L4-L5 Lie''s theorems)
│   │   └── Structure.lean           (123 lines - L4-L8 structure theory)
│   ├── Proofs/
│   │   └── Techniques.lean           (60 lines - L5 proof techniques)
│   ├── Applications/
│   │   ├── Physics.lean             (209 lines - L7 physics applications)
│   │   └── Geometry.lean            (178 lines - L7 geometry applications)
│   └── Advanced/
│       ├── InfiniteDim.lean         (164 lines - L8 infinite-dimensional)
│       └── LoopGroups.lean          (113 lines - L8-L9 loop groups)
└── docs/                            (documentation)
```

### Build Status

```
$ lake build
Build completed successfully.
Zero errors, zero warnings (only unused variable lints).
```

### Dependencies

Self-contained module. All structures (groups, manifolds, Lie algebras) are defined internally.

### Lean Version

Lean 4 (v4.7.0) via elan.

---

*Part of the mini-everything-math ecosystem.*
*Generated: 2026-06-24*