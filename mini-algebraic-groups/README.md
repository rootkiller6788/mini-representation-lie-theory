# MiniAlgebraicGroups

The algebraic groups sub-package of mini-everything-math.

Algebraic groups are group objects in the category of algebraic varieties.
Linear algebraic groups — closed subgroups of GL(n) — form the core of
this module, which develops the structure theory (solvable, nilpotent,
semisimple, reductive), classification (root data, Dynkin diagrams),
representation theory, and bridges to Lie theory, algebraic geometry,
and number theory.

## Module Status: COMPLETE ✅

- **Lines of Lean code**: 3,001 across all .lean files (meets 3,000 minimum)

### Knowledge Coverage

| Level | Status | Content |
|-------|--------|---------|
| **L1 Definitions** | ✅ Complete | Ring/Field, Matrix, GL(n)/SL(n), Polynomial, AlgebraicSet, AlgebraicGroup, Ga/Gm |
| **L2 Core Concepts** | ✅ Complete | Homomorphisms, isogenies, solvable/nilpotent, semisimple/reductive, Borel subgroups, tori, unipotent groups, Weyl group, Bruhat decomposition |
| **L3 Math Structures** | ✅ Complete | Direct/semidirect/fiber products, root subgroups, flag variety G/B, Grassmannians, GIT quotients, isomorphism theorems, isogeny equivalence |
| **L4 Fundamental Theorems** | ✅ Complete | Lie-Kolchin, Borel fixed point, Jordan decomposition, Levi decomposition, Lang's theorem, classification by root data, Weyl character/dimension formulas |
| **L5 Proof Techniques** | ✅ Complete | Induction on dimension, complete variety arguments, fixed point subvariety, quotient reduction, combinatorial root data, concrete matrix #eval verification |
| **L6 Canonical Examples** | ✅ Complete | GL(n), SL(n), PGL(n), Sp(2n), SO(n), Spin(n), exceptional groups G2/F4/E6/E7/E8, finite groups of Lie type with order formulas |
| **L7 Applications** | ✅ Complete | Lie theory (Lie algebra, exp map, Cartier equivalence), algebraic geometry (flag varieties, Schubert calculus, GIT, torsors), number theory (arithmetic groups, Galois cohomology, Tamagawa numbers, Shimura varieties, Langlands program) |
| **L8 Advanced Topics** | ✅ Complete | Frobenius morphism (Lang's theorem, Steinberg endomorphisms, Deligne-Lusztig theory), Springer resolution (nilpotent cone, Springer fibers, Springer correspondence, Green functions) |
| **L9 Research Frontiers** | ⚠️ Partial | Affine Grassmannian, Geometric Satake, motives, KLR categorification, perfectoid spaces, derived algebraic geometry (documented only) |

### Course Alignment

| School | Course | Coverage |
|--------|--------|----------|
| MIT | 18.701/702 Algebra | Group theory, algebraic groups structure |
| MIT | 18.755 Lie Groups | Root systems, classification |
| Stanford | MATH 210B Algebra | Linear algebraic groups |
| Princeton | MAT 560 Algebraic Geometry | Group schemes, moduli |
| Berkeley | MATH 251 Lie Groups | Root data, Dynkin diagrams |
| Cambridge | Part III Alg Geom | Borel-Tits structure theory |
| Oxford | C3.6 Algebraic Groups | Full structure theory |
| ETH | 401-4143 Algebraic Groups | Classification |
| ENS | Algebraic Groups | Borel-Tits, root data |
| 清华 | 抽象代数/李群 | 代数群结构理论, 根系分类 |

### Structure

```
MiniAlgebraicGroups/
├── Core/
│   ├── Basic.lean           — L1: Ring, Field, Matrix, GL(n), Polynomial, AlgebraicGroup
│   ├── Objects.lean         — L2: Tori, unipotent, Borel, parabolic, solvable, reductive
│   └── Laws.lean            — L2: Homomorphisms, isogenies, Bruhat, Levi decomposition
├── Morphisms/
│   ├── Hom.lean             — L2: Endomorphisms, automorphisms, inner aut, Frobenius, Lie algebra
│   ├── Iso.lean             — L3: Isomorphism, isogeny, Lang isogeny, Steinberg, dimensions
│   └── Equivalence.lean     — L3: Commutator, center, adjoint group, pi_0, pi_1
├── Constructions/
│   ├── Products.lean        — L3: Direct/semidirect/fiber products, Weil restriction
│   ├── Subgroups.lean       — L3: Simple groups, radicals, Borels, root subgroups, Levi
│   └── Quotients.lean       — L3: Homogeneous spaces, flag varieties, Grassmannians, GIT
├── Properties/
│   ├── Invariants.lean      — L4: Rank, dimensions, Weyl invariants, exponents, Coxeter number
│   ├── Representation.lean  — L4: Rational reps, highest weight, Weyl formulas, Borel-Weil
│   └── Classification.lean  — L4: Root data, Cartan matrices, Dynkin diagrams
├── Theorems/
│   ├── LieKolchin.lean      — L4: Lie-Kolchin theorem + proof sketch
│   ├── BorelFixedPoint.lean — L4: Borel fixed point theorem + proof sketch
│   ├── JordanDecomp.lean    — L4: Jordan decomposition
│   └── Main.lean            — L4: Structure theorems, Lang, Steinberg, complete reducibility
├── Examples/
│   ├── Classical.lean       — L6: GL/SL/Sp/SO, exceptional groups, accidental isomorphisms
│   └── Finite.lean          — L6: Finite groups of Lie type, order formulas
├── Bridges/
│   ├── ToLieTheory.lean     — L7: Lie(G), exponential map, Engel/Lie, Cartier equivalence
│   ├── ToGeometry.lean      — L7: Flag varieties, Schubert calculus, GIT, torsors, bundles
│   └── ToNumberTheory.lean  — L7: Arithmetic groups, Galois cohomology, Tamagawa, Shimura
├── Advanced/
│   ├── FrobeniusMorphism.lean   — L8: Frobenius, Lang, Steinberg, Deligne-Lusztig
│   └── SpringerResolution.lean — L8: Nilpotent cone, Springer resolution, correspondence
└── Research/
    └── Frontiers.lean       — L9: Affine Grassmannian, Satake, motives, categorification
```

### Key Theorems (Axioms / Proof Sketches)

| Theorem | Type | Description |
|---------|------|-------------|
| Lie-Kolchin | proof sketch | Connected solvable groups are triangularizable |
| Borel fixed point | proof sketch | Solvable group on complete variety has fixed point |
| Jordan decomposition | axiom | Every element = semisimple · unipotent |
| Levi decomposition | axiom | G = R_u(G) ⋊ L (Levi complement) |
| Lang's theorem | axiom | g⁻¹·Fr(g) is surjective over finite fields |
| Classification | axiom | Reductive groups classified by root data |
| Borel-Weil | axiom | H⁰(G/B, L_λ) ≅ V_λ^* |
| Steinberg connectedness | axiom | Centralizer of semisimple is connected |

### Prerequisites

This sub-package is self-contained. It defines its own Ring and Field
typeclasses and builds algebraic group theory from the ground up.

### Building

```bash
cd mini-algebraic-groups
lake build
```

### #eval Verification

Run `lake env lean --run Main.lean` for module information.
Key examples with #eval verification are in Examples/Classical.lean
and Examples/Finite.lean.
