# Prerequisite Dependency Tree — MiniAlgebraicGroups

## Core Prerequisites

```
Abstract Algebra (Groups, Rings, Fields)
├── Linear Algebra (Vector Spaces, Matrices, Determinants)
│   └── Multilinear Algebra (Tensor Products, Exterior Algebra)
│       └── Algebraic Groups (this module)
│           ├── Lie Theory (Lie Algebras, Exponential Map)
│           ├── Algebraic Geometry (Varieties, Sheaves, Schemes)
│           ├── Number Theory (Galois Cohomology, Automorphic Forms)
│           └── Representation Theory (Characters, Weights, Modules)
```

## Internal Dependencies

```
Core/Basic (L1: Definitions)
├── Core/Objects (L2: Structures)
│   ├── Core/Laws (L2: Properties)
│   │   ├── Morphisms/Hom (L2: Homomorphisms)
│   │   │   ├── Morphisms/Iso (L3: Isomorphisms)
│   │   │   │   └── Morphisms/Equivalence (L3: Equivalences)
│   │   │   └── Constructions/* (L3: Constructions)
│   │   │       └── Properties/* (L4: Properties)
│   │   │           └── Theorems/* (L4: Theorems)
│   │   │               ├── Examples/* (L6: Examples)
│   │   │               ├── Bridges/* (L7: Applications)
│   │   │               └── Advanced/* (L8: Advanced)
│   │   │                   └── Research/* (L9: Frontiers)
```

## Key Conceptual Dependencies

1. **Group Theory** → Algebraic Groups
   - Subgroups, normal subgroups, quotient groups
   - Group actions, orbits, stabilizers
   - Solvable, nilpotent, semisimple, simple groups

2. **Linear Algebra** → Matrix Groups
   - Matrices, determinants, eigenvalues
   - Vector spaces, linear transformations
   - Bilinear forms (symplectic, orthogonal)

3. **Algebraic Geometry** → Group Varieties
   - Affine varieties, Zariski topology
   - Regular functions, morphisms
   - Complete/projective varieties

4. **Lie Theory** → Lie Algebra of Algebraic Group
   - Tangent space, exponential map
   - Lie bracket, Jacobi identity
   - Root systems, Dynkin diagrams

5. **Representation Theory** → Representations of Algebraic Groups
   - Characters, weights, weight spaces
   - Irreducible representations
   - Highest weight theory, Weyl character formula
