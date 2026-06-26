# Dependency Map — Mini-Quantum-Groups

## Direct Dependencies
```
mini-quantum-groups
└── mini-object-kernel (from ../../../0. mini-math-kernel/mini-object-kernel)
    └── Provides: Basic types, Type u universe hierarchy
```

## Internal Dependencies
```
MiniQuantumGroups.lean (aggregator)
├── Core.Basic          ← (no internal deps)
├── Core.Laws           ← Core.Basic
├── Core.Objects        ← Core.Basic, Core.Laws
├── Theorems.Basic      ← Core.Basic, Core.Laws, Core.Objects
├── Theorems.Main       ← Core.Basic, Core.Laws, Core.Objects, Theorems.Basic
├── Theorems.Classification ← Core.Basic, Core.Laws
├── Theorems.UniversalProperties ← Core.Basic, Core.Objects
├── Constructions.*     ← Core.Basic, Core.Laws
├── Morphisms.Hom       ← Core.Basic
├── Morphisms.Iso       ← Core.Basic, Morphisms.Hom
├── Morphisms.Equivalence ← Core.Basic, Morphisms.Hom
├── Properties.*        ← Core.Basic, Core.Laws
├── Examples.Standard   ← Core.*, Properties.Invariants
├── Examples.Counterexamples ← Core.*
└── Bridges.*           ← Core.*, Properties.*
```

## External Dependencies (Future)
```
Potential dependencies for expanded module:
├── mini-linear-multilinear-algebra → tensor products over rings
├── mini-abstract-algebra-galois    → Hopf algebras over general rings
├── mini-lie-algebras               → classical U(g) for comparison
├── mini-category-theory            → braided monoidal categories
└── mini-character-theory           → q-characters
```
