# Architecture — Mini-Quantum-Groups

## Package Structure

```
MiniQuantumGroups
├── Core
│   ├── Basic    — q-calculus foundation, generator types
│   ├── Laws     — Algebraic identities with proofs
│   └── Objects  — Concrete quantum group objects
├── Theorems
│   ├── Basic              — Core theorems (q-binomial, PBW)
│   ├── Main               — Yang-Baxter, knot invariants
│   ├── Classification     — Lie type classification
│   └── UniversalProperties — Drinfeld double, Tannaka-Krein
├── Constructions
│   ├── Products   — Tensor/smash/bicrossed products
│   ├── Quotients  — Hopf ideals, homogeneous spaces
│   ├── Subobjects — Quantum subgroups, coideals
│   └── Universal  — FRT/RTT, quantum double
├── Morphisms
│   ├── Hom        — Hopf algebra homomorphisms
│   ├── Iso        — Isomorphisms, Drinfeld twists
│   └── Equivalence — Monoidal/Morita equivalence
├── Properties
│   ├── Invariants          — Jones, Kauffman, quantum dimensions
│   ├── Preservation        — Property stability
│   └── ClassificationData  — Dynkin diagrams, Weyl groups
├── Examples
│   ├── Standard        — U_q(sl_2), quantum plane, Jones
│   └── Counterexamples — Root of unity edge cases
└── Bridges
    ├── ToAlgebra     — Lie bialgebras, q-analysis
    ├── ToTopology    — Knot theory, 3-manifolds, TQFT
    ├── ToGeometry    — Quantum homogeneous spaces
    └── ToComputation — Anyons, topological QC
```

## Design Principles
1. **Computable First**: All core definitions are computable (#eval)
2. **Proven Theorems**: No `sorry`, all theorems have Lean proofs
3. **Modular**: Each submodule is self-contained with clear imports
4. **Documented**: Every definition has doc-strings explaining mathematical context
5. **Bridged**: Connections to algebra, topology, geometry, computation
