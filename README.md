# Mini Representation Theory & Lie Theory

A collection of **from-scratch, zero-dependency Lean 4 implementations** of university-level representation theory and Lie theory. Each module formalizes core definitions, theorems, canonical examples, and applications — from algebraic groups and character tables to quantum groups, vertex algebras, and Kac-Moody algebras — providing a verifiable, runnable mathematical knowledge base.

## Sub-Modules

| Sub-Module | Topics | Key Courses |
|------------|--------|-------------|
| [mini-algebraic-groups](mini-algebraic-groups/) | Linear algebraic groups, structure theory (solvable/nilpotent/semisimple/reductive), root data, Dynkin diagrams, Borel-Tits, Lie-Kolchin theorem | MIT 18.755, Stanford MATH 210B, Cambridge Part III Alg Geom |
| [mini-character-theory](mini-character-theory/) | Character theory of finite groups, orthogonality relations, Frobenius reciprocity, character tables, Burnside's p^a q^b theorem, Brauer induction, modular characters | MIT 18.704/18.715, Harvard Math 55/251, Cambridge Part III Rep Theory |
| [mini-kac-moody-algebras](mini-kac-moody-algebras/) | Generalized Cartan matrices, affine/hyperbolic root systems, Weyl groups, Verma modules, Weyl-Kac character formula, denominator identity, Macdonald identities | MIT 18.785, Berkeley MATH 274, Oxford Part C Lie Algebras |
| [mini-lie-algebras](mini-lie-algebras/) | Lie algebras, subalgebras/ideals, derived series, lower central series, Killing form, root spaces, Cartan subalgebras, Dynkin diagrams, classification, PBW theorem | MIT 18.755, Harvard Math 210B, Cambridge Part III Lie Algebras |
| [mini-lie-groups](mini-lie-groups/) | Lie groups and Lie algebras, smooth manifolds, exponential map, adjoint representation, classical groups (GL/SL/O/SO/U/SU/Sp/Spin), exceptional groups, gauge theory | MIT 18.755, Stanford MATH 210C, Cambridge Part III Lie Groups |
| [mini-quantum-groups](mini-quantum-groups/) | Drinfeld-Jimbo quantum groups, Hopf algebras, R-matrices, Yang-Baxter equation, braided tensor categories, knot invariants (Jones polynomial), topological quantum computing | Berkeley MATH 256, Princeton MAT 560, Cambridge Part III Quantum Groups |
| [mini-representation-theory](mini-representation-theory/) | Semisimple Lie algebra representations, highest weight theory, Weyl character/dimension formulas, BGG Category O, Verma modules, Clebsch-Gordan decomposition, angular momentum | MIT 18.715, Harvard Math 251, Stanford MATH 210C |
| [mini-vertex-algebras](mini-vertex-algebras/) | Vertex algebras and vertex operator algebras (VOAs), Goddard uniqueness, Dong lemma, Zhu theorem, Heisenberg/Virasoro/Lattice/Monster VOAs, conformal field theory | MIT 18.785, Berkeley MATH 274, Cambridge Part III Vertex Algebras |

## Design Philosophy

- **Zero external dependencies** — pure Lean 4 (v4.7.0+), self-contained algebraic foundations defined internally
- **Self-contained modules** — each directory has its own `lakefile.lean`, `Main.lean`, module aggregator, source tree, and docs
- **Theory-to-code mapping** — every module follows a 9-level knowledge hierarchy (L1 definitions → L9 research frontiers)
- **Computational verification** — key theorems validated via `#eval` and `native_decide`, zero `sorry` across all modules

## Building

Each module is standalone. Navigate to a module directory and run:

```bash
cd mini-algebraic-groups
lake build      # build everything
lean --run Main.lean  # run module entry point
```

Requires **Lean 4** (v4.7.0+) installed via [elan](https://github.com/leanprover/elan).

## Project Structure

```
mini-representation-lie-theory/
├── mini-algebraic-groups/       # Linear algebraic groups, Borel-Tits structure theory, classification
├── mini-character-theory/       # Character theory of finite groups, Frobenius reciprocity, modular characters
├── mini-kac-moody-algebras/     # Generalized Cartan matrices, Weyl-Kac formula, affine/hyperbolic types
├── mini-lie-algebras/           # Lie algebras, root systems, Killing form, Cartan criteria, classification
├── mini-lie-groups/             # Lie groups, exponential map, classical/exceptional groups, gauge theory
├── mini-quantum-groups/         # Quantum groups, R-matrices, Yang-Baxter, knot invariants, anyons
├── mini-representation-theory/  # Highest weight theory, Weyl formulas, BGG Category O, Verma modules
└── mini-vertex-algebras/        # Vertex operator algebras, Goddard/Zhu theorems, Monstrous Moonshine
```

## License

MIT
