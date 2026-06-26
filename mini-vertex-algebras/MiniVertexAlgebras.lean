/-
# MiniVertexAlgebras

Vertex algebras and vertex operator algebras: formalization from first principles.
Covers L1-L9 knowledge levels.

A vertex algebra is a vector space V equipped with:
- vacuum |0> in V
- translation operator T: V -> V
- state-field correspondence Y(., z): V -> End(V)[[z, z^{-1}]]
satisfying vacuum, translation, and locality axioms.

This module covers:
- L1: VertexAlgebra, VOA, Field, Mode, Vacuum, Translation
- L2: Normal ordering, OPE, Conformal vector, Characters
- L3: Modules, intertwining operators, subalgebras, ideals
- L4: Goddard uniqueness, Dong lemma, associativity, Zhu theorem
- L5: Induction on weight, normal ordering, contour deformation
- L6: Heisenberg VOA, Virasoro VOA, Lattice VOA, Commutative VA
- L7: Conformal Field Theory, Representation Theory connections
- L8: Chiral algebras, W-algebras, Factorization algebras
- L9: Geometric Langlands, Moonshine, quantum geometric Langlands
-/

import MiniVertexAlgebras.Core.AxiomCompat
import MiniVertexAlgebras.Core.Basic
import MiniVertexAlgebras.Core.FieldCalculus
import MiniVertexAlgebras.Core.Extended
