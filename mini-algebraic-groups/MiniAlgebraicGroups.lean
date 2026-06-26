/-
# MiniAlgebraicGroups

The algebraic groups sub-package of mini-everything-math.

Algebraic groups are group objects in the category of algebraic varieties.
Linear algebraic groups are affine algebraic groups that are isomorphic to
a closed subgroup of GL(n) for some n. This package develops:

## Sub-packages
- Core         — Algebraic groups, tori, unipotent groups, Borel subgroups
- Morphisms    — Homomorphisms, isogenies, equivalences
- Constructions — Products, subgroups, quotients, flag varieties
- Properties   — Invariants, representations, classification data
- Theorems     — Lie-Kolchin, Borel fixed point, Jordan decomposition
- Examples     — Classical groups GL/SL/Sp/SO, finite groups of Lie type
- Bridges      — To Lie theory, geometry, number theory
- Advanced     — Frobenius morphism, Springer resolution
- Research     — Affine Grassmannian, geometric Satake (documentation)
-/

import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Morphisms.Hom
import MiniAlgebraicGroups.Morphisms.Iso
import MiniAlgebraicGroups.Morphisms.Equivalence
import MiniAlgebraicGroups.Constructions.Products
import MiniAlgebraicGroups.Constructions.Subgroups
import MiniAlgebraicGroups.Constructions.Quotients
import MiniAlgebraicGroups.Properties.Invariants
import MiniAlgebraicGroups.Properties.Representation
import MiniAlgebraicGroups.Properties.Classification
import MiniAlgebraicGroups.Theorems.LieKolchin
import MiniAlgebraicGroups.Theorems.BorelFixedPoint
import MiniAlgebraicGroups.Theorems.JordanDecomp
import MiniAlgebraicGroups.Theorems.Main
import MiniAlgebraicGroups.Examples.Classical
import MiniAlgebraicGroups.Examples.Finite
import MiniAlgebraicGroups.Bridges.ToLieTheory
import MiniAlgebraicGroups.Bridges.ToGeometry
import MiniAlgebraicGroups.Bridges.ToNumberTheory
import MiniAlgebraicGroups.Advanced.FrobeniusMorphism
import MiniAlgebraicGroups.Advanced.SpringerResolution
import MiniAlgebraicGroups.Research.Frontiers
