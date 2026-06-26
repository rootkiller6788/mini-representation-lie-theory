/-
# MiniLieGroups

Lie group theory: Lie groups, Lie algebras, exponential map,
adjoint representation, Lie subgroups, quotient groups,
classical Lie groups (GL, SL, O, SO, U, SU, Sp),
Lie's theorems, structure theory, and applications.

This is a sub-package of mini-representation-lie-theory
in the mini-everything-math ecosystem.
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.Core.Smooth
import MiniLieGroups.Core.TangentSpace
import MiniLieGroups.LieAlgebra.Definition
import MiniLieGroups.LieAlgebra.Exponential
import MiniLieGroups.LieAlgebra.Adjoint
import MiniLieGroups.Morphisms.Hom
import MiniLieGroups.Morphisms.Iso
import MiniLieGroups.Constructions.Subgroups
import MiniLieGroups.Constructions.Quotients
import MiniLieGroups.Constructions.Products
import MiniLieGroups.Classical.GeneralLinear
import MiniLieGroups.Classical.Orthogonal
import MiniLieGroups.Classical.Unitary
import MiniLieGroups.Classical.Symplectic
import MiniLieGroups.Theorems.Basic
import MiniLieGroups.Theorems.LieCorrespondence
import MiniLieGroups.Theorems.Structure
import MiniLieGroups.Proofs.Techniques
import MiniLieGroups.Applications.Physics
import MiniLieGroups.Applications.Geometry
import MiniLieGroups.Advanced.InfiniteDim
import MiniLieGroups.Advanced.LoopGroups