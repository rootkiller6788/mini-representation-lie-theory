/-
# MiniCharacterTheory

Character theory of finite groups: representations, characters,
orthogonality relations, Frobenius reciprocity, character tables,
Burnside's p^a q^b theorem, Brauer's induction theorem,
modular characters, and applications to group theory and number theory.

This is a sub-package of mini-representation-lie-theory in the
mini-everything-math ecosystem. It imports all submodules.
-/

import MiniCharacterTheory.Core.Basic
import MiniCharacterTheory.Core.Operations
import MiniCharacterTheory.Core.Orthogonality
import MiniCharacterTheory.Core.AxiomCompat
import MiniCharacterTheory.Constructions.CharacterTable
import MiniCharacterTheory.Constructions.InducedCharacters
import MiniCharacterTheory.Constructions.TensorOperations
import MiniCharacterTheory.Properties.InnerProduct
import MiniCharacterTheory.Properties.Degrees
import MiniCharacterTheory.Properties.Integrality
import MiniCharacterTheory.Theorems.Fundamental
import MiniCharacterTheory.Theorems.Burnside
import MiniCharacterTheory.Theorems.CharacterRing
import MiniCharacterTheory.Examples.SmallGroups
import MiniCharacterTheory.Examples.AbelianGroups
import MiniCharacterTheory.Examples.Computational
import MiniCharacterTheory.Applications.ToGroupTheory
import MiniCharacterTheory.Applications.ToNumberTheory
import MiniCharacterTheory.Advanced.BrauerTheory
import MiniCharacterTheory.Advanced.ModularTheory
