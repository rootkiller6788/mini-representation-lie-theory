import MiniRepresentationTheory.Core.Basic
import MiniRepresentationTheory.Core.Objects

/-!
# Representation Theory - Core Laws

Homomorphisms of representations, subrepresentations, quotient
representations, and the category of representations.

Levels: L1 (Definitions), L2 (Core Concepts)
-/

namespace MiniRepresentationTheory

/-! ## Representation Homomorphisms

An intertwining operator (or G-module homomorphism) between two
representations V and W is a linear map commuting with the group action.
-/

structure RepresentationHom (V W : Representation) where
  source : Representation := V
  target : Representation := W
  -- In the combinatorial model, a homomorphism is specified by
  -- its action on weight spaces (a list of pairs mapping weights)
  weightMap : List (Weight × Weight)
  isIntertwining : Bool := true
deriving Repr

namespace RepresentationHom

def identity (V : Representation) : RepresentationHom V V :=
  { weightMap := V.allWeights.map fun w => (w, w),
    isIntertwining := true }

def compose {V W X : Representation}
    (f : RepresentationHom V W) (g : RepresentationHom W X) : RepresentationHom V X :=
  { weightMap := f.weightMap.foldl (fun acc (w1, w2) =>
      acc ++ g.weightMap.filterMap fun (w2', w3) =>
        if Weight.equal w2 w2' then some (w1, w3) else none) [],
    isIntertwining := f.isIntertwining && g.isIntertwining }

def isZero (f : RepresentationHom V W) : Bool :=
  f.weightMap.isEmpty

def mapWeight (f : RepresentationHom V W) (w : Weight) : Option Weight :=
  f.weightMap.find? (fun (src, _) => Weight.equal src w) |>.map Prod.snd

def kernelWeights (f : RepresentationHom V W) : List Weight :=
  f.weightMap.filterMap fun (w1, w2) =>
    if Weight.isZero w2 then some w1 else none

def imageWeights (f : RepresentationHom V W) : List Weight :=
  f.weightMap.map Prod.snd

end RepresentationHom

/-! ## Subrepresentations

A subrepresentation is an invariant subspace of a representation.
-/

structure Subrepresentation where
  parent : Representation
  includedWeights : List Weight
  dimension : Nat
deriving Repr

namespace Subrepresentation

def fromWeights (V : Representation) (weights : List Weight) : Subrepresentation :=
  let dim := weights.foldl (fun acc w =>
    acc + V.weightSpaceDimension w) 0
  { parent := V,
    includedWeights := weights,
    dimension := dim }

def complement (S : Subrepresentation) : Subrepresentation :=
  let allWts := S.parent.allWeights
  let complWts := allWts.filter (fun w => !S.includedWeights.any (fun sw => Weight.equal sw w))
  fromWeights S.parent complWts

def isInvariant (S : Subrepresentation) : Bool :=
  -- A subspace is invariant if it is a union of weight spaces
  S.includedWeights.all (fun w =>
    S.parent.allWeights.any (fun pw => Weight.equal w pw))

def isProper (S : Subrepresentation) : Bool :=
  S.dimension < S.parent.dim && S.dimension > 0

def containsHighestWeight (S : Subrepresentation) : Bool :=
  S.includedWeights.any (fun w => Weight.equal w S.parent.highestWt)

def restriction (S : Subrepresentation) : Representation :=
  let weights := S.includedWeights
  let char := FormalChar.zero
  let char' := weights.foldl (fun acc w =>
    let mult := S.parent.weightMultiplicity w
    FormalChar.add acc (FormalChar.singleton w mult))
    char
  { algebraRank := S.parent.algebraRank,
    highestWt :=
      match weights with
      | [] => Weight.zero S.parent.algebraRank
      | w::_ => w,
    character := char',
    dim := S.dimension }

end Subrepresentation

/-! ## Quotient Representations

Given a subrepresentation U of V, the quotient V/U is naturally
a representation.
-/

structure QuotientRepresentation where
  numerator : Representation
  denominator : Subrepresentation
  quotientWeights : List Weight
  quotientDim : Nat
deriving Repr

namespace QuotientRepresentation

def fromSubrepresentation (V : Representation) (U : Subrepresentation) : QuotientRepresentation :=
  let qWeights := V.allWeights.filter (fun w =>
    !U.includedWeights.any (fun uw => Weight.equal w uw))
  let qDim := qWeights.foldl (fun acc w =>
    acc + V.weightSpaceDimension w) 0
  { numerator := V,
    denominator := U,
    quotientWeights := qWeights,
    quotientDim := qDim }

def asRepresentation (Q : QuotientRepresentation) : Representation :=
  let char := Q.quotientWeights.foldl (fun acc w =>
    let mult := Q.numerator.weightMultiplicity w
    FormalChar.add acc (FormalChar.singleton w mult))
    FormalChar.zero
  { algebraRank := Q.numerator.algebraRank,
    highestWt :=
      match Q.quotientWeights with
      | [] => Weight.zero Q.numerator.algebraRank
      | w::_ => w,
    character := char,
    dim := Q.quotientDim }

end QuotientRepresentation

/-! ## Isomorphism of Representations

Two representations are isomorphic if their formal characters are equal
(for semisimple Lie algebras over C, this is necessary and sufficient).
-/

structure RepresentationIso (V W : Representation) where
  forward : RepresentationHom V W
  inverse : RepresentationHom W V
  isIdentity : Bool :=
    (RepresentationHom.compose forward inverse).isIntertwining &&
    (RepresentationHom.compose inverse forward).isIntertwining
deriving Repr

namespace RepresentationIso

def isIsomorphic (V W : Representation) : Bool :=
  -- Two representations of a semisimple Lie algebra are isomorphic
  -- iff their formal characters are equal (complete reducibility)
  FormalChar.equal V.character W.character && V.dim == W.dim

def trivialIso (V : Representation) : RepresentationIso V V :=
  { forward := RepresentationHom.identity V,
    inverse := RepresentationHom.identity V,
    isIdentity := true }

end RepresentationIso

/-! ## Category Structure

The category Rep(g) of finite-dimensional representations.
-/

structure RepCategory where
  rank : Nat
  objects : List Representation
  morphismCount : Nat
deriving Repr, Inhabited

namespace RepCategory

def empty (rank : Nat) : RepCategory :=
  { rank := rank, objects := [], morphismCount := 0 }

def addObject (cat : RepCategory) (V : Representation) : RepCategory :=
  { cat with objects := cat.objects ++ [V] }

def addMorphism (cat : RepCategory) (V W : Representation) (f : RepresentationHom V W) : RepCategory :=
  { cat with morphismCount := cat.morphismCount + 1 }

def hasObject (cat : RepCategory) (V : Representation) : Bool :=
  cat.objects.any (fun obj => FormalChar.equal obj.character V.character)

def irreducibleObjects (cat : RepCategory) : List Representation :=
  cat.objects.filter (fun V => V.isIrreducible)

end RepCategory

end MiniRepresentationTheory