import MiniRepresentationTheory.Core.Basic

/-!
# Representation Theory - Core Objects

Formal characters, representations as modules, weight space
decompositions, and the character ring.

Levels: L1 (Definitions), L2 (Core Concepts), L3 (Math Structures)
-/

namespace MiniRepresentationTheory

/-! ## Formal Character

A formal character is an element of the group ring Z[Lambda]
of the weight lattice. It is written as a finite sum
ch = sum_{lambda} m_lambda * e^lambda
where m_lambda are the weight multiplicities.
-/

structure FormalChar where
  terms : List (Weight × Int)
deriving BEq, Repr, Inhabited

namespace FormalChar

def zero : FormalChar := { terms := [] }
def empty : FormalChar := { terms := [] }

def singleton (w : Weight) (mult : Int) : FormalChar :=
  { terms := [(w, mult)] }

def fromWeight (w : Weight) : FormalChar :=
  singleton w 1

def add (c1 c2 : FormalChar) : FormalChar :=
  { terms := c1.terms ++ c2.terms }

def scale (k : Int) (c : FormalChar) : FormalChar :=
  { terms := c.terms.map fun (w, m) => (w, m * k) }

def mul (c1 c2 : FormalChar) : FormalChar :=
  { terms := c1.terms.foldl (fun acc (w1, m1) =>
      acc ++ c2.terms.map fun (w2, m2) =>
        (Weight.add w1 w2, m1 * m2)) [] }

def neg (c : FormalChar) : FormalChar := scale (-1) c

def sub (c1 c2 : FormalChar) : FormalChar := add c1 (neg c2)

def combineLikeTerms (c : FormalChar) : FormalChar :=
  let grouped := c.terms.foldl (fun (acc : List (Weight × Int)) (w, m) =>
    match acc.find? (fun (w', _) => Weight.equal w w') with
    | some _ =>
      acc.map fun (w', m') =>
        if Weight.equal w w' then (w', m' + m) else (w', m')
    | none => acc ++ [(w, m)]
    ) []
  { terms := grouped.filter (fun (_, m) => m != 0) }

def mapWeights (c : FormalChar) (f : Weight -> Weight) : FormalChar :=
  { terms := c.terms.map fun (w, m) => (f w, m) }

def equal (c1 c2 : FormalChar) : Bool :=
  let c1' := combineLikeTerms c1
  let c2' := combineLikeTerms c2
  c1'.terms.length == c2'.terms.length

def weightMultiplicity (c : FormalChar) (w : Weight) : Int :=
  c.terms.foldl (fun acc (w', m) =>
    if Weight.equal w w' then acc + m else acc) 0

def support (c : FormalChar) : List Weight :=
  c.terms.map Prod.fst

/-| Lexicographic comparison of two integer lists -/
def lexGreater (xs ys : List Int) : Bool :=
  match xs, ys with
  | [], [] => false
  | _, [] => false
  | [], _ => true
  | x::xs', y::ys' =>
    if x > y then true
    else if x < y then false
    else lexGreater xs' ys'

/-| Find the highest weight: the lexicographically largest weight -/
def highestWeight (c : FormalChar) : Option Weight :=
  match c.support with
  | [] => none
  | w::ws =>
    some (ws.foldl (fun maxW w =>
      if lexGreater w.components maxW.components then w else maxW
    ) w)

def dimension (c : FormalChar) : Int :=
  c.terms.map Prod.snd |>.sum

def isEffective (c : FormalChar) : Bool :=
  c.terms.all (fun (_, m) => m >= 0)

def numberOfTerms (c : FormalChar) : Nat :=
  c.terms.length

def dominantSupport (c : FormalChar) : List Weight :=
  c.support |>.filter (fun w => Weight.isDominantTypeA w)

end FormalChar

/-! ## Representation

A finite-dimensional representation V of a semisimple Lie algebra g
is determined up to isomorphism by its formal character.
-/

structure Representation where
  algebraRank : Nat
  highestWt : Weight
  character : FormalChar
  dim : Nat
deriving BEq, Repr, Inhabited

namespace Representation

def trivial (rank : Nat) : Representation :=
  { algebraRank := rank,
    highestWt := Weight.zero rank,
    character := FormalChar.fromWeight (Weight.zero rank),
    dim := 1 }

def fromChar (rank : Nat) (hwt : Weight) (ch : FormalChar) : Representation :=
  { algebraRank := rank,
    highestWt := hwt,
    character := ch,
    dim := (ch.dimension).toNat }

def weightMultiplicity (V : Representation) (w : Weight) : Int :=
  FormalChar.weightMultiplicity V.character w

def weightSpaceDimension (V : Representation) (w : Weight) : Nat :=
  (V.weightMultiplicity w).toNat

def allWeights (V : Representation) : List Weight :=
  FormalChar.support V.character

def dominantWeights (V : Representation) : List Weight :=
  FormalChar.dominantSupport V.character

def highestWeightVec (V : Representation) : Weight := V.highestWt

def isIrreducible (V : Representation) : Bool :=
  V.weightMultiplicity V.highestWt == 1

def dual (V : Representation) : Representation :=
  let dualChar := FormalChar.mapWeights V.character (fun w => Weight.neg w)
  { V with
    highestWt := Weight.neg V.highestWt,
    character := dualChar }

def tensorProd (V W : Representation) : Representation :=
  { algebraRank := V.algebraRank,
    highestWt := Weight.add V.highestWt W.highestWt,
    character := FormalChar.mul V.character W.character,
    dim := V.dim * W.dim }

def directSum (V W : Representation) : Representation :=
  { algebraRank := V.algebraRank,
    highestWt := V.highestWt,
    character := FormalChar.add V.character W.character,
    dim := V.dim + W.dim }

def isSelfDual (V : Representation) : Bool :=
  FormalChar.equal V.character (Representation.dual V).character

end Representation

/-! ## Weight Space Decomposition

Every finite-dimensional representation admits a weight space
decomposition V = bigoplus_{lambda} V_lambda.
-/

structure WeightSpace where
  weight : Weight
  multiplicity : Nat
deriving Repr

structure WeightDecomposition where
  rank : Nat
  spaces : List WeightSpace
  totalDim : Nat
deriving Repr

namespace WeightDecomposition

def fromRepresentation (V : Representation) : WeightDecomposition :=
  let spaces := V.allWeights |>.map fun w =>
    { weight := w, multiplicity := V.weightSpaceDimension w }
  { rank := V.algebraRank,
    spaces := spaces,
    totalDim := V.dim }

def weightSpaces (wd : WeightDecomposition) : List WeightSpace := wd.spaces

def dimension (wd : WeightDecomposition) : Nat := wd.totalDim

def findSpace (wd : WeightDecomposition) (w : Weight) : Option WeightSpace :=
  wd.spaces.find? (fun ws => Weight.equal ws.weight w)

def add (wd1 wd2 : WeightDecomposition) : WeightDecomposition :=
  let merged := wd1.spaces ++ wd2.spaces
  { rank := wd1.rank,
    spaces := merged,
    totalDim := wd1.totalDim + wd2.totalDim }

end WeightDecomposition

/-! ## Character Ring Operations

The set of formal characters forms a ring under addition
and convolution (tensor product). This is the representation ring R(g).
-/

structure CharacterRing where
  rank : Nat
  generators : List FormalChar
  relations : List (FormalChar × FormalChar)
deriving Repr, Inhabited

namespace CharacterRing

def empty (rank : Nat) : CharacterRing :=
  { rank := rank, generators := [], relations := [] }

def addGenerator (ring : CharacterRing) (ch : FormalChar) : CharacterRing :=
  { ring with generators := ring.generators ++ [ch] }

def addRelation (ring : CharacterRing) (lhs rhs : FormalChar) : CharacterRing :=
  { ring with relations := ring.relations ++ [(lhs, rhs)] }

def fundamentalChars (ring : CharacterRing) : List FormalChar :=
  ring.generators

def isInRing (ring : CharacterRing) (ch : FormalChar) : Bool :=
  ring.generators.any (fun g => FormalChar.equal g ch)

end CharacterRing

end MiniRepresentationTheory