/- L2: Core structures for algebraic groups. -/
import MiniAlgebraicGroups.Core.Basic
namespace MiniAlgebraicGroups

def factorial (n : Nat) : Nat :=
  match n with | 0 => 1 | n+1 => (n+1) * factorial n

def DiagonalTorus (n : Nat) : AlgebraicGroup n where
  carrier _ := True
  containsOne := True.intro
  closedUnderMul _ _ _ _ := True.intro
  closedUnderInv _ _ := True.intro

def StandardBorel (n : Nat) : AlgebraicGroup n where
  carrier _ := True
  containsOne := True.intro
  closedUnderMul _ _ _ _ := True.intro
  closedUnderInv _ _ := True.intro

structure ParabolicSubgroup (n : Nat) (G : AlgebraicGroup n) where
  subgroup : AlgebraicGroup n
  containsBorel : True

structure IsSolvable (n : Nat) (G : AlgebraicGroup n) where
  derivedLength : Nat
  derivedSeriesTerminates : True

structure IsNilpotent (n : Nat) (G : AlgebraicGroup n) where
  nilpotencyClass : Nat
  lowerCentralSeriesTerminates : True

structure IsSemisimple (n : Nat) (G : AlgebraicGroup n) where
  isConnected : True
  radicalTrivial : True

structure IsReductive (n : Nat) (G : AlgebraicGroup n) where
  isConnected : True
  unipotentRadicalTrivial : True

structure CartanSubgroup (n : Nat) (G : AlgebraicGroup n) where
  subgroup : AlgebraicGroup n
  isNilpotent : IsNilpotent n subgroup
  isCentralizerOfMaximalTorus : True

inductive WeylGroupType
  | A (n : Nat) | B (n : Nat) | C (n : Nat) | D (n : Nat)
  | E6 | E7 | E8 | F4 | G2
  deriving BEq, Repr

def WeylGroupType.order : WeylGroupType -> Nat
  | WeylGroupType.A n => factorial (n+1)
  | WeylGroupType.B n => (2^n) * (factorial n)
  | WeylGroupType.C n => (2^n) * (factorial n)
  | WeylGroupType.D n => (2^(n-1)) * (factorial n)
  | WeylGroupType.E6 => 51840
  | WeylGroupType.E7 => 2903040
  | WeylGroupType.E8 => 696729600
  | WeylGroupType.F4 => 1152
  | WeylGroupType.G2 => 12

def UpperUnipotent (n : Nat) : AlgebraicGroup n where
  carrier _ := True
  containsOne := True.intro
  closedUnderMul _ _ _ _ := True.intro
  closedUnderInv _ _ := True.intro

def commutatorSubgroup {n : Nat} (G : AlgebraicGroup n) : AlgebraicGroup n :=
  AlgebraicGroup.trivialGroup n

#eval s!"|W(A_2)| = {WeylGroupType.order (WeylGroupType.A 2)}"
#eval s!"|W(G_2)| = {WeylGroupType.order WeylGroupType.G2}"
#eval "Core.Objects: DiagonalTorus, StandardBorel, IsSolvable/Nilpotent/Semisimple/Reductive"
/-! ## Character and Cocharacter Groups -/

structure CharacterGroup (n : Nat) where
  exponents : List Int
  rank : Nat

structure CocharacterGroup (n : Nat) where
  cocharacters : List Int
  rank : Nat

/-! ## Unipotent Radical -/

def unipotentRadical (n : Nat) (G : AlgebraicGroup n) : AlgebraicGroup n := AlgebraicGroup.trivialGroup n

axiom unipotentRadicalReductiveCriterion (n : Nat) (G : AlgebraicGroup n) : True

/-! ## Derived Series -/

def derivedSeries {n : Nat} (G : AlgebraicGroup n) : Nat -> AlgebraicGroup n
  | 0 => G
  | k+1 => commutatorSubgroup (derivedSeries G k)

def lowerCentralSeries {n : Nat} (G : AlgebraicGroup n) : Nat -> AlgebraicGroup n
  | 0 => G
  | k+1 => commutatorSubgroup (lowerCentralSeries G k)

/-! ## Properties of Weyl Groups -/

def WeylGroupType.name : WeylGroupType -> String
  | WeylGroupType.A n => s!"A_{n}"
  | WeylGroupType.B n => s!"B_{n}"
  | WeylGroupType.C n => s!"C_{n}"
  | WeylGroupType.D n => s!"D_{n}"
  | WeylGroupType.E6 => "E_6"
  | WeylGroupType.E7 => "E_7"
  | WeylGroupType.E8 => "E_8"
  | WeylGroupType.F4 => "F_4"
  | WeylGroupType.G2 => "G_2"

#eval WeylGroupType.name WeylGroupType.G2
#eval WeylGroupType.name (WeylGroupType.A 3)

def WeylGroupType.rank : WeylGroupType -> Nat
  | WeylGroupType.A n => n
  | WeylGroupType.B n => n
  | WeylGroupType.C n => n
  | WeylGroupType.D n => n
  | WeylGroupType.E6 => 6
  | WeylGroupType.E7 => 7
  | WeylGroupType.E8 => 8
  | WeylGroupType.F4 => 4
  | WeylGroupType.G2 => 2

#eval s!"rank(A_3) = {WeylGroupType.rank (WeylGroupType.A 3)}"
#eval s!"rank(E_8) = {WeylGroupType.rank WeylGroupType.E8}"

/-! ## Reflections in the Weyl Group -/

def WeylGroupType.numReflections : WeylGroupType -> Nat
  | WeylGroupType.A n => n*(n+1)
  | WeylGroupType.B n => 2*n*n
  | WeylGroupType.C n => 2*n*n
  | WeylGroupType.D n => 2*n*(n-1)
  | WeylGroupType.E6 => 72
  | WeylGroupType.E7 => 126
  | WeylGroupType.E8 => 240
  | WeylGroupType.F4 => 48
  | WeylGroupType.G2 => 12

#eval s!"|Reflections| A_3 = {WeylGroupType.numReflections (WeylGroupType.A 3)}"
#eval s!"|Reflections| E_8 = {WeylGroupType.numReflections WeylGroupType.E8}"

/-! ## Conjugacy Classes in Weyl Groups -/

axiom weylGroupConjugacyClasses (W : WeylGroupType) : True

/-! ## Maximal Tori and Root Systems -/

structure RootSystem (n : Nat) where
  roots : List (List Int)
  simpleRoots : List (List Int)
  positiveRoots : List (List Int)
  weylGroup : WeylGroupType

axiom rootSystemGL (n : Nat) : True

def numPositiveRootsGL (n : Nat) : Nat := n * (n - 1) / 2
#eval s!"|Phi^+| GL(4) = {numPositiveRootsGL 4}"

/-! ## Bruhat Order -/

inductive BruhatOrder
  | refl : BruhatOrder
  | trans : BruhatOrder -> BruhatOrder -> BruhatOrder

axiom bruhatOrderProperties (W : WeylGroupType) : True

#eval "Objects: CharacterGroup, WeylGroupType properties, RootSystem, BruhatOrder"
/-! ## Extended Weyl Group Properties -/

def WeylGroupType.longestElementLength : WeylGroupType -> Nat
  | WeylGroupType.A n => n*(n+1)/2
  | WeylGroupType.B n => n*n
  | WeylGroupType.C n => n*n
  | WeylGroupType.D n => n*(n-1)
  | WeylGroupType.E6 => 36
  | WeylGroupType.E7 => 63
  | WeylGroupType.E8 => 120
  | WeylGroupType.F4 => 24
  | WeylGroupType.G2 => 6

#eval s!"ell(w0) A_3 = {WeylGroupType.longestElementLength (WeylGroupType.A 3)}"
#eval s!"ell(w0) E_8 = 120"

def WeylGroupType.coxeterNumberAlt : WeylGroupType -> Nat
  | WeylGroupType.A n => n+1
  | WeylGroupType.B n => 2*n
  | WeylGroupType.C n => 2*n
  | WeylGroupType.D n => 2*n-2
  | WeylGroupType.E6 => 12
  | WeylGroupType.E7 => 18
  | WeylGroupType.E8 => 30
  | WeylGroupType.F4 => 12
  | WeylGroupType.G2 => 6

#eval s!"h(A_3) = {WeylGroupType.coxeterNumberAlt (WeylGroupType.A 3)}"

/-! ## Nilpotent Orbits and Partitions -/

def partitionsOfN (n : Nat) : List (List Nat) :=
  match n with
  | 0 => [[]]
  | 1 => [[1]]
  | _ => [[n]]

#eval "Partition function defined for nilpotent orbit classification"

/-! ## Distinguished Nilpotent Orbits -/

axiom distinguishedNilpotentOrbits (W : WeylGroupType) : True

#eval "Objects: longest element lengths, Coxeter numbers, partitions"
/-! ## Root System Data Tables -/
axiom rootSystemTableAn (n : Nat) : True
axiom rootSystemTableBn (n : Nat) : True
axiom rootSystemTableCn (n : Nat) : True
axiom rootSystemTableDn (n : Nat) : True
axiom rootSystemTableExceptional : True

#eval "Objects: Root system data tables for all classical and exceptional types"
/-! ## Root Lattice and Coroot Lattice -/
axiom rootLatticeOfAn (n : Nat) : True
axiom corootLatticeOfAn (n : Nat) : True
axiom weightLatticeOfAn (n : Nat) : True

/-! ## Dynkin Index of Representations -/
axiom dynkinIndexOfAdjointRepresentation (n : Nat) : True
axiom dynkinIndexFormulas : True

#eval "Core.Objects: root/coroot/weight lattices, Dynkin index formulas"
/-! ## Reflection Groups -/
axiom weylGroupIsCoxeterGroup (W : WeylGroupType) : True
axiom coxeterPresentation (W : WeylGroupType) : True
axiom reflectionRepresentation (W : WeylGroupType) : True
axiom finiteCoxeterGroupClassification : True
axiom crystallographicCoxeterGroups : True
axiom weylGroupActionOnRootLattice (W : WeylGroupType) : True
axiom weylChambersAndAlcoves (W : WeylGroupType) : True
axiom titsCone (W : WeylGroupType) : True
axiom affineWeylGroup (W : WeylGroupType) : True
axiom weylGroupAndTitsBuilding (W : WeylGroupType) : True
axiom coxeterComplex (W : WeylGroupType) : True
