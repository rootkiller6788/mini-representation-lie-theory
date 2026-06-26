/-
# MiniCharacterTheory.Constructions.CharacterTable

L3: Construction and manipulation of character tables.
Extends the CharacterTable type defined in Core/Orthogonality.
-/

import MiniCharacterTheory.Core.Orthogonality
import MiniCharacterTheory.Core.AxiomCompat

namespace MiniCharacterTheory

/-! ## Conjugacy Class -/

structure ConjugacyClass {n : Nat} (G : FiniteGroup n) where
  representative : Fin n
  size : Nat
  elements : List (Fin n)

namespace ConjugacyClass

variable {n : Nat} {G : FiniteGroup n}

def ofElement (g : Fin n) : ConjugacyClass G :=
  { representative := g, size := 1, elements := [g] }

def classEquation (classes : List (ConjugacyClass G)) : Prop :=
  let totalSize := classes.foldl (fun acc c => acc + c.size) 0
  totalSize = n

end ConjugacyClass

/-! ## Character Table Extended Operations -/

namespace CharacterTable

variable {n : Nat} {G : FiniteGroup n}

/-- Construct a character table from data -/
def fromData (irrChars : List (IrreducibleChar G))
    (conjClasses : List (ConjugacyClass G)) : CharacterTable G :=
  let reps := conjClasses.map ConjugacyClass.representative
  let sizes := conjClasses.map ConjugacyClass.size
  let entries := irrChars.map (fun chi =>
    reps.map (fun g => IrreducibleChar.valueAt chi g))
  { irrChars := irrChars
    conjClassReps := reps
    classSizes := sizes
    tableEntries := entries }

/-- Get entry chi_i(g_j) -/
def getEntry (CT : CharacterTable G) (i j : Nat) : Option CharValue :=
  match CT.tableEntries.get? i with
  | none => none
  | some row => row.get? j

/-- First column (degrees) -/
def firstColumn (CT : CharacterTable G) : List CharValue :=
  CT.irrChars.map (fun chi => IrreducibleChar.degree chi)

/-- Check sum of squares of first column = |G| -/
def checkSquareIdentity (CT : CharacterTable G) : Bool :=
  let squares := (CT.firstColumn).map (fun d => d.mul d)
  let sumSq := squares.foldl (fun acc x => acc.add x) CharValue.zero
  sumSq == CharValue.ofNat n

/-- Get degree for i-th irr char -/
def getDegree (CT : CharacterTable G) (i : Nat) : Option CharValue :=
  CT.firstColumn.get? i

/-- Get row i -/
def getRow (CT : CharacterTable G) (i : Nat) : Option (List CharValue) :=
  CT.tableEntries.get? i

/-- Get column j -/
def getColumn (CT : CharacterTable G) (j : Nat) : List CharValue :=
  CT.irrChars.map (fun chi =>
    match CT.conjClassReps.get? j with
    | none => CharValue.zero
    | some g => IrreducibleChar.valueAt chi g)

/-- Check square (numIrr = numClasses) -/
def checkSquare (CT : CharacterTable G) : Bool :=
  CT.irrChars.length == CT.conjClassReps.length

/-- Character table as matrix -/
def asMatrix (CT : CharacterTable G) : List (List CharValue) :=
  CT.tableEntries

#eval "Constructions.CharacterTable: ConjugacyClass, table construction, row/column ops"
#eval "Character table square check, matrix representation"

end CharacterTable

end MiniCharacterTheory
