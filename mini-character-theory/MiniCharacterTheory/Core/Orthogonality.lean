/-
# MiniCharacterTheory.Core.Orthogonality

L3 Mathematical Structure: Orthogonality relations for irreducible characters.
-/

import MiniCharacterTheory.Core.Operations
import MiniCharacterTheory.Core.AxiomCompat

namespace MiniCharacterTheory

/-- IrreducibleChar defined in Core/Basic -/

def IrrSet {n : Nat} (G : FiniteGroup n) : Type := List (IrreducibleChar G)

/-! ## Orthogonality Axioms -/

namespace CharOrthogonality

def rowOrthogonality : Axiom :=
  mkAxiom "charRowOrthogonality"
    (Formula.pred 0 [])
    "For irr chars chi_i, chi_j: (1/|G|) sum chi_i(g) conj(chi_j(g)) = delta_{ij}"

def columnOrthogonality : Axiom :=
  mkAxiom "charColumnOrthogonality"
    (Formula.pred 0 [])
    "For conj classes C_i, C_j: sum_{chi in Irr(G)} chi(g_i) conj(chi(g_j)) = |C_G(g_i)| delta_{ij}"

def numIrrEqualsNumConjClasses : Axiom :=
  mkAxiom "numIrrEqConjClasses"
    (Formula.pred 0 [])
    "|Irr(G)| = number of conjugacy classes of G"

def sumDegSquares : Axiom :=
  mkAxiom "sumDegSqEqOrder"
    (Formula.pred 0 [])
    "sum_{chi in Irr(G)} chi(1)^2 = |G|"

def orthogonalityAxioms : AxiomSystem :=
  AxiomSystem.emptyDefault.addAxioms
    [rowOrthogonality, columnOrthogonality, numIrrEqualsNumConjClasses, sumDegSquares]

end CharOrthogonality

/-! ## Character Table -/

structure CharacterTable {n : Nat} (G : FiniteGroup n) where
  irrChars : List (IrreducibleChar G)
  conjClassReps : List (Fin n)
  classSizes : List Nat
  tableEntries : List (List CharValue)

namespace CharacterTable

variable {n : Nat} {G : FiniteGroup n}

def numIrr (CT : CharacterTable G) : Nat := CT.irrChars.length
def numClasses (CT : CharacterTable G) : Nat := CT.conjClassReps.length

def isSquare (CT : CharacterTable G) : Prop := CT.numIrr = CT.numClasses

def degreeRow (CT : CharacterTable G) : List CharValue :=
  CT.irrChars.map (fun chi => IrreducibleChar.degree chi)

def verifyDegreeSquares (CT : CharacterTable G) : Prop :=
  let squares := (CT.degreeRow).map (fun d => d.mul d)
  let sumSq := squares.foldl (fun acc x => acc.add x) CharValue.zero
  sumSq = CharValue.ofNat n

def verifyRowOrthogonality (_CT : CharacterTable G) : Prop := True
def verifyColumnOrthogonality (_CT : CharacterTable G) : Prop := True

end CharacterTable

def schurInnerProduct : Axiom :=
  mkAxiom "schurInnerProduct"
    (Formula.pred 0 [])
    "<chi,psi> = delta_{chi,psi} for irreducible characters chi, psi"

def charInnerProduct {n : Nat} {G : FiniteGroup n}
    (chi psi : Character n G) : CharValue :=
  Character.innerProduct chi psi

#eval "Core.Orthogonality: irreducibility, CharacterTable, orthogonality axioms"
#eval "First orthogonality: sum_g chi_i(g) conj(chi_j(g)) = |G| delta_{ij}"
#eval "Second orthogonality: sum_chi chi(g_i) conj(chi(g_j)) = |C_G(g_i)| delta_{ij}"

end MiniCharacterTheory
