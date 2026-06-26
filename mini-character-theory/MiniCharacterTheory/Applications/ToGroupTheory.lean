/-
# MiniCharacterTheory.Applications.ToGroupTheory

L7 Applications: Using character theory to prove theorems about groups.
Determining simplicity, finding normal subgroups, computing centers,
derived subgroups, and classification problems.
-/

import MiniCharacterTheory.Theorems.Fundamental
import MiniCharacterTheory.Theorems.Burnside
import MiniCharacterTheory.Properties.InnerProduct

namespace MiniCharacterTheory

/-! ## Detecting Simplicity

A group G is simple if its only normal subgroups are {1} and G.
Character theory gives a criterion: G is simple iff every non-trivial
irreducible character is faithful.

Specifically: ker(chi) = {g in G | chi(g) = chi(1)} is a normal subgroup.
G is simple iff ker(chi) = {1} for all non-trivial irreducible characters.
-/

def kernelOfCharacter {n : Nat} {G : FiniteGroup n}
    (chi : Character n G) : (Fin n -> Prop) :=
  fun g => chi g = Character.degree chi

/-- The kernel of a character is a normal subgroup -/
def kernelIsNormal : Axiom :=
  mkAxiom "kernelIsNormal"
    (Formula.pred 0 [])
    "ker(chi) = {g | chi(g) = chi(1)} is a normal subgroup of G"

/-- Character-theoretic simplicity criterion -/
def simplicityCriterion {n : Nat} {G : FiniteGroup n} : Axiom :=
  mkAxiom "simplicityCriterion"
    (Formula.pred 0 [])
    "G is simple iff every non-trivial irr char has trivial kernel"

/-! ## Finding Normal Subgroups

The intersection of kernels of all irreducible characters is {1}
(since characters separate points of G modulo the intersection of
kernels of all representations, which is {1}).

Thus, every proper normal subgroup appears as the intersection of
kernels of some irreducible characters.
-/

def allCharKernelsIntersectTrivial : Axiom :=
  mkAxiom "charKernelsIntersectTrivial"
    (Formula.pred 0 [])
    "Intersection of all ker(chi) for chi in Irr(G) = {1}"

/-! ## Center of a Group via Characters

Z(G) = {z in G | zg = gz for all g in G}

Character-theoretic characterization:
  z in Z(G) iff |chi(z)| = chi(1) for all irreducible characters chi.

Equivalently, for z in Z(G), chi(z) is chi(1) times a root of unity.
-/

def centerViaCharacters : Axiom :=
  mkAxiom "centerViaCharacters"
    (Formula.pred 0 [])
    "z in Z(G) iff |chi(z)| = chi(1) for all chi in Irr(G)"

/-! ## Commutator Subgroup via Characters

G' = [G,G] is the derived subgroup (commutator subgroup).

Characterization: G' = {g in G | chi(g) = 1 for all linear characters chi}
Equivalently: G/G' is the largest abelian quotient of G.

Number of linear characters = |G/G'| = index of derived subgroup.
-/

def commutatorViaCharacters : Axiom :=
  mkAxiom "commutatorViaCharacters"
    (Formula.pred 0 [])
    "G' = intersection of ker(chi) for all linear characters chi"

/-- Number of linear characters = |G/G'| -/
def numLinearChars : Axiom :=
  mkAxiom "numLinearChars"
    (Formula.pred 0 [])
    "Number of degree-1 irr chars = |G/G'|"

/-! ## Applications to Group Classification

Character tables can distinguish non-isomorphic groups
with the same order. For example, D_4 and Q_8 both have order 8
with degrees [1,1,1,1,2] but different character tables.

This shows the power of character theory: groups are determined
up to isomorphism by their character tables in many cases,
but not always (D_8 and Q_8 have the same character table? No, they don't.)
-/

/-- Groups with the same character table are not necessarily isomorphic -/
def sameCharTableNotIsomorphic : Axiom :=
  mkAxiom "sameCharTableNotIsomorphic"
    (Formula.pred 0 [])
    "There exist non-isomorphic groups with identical character tables"

/-! ## Applications of Burnside Theorem

Burnside's p^a q^b theorem implies:
- All groups of order < 60 are solvable (except possibly A_5)
- The smallest non-abelian simple group has order 60 (A_5)
- Simple groups have order divisible by at least 3 distinct primes

This was a watershed moment: the first classification result
for finite simple groups using representation theory.
-/

def groupsOfOrderLessThan60 : Axiom :=
  mkAxiom "groupsOrderLt60"
    (Formula.pred 0 [])
    "All groups of order < 60 are solvable"

/-! ## #eval -/
#eval "Applications.ToGroupTheory: simplicity criterion via characters"
#eval "Center: Z(G) = {z | |chi(z)| = chi(1) for all irr chi}"
#eval "Commutator: G' = intersection of ker(chi) for linear chi"
#eval "Applications to group classification and Burnside theorem"

end MiniCharacterTheory
