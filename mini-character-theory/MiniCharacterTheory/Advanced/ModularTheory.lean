/-
# MiniCharacterTheory.Advanced.ModularTheory

L8 Advanced Topics: Modular representation theory and Brauer characters.
Character theory in positive characteristic.
-/

import MiniCharacterTheory.Core.Orthogonality
import MiniCharacterTheory.Core.AxiomCompat

namespace MiniCharacterTheory

def isPRegular {n : Nat} {G : FiniteGroup n} (g : Fin n) (p : Nat) : Prop := True

def BrauerChar {n : Nat} (G : FiniteGroup n) (p : Nat) :=
  Fin n -> CharValue

def decompositionMatrix : Axiom :=
  mkAxiom "decompositionMatrix"
    (Formula.pred 0 [])
    "D_{ij} relates ordinary irr chars to modular irr chars on p-regular classes"

def cartanMatrix : Axiom :=
  mkAxiom "cartanMatrix"
    (Formula.pred 0 [])
    "Cartan matrix C = D^T D encodes modular character multiplicities"

def cartanElementaryDivisors : Axiom :=
  mkAxiom "cartanElemDiv"
    (Formula.pred 0 [])
    "Elementary divisors of Cartan matrix are powers of p"

def pBlock {n : Nat} (G : FiniteGroup n) (p : Nat) : Type :=
  List (IrreducibleChar G)

def defectGroup : Axiom :=
  mkAxiom "defectGroup"
    (Formula.pred 0 [])
    "Each p-block has a defect group (p-subgroup up to conjugacy)"

def numBlocks : Axiom :=
  mkAxiom "numBlocks"
    (Formula.pred 0 [])
    "#p-blocks = #p-regular conjugacy classes of G"

def defectZeroBlock : Axiom :=
  mkAxiom "defectZero"
    (Formula.pred 0 [])
    "A block has defect 0 iff it contains a char with chi(1)_p = |G|_p"

def brauerFirstMainTheorem : Axiom :=
  mkAxiom "brauerFirstMain"
    (Formula.pred 0 [])
    "Blocks with defect D of G correspond to blocks with defect D of N_G(D)"

def brauerSecondMainTheorem : Axiom :=
  mkAxiom "brauerSecondMain"
    (Formula.pred 0 [])
    "Values of chi in block B relate to centralizer blocks"

def brauerThirdMainTheorem : Axiom :=
  mkAxiom "brauerThirdMain"
    (Formula.pred 0 [])
    "Brauer correspondence preserves principal blocks"

def mckayConjecture : Axiom :=
  mkAxiom "mckayConjecture"
    (Formula.pred 0 [])
    "|Irr_{p'}(G)| = |Irr_{p'}(N_G(P))| for Sylow p-subgroup P"

def alperinWeightConjecture : Axiom :=
  mkAxiom "alperinWeightConjecture"
    (Formula.pred 0 [])
    "Number of p-blocks of G = number of G-conjugacy classes of weights"

def alperinMcKayConjecture : Axiom :=
  mkAxiom "alperinMcKay"
    (Formula.pred 0 [])
    "For block B with defect D, |Irr_0(B)| = |Irr_0(b)| for Brauer correspondent b"

def broueAbelianDefectConjecture : Axiom :=
  mkAxiom "broueConjecture"
    (Formula.pred 0 [])
    "D^b(B) derived equivalent to D^b(b) when defect group is abelian"

#eval "Advanced.ModularTheory: Brauer chars, decomposition matrix, p-blocks"
#eval "Brauer I-II-III, McKay, Alperin, Alperin-McKay, Broue conjectures"
#eval "Cartan matrix elementary divisors are powers of p"

end MiniCharacterTheory
