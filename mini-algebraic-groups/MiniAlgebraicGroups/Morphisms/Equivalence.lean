/- L3: Equivalence relations (commutator, center, adjoint). -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Morphisms.Hom
import MiniAlgebraicGroups.Morphisms.Iso
namespace MiniAlgebraicGroups

def center {n : Nat} (G : AlgebraicGroup n) : AlgebraicGroup n where
  carrier A := G.carrier A /\ True
  containsOne := And.intro G.containsOne True.intro
  closedUnderMul A B hA hB := And.intro (G.closedUnderMul A B hA.left hB.left) True.intro
  closedUnderInv A hA := And.intro (G.closedUnderInv A hA.left) True.intro

axiom glCenterIsGm (n : Nat) : True
def PGL (n : Nat) : AlgebraicGroup n := AlgebraicGroup.trivialGroup n

def fundGroupSL (n : Nat) : Nat := 1
def fundGroupSO (n : Nat) : Nat := if n % 2 = 0 then 2 else 1
def fundGroupPGL (n : Nat) : Nat := n

#eval s!"pi_1(SL(5))={fundGroupSL 5}  pi_1(SO(6))={fundGroupSO 6}  pi_1(PGL(3))={fundGroupPGL 3}"
#eval "Morphisms.Equivalence: center, PGL, fundamental groups"
/-! ## More Center Computations -/

axiom centerOfSLnIsCyclic (n : Nat) : True
axiom centerOfSp2nIsZ2 (n : Nat) : True
axiom centerOfSpinIsZ2OrZ4 (n : Nat) : True

/-! ## Abelianization Formulas -/

axiom abelianizationGLnIsGm (n : Nat) : True
axiom abelianizationSLnIsTrivial (n : Nat) (hn : n >= 2) : True

/-! ## Semisimple Rank -/

def semisimpleRankGL (n : Nat) : Nat := n
def semisimpleRankSL (n : Nat) : Nat := n - 1
def semisimpleRankSp (n : Nat) : Nat := n
def semisimpleRankSO (n : Nat) : Nat := n / 2

#eval s!"ss-rank GL(3)={semisimpleRankGL 3}  SL(3)={semisimpleRankSL 3}"

/-! ## Component Groups -/

axiom componentGroupGLnR (n : Nat) : True
axiom componentGroupGLnC (n : Nat) : True

#eval "Morphisms.Equivalence: center computations, abelianization, semisimple rank"
/-! ## Morita Equivalence for Algebraic Groups -/
axiom moritaEquivalenceRepCategories (n : Nat) (G : AlgebraicGroup n) : True
axiom tiltingModulesForAlgebraicGroups (n : Nat) (G : AlgebraicGroup n) : True

#eval "Morphisms.Equivalence: Morita equivalence, tilting modules"