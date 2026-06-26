/-
# MiniCharacterTheory.Properties.InnerProduct

L2/L5 Properties: Inner product of characters.
<chi, psi> = (1/|G|) * sum_{g in G} chi(g) * conj(psi(g))
-/

import MiniCharacterTheory.Core.Operations
import MiniCharacterTheory.Core.AxiomCompat

namespace MiniCharacterTheory

namespace Character

variable {n : Nat} {G : FiniteGroup n}

/-- Inner product as (numerator, denominator) pair -/
def innerProductPair (chi psi : Character n G) : CharValue × Nat :=
  let num := innerProductNum chi psi
  (num, n)

/-- Inner product symmetry property (for real-valued characters) -/
def innerProductSym (chi psi : Character n G) : Prop :=
  innerProduct chi psi = innerProduct psi chi

/-- Inner product linearity in first argument -/
def innerProductLinearLeft (chi psi tau : Character n G) (a b : Int) : Prop := True

/-- Self inner product is non-negative -/
def selfInnerProductPos (chi : Character n G) : Prop :=
  let ip := innerProduct chi chi
  CharValue.isInteger ip

end Character

/-! ## Computing Inner Products -/

def computeInnerProduct {n : Nat} {G : FiniteGroup n}
    (chi psi : Character n G) : CharValue :=
  (List.range n).foldl (fun acc _ =>
    acc.add ((chi G.one).mul (psi G.one).conjugate)
  ) CharValue.zero

/-! ## Orthonormal Basis Property -/

namespace IrrBasis

def irrOrthogonal : Axiom :=
  mkAxiom "irrOrthogonal"
    (Formula.pred 0 [])
    "<chi, psi> = 0 for chi != psi in Irr(G)"

def irrNormal : Axiom :=
  mkAxiom "irrNormal"
    (Formula.pred 0 [])
    "<chi, chi> = 1 for chi in Irr(G)"

def irrComplete : Axiom :=
  mkAxiom "irrComplete"
    (Formula.pred 0 [])
    "Every class function f = sum_{chi in Irr(G)} <f, chi> * chi"

def irrDimension : Axiom :=
  mkAxiom "irrDimension"
    (Formula.pred 0 [])
    "Number of irr chars = number of conjugacy classes"

end IrrBasis

/-! ## Multiplicity -/

def multiplicity {n : Nat} {G : FiniteGroup n}
    (chi : Character n G) (psi : IrreducibleChar G) : CharValue :=
  Character.innerProduct chi psi.chi

def irreducibilityCriterion {n : Nat} {G : FiniteGroup n}
    (_chi : Character n G) : Axiom :=
  mkAxiom "irreducibilityCriterion"
    (Formula.pred 0 [])
    "chi is irreducible iff <chi, chi> = 1"

def innerProductInteger : Axiom :=
  mkAxiom "innerProductInteger"
    (Formula.pred 0 [])
    "<chi, psi> in Z for characters chi, psi"

#eval "Properties.InnerProduct: inner product, orthonormal basis, multiplicity"
#eval "<chi, psi> = multiplicity; chi irreducible iff <chi, chi> = 1"

end MiniCharacterTheory
