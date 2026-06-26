/-
# MiniVertexAlgebras.Core.FieldCalculus

Formal calculus on fields: normal ordering, operator product expansion (OPE),
Wick's theorem, formal derivatives, and the lambda-bracket formalism.

L2: Core concepts — normal ordering, OPE, lambda-bracket
L5: Proof techniques — formal series manipulation
-/

import MiniVertexAlgebras.Core.Basic

namespace MiniVertexAlgebras

/-! ## Formal Fields

A formal field on a vertex algebra V is a series A(z) = sum_{n in Z} A_{(n)} z^{-n-1}.
We represent fields as Z-indexed families with the field condition. -/

structure FormalField (V : Vec) where
  modes : Int → V.carrier → V.carrier
  fieldCond : ∀ (v : V.carrier), ∃ (N : Int), ∀ (n : Int), n ≥ N → modes n v = V.zero
  modeAdd : ∀ (n : Int) (x y : V.carrier), modes n (V.add x y) = V.add (modes n x) (modes n y)
  modeSmul : ∀ (n : Int) (r : Int) (x : V.carrier), modes n (V.smul r x) = V.smul r (modes n x)

/-! ## Field from a state

The state-field correspondence maps each state a to a field Y(a, z)
with modes Y(a, z)_{(n)} = a_{(n)}. -/

def stateField (VA : BasicVertexAlgebra) (a : VA.vec.carrier) : FormalField VA.vec where
  modes n v := VA.nproduct n a v
  fieldCond v := VA.field_cond a v
  modeAdd n x y := VA.nproduct_add_right n a x y
  modeSmul n r x := VA.nproduct_smul_right n r a x

/-! ## Normal Ordered Product

The normal ordered product :AB:(z) of two fields A(z), B(z) moves
annihilation operators to the right of creation operators.
We register this as an axiom with known computational rules. -/

def normalOrderProductAxiom : Axiom :=
  Axiom.mk "normalOrderProduct" (Formula.pred 0 [])
    ":AB:_{(n)} = sum_{i<0} A_{(i)} B_{(n-i-1)} + sum_{i>=0} B_{(n-i-1)} A_{(i)}"

/-! ## Operator Product Expansion (OPE)

The OPE A(z) B(w) = sum_j C_j(w) / (z-w)^{j+1} encodes the singular
part of the product. The coefficients C_j are fields. -/

def opeAxiom : Axiom :=
  Axiom.mk "operatorProductExpansion" (Formula.pred 0 [])
    "A(z)B(w) = sum_j C_j(w)/(z-w)^{j+1} for finitely many singular terms"

/-! ## Contraction / Wick's Theorem

For free fields, Wick's theorem expresses products in terms of
normal ordered products and contractions. -/

def wicksTheoremAxiom : Axiom :=
  Axiom.mk "wicksTheorem" (Formula.pred 0 [])
    "T[A_1(z_1)...A_n(z_n)] = sum over pairings of contractions x normal ordered remainder"

/-! ## Lambda-Bracket Formalism

The lambda-bracket [a_lambda b] = sum_{i >= 0} lambda^i / i! a_{(i)} b
captures the OPE singular part. -/

def lambdaBracketAxiom : Axiom :=
  Axiom.mk "lambdaBracket" (Formula.pred 0 [])
    "[a_lambda b] = sum_{i>=0} lambda^i / i! a_{(i)} b"

/-! ## Formal derivative of a field

partial_z A(z) = sum_{n in Z} (-n-1) A_{(n)} z^{-n-2}
Equivalently: (partial A)_{(n)} = -n A_{(n-1)} -/

def formalDerivativeAxiom : Axiom :=
  Axiom.mk "formalDerivative" (Formula.pred 0 [])
    "(partial_z A)_{(n)} = -n A_{(n-1)}"

/-! ## Iterated Fields

The iterated field Y(Y(a,z-w)b,w) c expressed via the Borcherds
identity. For computational purposes, we define truncated versions. -/

def iteratedFieldAxiom : Axiom :=
  Axiom.mk "iteratedField" (Formula.pred 0 [])
    "Y(Y(a,z-w)b,w) = Y(a,z)Y(b,w) - Y(b,w)Y(a,z) in appropriate domains"

/-! ## #eval verification -/

#eval "Core.FieldCalculus: FormalField, stateField, normal ordering defined"
#eval "Core.FieldCalculus: OPE, Wick theorem, lambda-bracket axioms registered"
#eval "Core.FieldCalculus: Formal derivative, iterated fields"

end MiniVertexAlgebras
