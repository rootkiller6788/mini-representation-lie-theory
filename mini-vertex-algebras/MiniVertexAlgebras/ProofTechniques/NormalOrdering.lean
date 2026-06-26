/-
# MiniVertexAlgebras.ProofTechniques.NormalOrdering

Normal ordering and Wick theorem: fundamental computational techniques.
L5: Proof techniques.
-/

import MiniVertexAlgebras.Core.Basic
import MiniVertexAlgebras.Core.FieldCalculus

namespace MiniVertexAlgebras

/-- Normal ordered product axiom --/
def normalOrderedProductAxiom : Axiom :=
  Axiom.mk "normalOrderedProduct" (Formula.pred 0 [])
    "Normal ordering :AB: places creation operators left of annihilation operators"

/-- Wick theorem axiom --/
def wickTheoremAxiom : Axiom :=
  Axiom.mk "wickTheorem" (Formula.pred 0 [])
    "Wick theorem: product = sum over pairings of contractions x normal ordered"

/-- OPE calculation axiom --/
def opeCalculationAxiom : Axiom :=
  Axiom.mk "opeCalculation" (Formula.pred 0 [])
    "OPE computed via normal ordering and commutation relations"

/-- Heisenberg OPE: b(z)b(w) ~ 1/(z-w)^2 --/
def heisenbergOPEAxiom : Axiom :=
  Axiom.mk "heisenbergOPE" (Formula.pred 0 [])
    "b(z)b(w) = :b(z)b(w): + 1/(z-w)^2"

/-- Virasoro OPE: L(z)L(w) ~ c/2/(z-w)^4 + 2L/(z-w)^2 + dL/(z-w) --/
def virasoroOPEAxiom : Axiom :=
  Axiom.mk "virasoroOPE" (Formula.pred 0 [])
    "L(z)L(w) = c/2/(z-w)^4 + 2L(w)/(z-w)^2 + dL(w)/(z-w) + :LL:"

/-- Contraction of free boson fields --/
def freeBosonContraction : Axiom :=
  Axiom.mk "freeBosonContraction" (Formula.pred 0 [])
    "Contraction [[b(z), b(w)]] = 1/(z-w)^2"

/-- Normal ordering of Virasoro field --/
def virasoroNormalOrdering : Axiom :=
  Axiom.mk "virasoroNormalOrdering" (Formula.pred 0 [])
    ":LL: = sum_k (:L_{k} L_{n-k}:) gives weight-4 field"

#eval "ProofTechniques.NormalOrdering: axioms registered"

end MiniVertexAlgebras
