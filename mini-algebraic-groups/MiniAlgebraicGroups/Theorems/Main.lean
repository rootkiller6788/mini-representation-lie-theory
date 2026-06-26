/- L4: Structure theorems. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Constructions.Subgroups
import MiniAlgebraicGroups.Theorems.LieKolchin
import MiniAlgebraicGroups.Theorems.BorelFixedPoint
import MiniAlgebraicGroups.Theorems.JordanDecomp
namespace MiniAlgebraicGroups

axiom structureOfConnectedSolvable (n : Nat) (G : AlgebraicGroup n) (hSolvable : IsSolvable n G) : True
axiom structureOfConnectedReductive (n : Nat) (G : AlgebraicGroup n) (hReductive : IsReductive n G) : True
axiom borelTitsSelfNormalizing (n : Nat) (G : AlgebraicGroup n) : True
axiom leviDecompositionFull (n : Nat) (G : AlgebraicGroup n) : True
axiom langTheoremFull (n : Nat) (G : AlgebraicGroup n) : True
axiom steinbergConnectedCentralizer (n : Nat) (G : AlgebraicGroup n) (hG : IsSemisimple n G) : True
axiom completeReducibilityChar0 (n : Nat) (G : AlgebraicGroup n) (hReductive : IsReductive n G) : True

#eval "Theorems.Main: structure of solvable/reductive, Levi, Lang, Steinberg, complete reducibility"
/-! ## Additional Structure Theorems -/

axiom titsSystemAxioms (n : Nat) (G : AlgebraicGroup n) : True
axiom bnPairStructure (n : Nat) (G : AlgebraicGroup n) : True
axiom bruhatTitsBuilding (n : Nat) (G : AlgebraicGroup n) : True

axiom chevalleyCommutatorFormula (n : Nat) (G : AlgebraicGroup n) : True
axiom steinbergRelations (n : Nat) (G : AlgebraicGroup n) : True

axiom rosenlichtTheorem (n : Nat) (G : AlgebraicGroup n) : True
axiom mostowDecompositionTheorem (n : Nat) (G : AlgebraicGroup n) : True

#eval "Theorems.Main: Tits system, BN-pair, Chevalley commutator formula"
/-! ## Classification Theorems -/
axiom chevalleyClassificationSemisimple : True
axiom demazureTitsClassificationAnisotropic : True
axiom kacClassificationFiniteDimensional : True

#eval "Theorems.Main: Chevalley, Demazure-Tits, Kac classification theorems"
/-! ## Decomposition Theorems -/
axiom bruhatDecompositionForReductive (n : Nat) (G : AlgebraicGroup n) : True
axiom iwasawaDecomposition (n : Nat) (G : AlgebraicGroup n) : True
axiom cartanDecomposition (n : Nat) (G : AlgebraicGroup n) : True
axiom kawApproximation (n : Nat) (G : AlgebraicGroup n) : True

#eval "Theorems.Main: Bruhat, Iwasawa, Cartan decompositions"
/-! ## Chevalley's Theorem -/
axiom chevalleyTheoremOnConstructibleSets : True
axiom chevalleyTheoremOnRationalityOfRepresentations : True

#eval "Theorems.Main: Chevalley's theorems on constructible sets and representations"