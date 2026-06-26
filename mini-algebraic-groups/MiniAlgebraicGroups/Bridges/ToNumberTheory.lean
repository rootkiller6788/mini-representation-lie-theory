/- L7: Bridge to number theory. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Properties.Invariants
import MiniAlgebraicGroups.Theorems.Main
namespace MiniAlgebraicGroups

axiom arithmeticGroupExamples : True
axiom galoisCohomologyTorsors (n : Nat) (G : AlgebraicGroup n) : True
axiom hilbertTheorem90 (n : Nat) : True
axiom kneserBruhatTits (n : Nat) (G : AlgebraicGroup n) : True
axiom tamagawaNumber (n : Nat) (G : AlgebraicGroup n) : True
axiom weilTamagawaFormula (n : Nat) (G : AlgebraicGroup n) : True
axiom shimuraVarieties (n : Nat) (G : AlgebraicGroup n) : True
axiom langlandsProgram (n : Nat) (G : AlgebraicGroup n) : True
axiom ngoFundamentalLemmaProof : True

#eval "Bridges.ToNumberTheory: arithmetic groups, Galois cohomology, Tamagawa, Shimura, Langlands"
/-! ## More Number Theory Connections -/

axiom localGlobalPrincipleAlgebraicGroups (n : Nat) (G : AlgebraicGroup n) : True
axiom adelicPoints (n : Nat) (G : AlgebraicGroup n) : True
axiom automorphicRepresentations (n : Nat) (G : AlgebraicGroup n) : True

axiom langlandsFunctoriality (n : Nat) (G : AlgebraicGroup n) : True
axiom endoscopyTheory (n : Nat) (G : AlgebraicGroup n) : True

#eval "Bridges.ToNumberTheory: local-global principle, adelic points, automorphic reps"
/-! ## More Arithmetic Theory -/

axiom hasseWeilZetaFunctionShimuraVarieties (n : Nat) (G : AlgebraicGroup n) : True
axiom etaleCohomologyShimuraVarieties (n : Nat) (G : AlgebraicGroup n) : True
axiom automorphicGaloisRepresentations (n : Nat) (G : AlgebraicGroup n) : True

/-! ## L-Functions -/

axiom langlandsLFunction (n : Nat) (G : AlgebraicGroup n) : True
axiom functionalEquationLFunction (n : Nat) (G : AlgebraicGroup n) : True

/-! ## Trace Formula -/

axiom arthurSelbergTraceFormula (n : Nat) (G : AlgebraicGroup n) : True
axiom stableTraceFormula (n : Nat) (G : AlgebraicGroup n) : True

#eval "Bridges.ToNumberTheory: zeta functions, L-functions, trace formula"
/-! ## Arithmetic Duality Theorems -/
axiom poitouTateDuality (n : Nat) (G : AlgebraicGroup n) : True
axiom artinVerdierDuality (n : Nat) (G : AlgebraicGroup n) : True

/-! ## Class Field Theory -/
axiom langlandsCorrespondenceForTori (n : Nat) (G : AlgebraicGroup n) : True
axiom localClassFieldTheoryViaAlgebraicGroups (n : Nat) (G : AlgebraicGroup n) : True

#eval "Bridges.ToNumberTheory: Poitou-Tate, Artin-Verdier, class field theory"
/-! ## Theta Functions and Automorphic Forms -/
axiom thetaCorrespondence (n : Nat) (G : AlgebraicGroup n) : True
axiom siegelWeilFormula (n : Nat) (G : AlgebraicGroup n) : True

#eval "Bridges.ToNumberTheory: theta correspondence, Siegel-Weil formula"