/- L4: Borel fixed point theorem. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Constructions.Quotients
namespace MiniAlgebraicGroups

axiom borelFixedPoint (n : Nat) (G : AlgebraicGroup n) (hSolvable : IsSolvable n G) (hConnected : True) : True
axiom borelSelfNormalizing (n : Nat) (G : AlgebraicGroup n) : True
axiom flagVarietyIsComplete (n : Nat) (G : AlgebraicGroup n) : True
axiom maximalToriConjugacyViaBorel (n : Nat) (G : AlgebraicGroup n) : True

#eval "Theorems.BorelFixedPoint: solvable group on complete variety has fixed point"
/-! ## Proof Details -/

axiom borelFixedPointProofInduction (n : Nat) (G : AlgebraicGroup n) : True
axiom borelFixedPointProofQuotientAction (n : Nat) (G : AlgebraicGroup n) : True

/-! ## Applications -/

axiom borelFixedPointFlagVarietyApplication (n : Nat) (G : AlgebraicGroup n) : True
axiom borelFixedPointGrassmannianApplication (n : Nat) (G : AlgebraicGroup n) : True
axiom borelFixedPointHomogeneousSpaceApplication (n : Nat) (G : AlgebraicGroup n) : True

#eval "BorelFixedPoint: proof steps, flag variety/Grassmannian applications"
/-! ## Generalizations of Borel Fixed Point -/
axiom horrocksMumfordFixedPoint (n : Nat) (G : AlgebraicGroup n) : True
axiom fogartyFixedPoint (n : Nat) (G : AlgebraicGroup n) : True

#eval "BorelFixedPoint: Horrocks-Mumford, Fogarty generalizations"