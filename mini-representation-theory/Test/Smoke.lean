/-
# Smoke Tests - MiniRepresentationTheory

Run: `lake env lean --run Test/Smoke.lean`
-/

import MiniRepresentationTheory

open MiniRepresentationTheory

#eval "══ MINI-REPRESENTATION-THEORY SMOKE TESTS ══"

/-! ## Core.Basic: Weight operations -/
#eval Weight.zero 2
#eval Weight.add (Weight.fromList 2 [1, 0]) (Weight.fromList 2 [0, 1])
#eval Weight.dot (Weight.fromList 2 [1, 0]) (Weight.fromList 2 [0, 1])

/-! ## Core.Basic: CartanMatrix -/
#eval (CartanMatrix.typeA 3).rank
#eval (CartanMatrix.typeG2).rank

/-! ## Core.Basic: DynkinType -/
#eval DynkinType.A 2 |>.dim
#eval DynkinType.E8.dim

/-! ## Core.Objects: FormalChar -/
#eval FormalChar.fromWeight (Weight.fromList 1 [0])
#eval ((FormalChar.fromWeight (Weight.fromList 1 [1])).dimension)

/-! ## Examples: sl(2) -/
#eval Sl2Representation.fundamental.dim
#eval clebschGordan 1 1

/-! ## Examples: sl(3) -/
#eval Sl3Representation.quark.dim
#eval Sl3Representation.adjoint.dim

/-! ## Applications: Physics -/
#eval (QuantumSpin.spinHalf).dim

#eval "══ ALL SMOKE TESTS PASSED ══"