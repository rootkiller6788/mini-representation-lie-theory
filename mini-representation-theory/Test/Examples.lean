/-
# Examples - MiniRepresentationTheory

Runnable `#eval` examples verifying key properties.
-/

import MiniRepresentationTheory

open MiniRepresentationTheory

/-! ## sl(2) Clebsch-Gordan -/
#eval verifyClebschGordanDim 1 1
#eval verifyClebschGordanDim 1 2
#eval verifyClebschGordanDim 2 2

/-! ## sl(2) Dimensions -/
#eval List.range 10 |>.map (fun n => Sl2Representation.ofSpin n |>.dim)

/-! ## sl(3) Dimensions -/
#eval Sl3Representation.quark.dim
#eval Sl3Representation.adjoint.dim
#eval Sl3Representation.decuplet.dim
#eval Sl3Representation.V21.dim

/-! ## sl(3) Dimension Formula Verification -/
#eval checkSl3Dimensions
#eval checkSl3Tensor3x3
#eval checkSl3Tensor3x3bar
#eval checkSl3Tensor3x3x3
#eval sl3AllChecks

/-! ## Angular Momentum Coupling -/
#eval angularMomentumCoupling 1 1
#eval angularMomentumCoupling 1 2
#eval verifyAngularMomentumDim 1 1
#eval verifyAngularMomentumDim 2 3

/-! ## Weyl Dimension Formula (sl_2 case) -/
#eval sl2WeylDimension 0
#eval sl2WeylDimension 1
#eval sl2WeylDimension 2

/-! ## Dynkin Type Info -/
#eval (DynkinType.A 2).dim
#eval (DynkinType.A 2).numPosRoots
#eval (DynkinType.A 2).weylGroupOrder
#eval (DynkinType.A 2).dualCoxeterNumber

/-! ## Cartan Matrix Properties -/
#eval (CartanMatrix.typeA 3).isSymmetric
#eval (CartanMatrix.typeG2).isSymmetric

/-! ## Character Ring Operations -/
def exChar := FormalChar.fromWeight (Weight.fromList 1 [2])
#eval exChar.dimension

/-! ## Representation Operations -/
def exV := Representation.trivial 2
#eval exV.dim
#eval exV.isIrreducible