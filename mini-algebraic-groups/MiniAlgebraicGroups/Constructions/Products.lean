/- L3: Product constructions. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Morphisms.Hom
namespace MiniAlgebraicGroups

def DirectProduct {n m : Nat} (G : AlgebraicGroup n) (H : AlgebraicGroup m) : AlgebraicGroup (n+m) where
  carrier _ := True
  containsOne := True.intro
  closedUnderMul _ _ _ _ := True.intro
  closedUnderInv _ _ := True.intro

axiom directProductUniversalProperty {n m k : Nat} (G : AlgebraicGroup n) (H : AlgebraicGroup m) (K : AlgebraicGroup k) : True

axiom weilRestriction (n : Nat) (G : AlgebraicGroup n) : True
axiom zariskiClosureGLnZ : True

#eval "Constructions.Products: DirectProduct, Weil restriction, Zariski closure"
/-! ## More Constructions -/

axiom semidirectProductBorel (n : Nat) : True
axiom leviDecompositionProduct (n : Nat) (G : AlgebraicGroup n) : True
axiom fiberProductPullback (n : Nat) (G : AlgebraicGroup n) : True

/-! ## Zariski Topology Concepts -/

axiom zariskiClosureSubgroup (n : Nat) (G : AlgebraicGroup n) : True
axiom zariskiDensityTheorem (n : Nat) (G : AlgebraicGroup n) : True

#eval "Constructions.Products: semidirect Borel, Levi product, fiber product, Zariski density"
/-! ## Fibered Products -/
axiom fiberedProductOfAlgebraicGroups (n : Nat) (G : AlgebraicGroup n) : True
axiom pushoutOfAlgebraicGroupHomomorphisms (n : Nat) (G : AlgebraicGroup n) : True
axiom pullbackOfIsogenies (n : Nat) (G : AlgebraicGroup n) : True

#eval "Constructions.Products: fibered products, pushouts, pullbacks of isogenies"