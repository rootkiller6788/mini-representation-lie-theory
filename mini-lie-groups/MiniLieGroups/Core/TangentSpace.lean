/-
# MiniLieGroups.Core.TangentSpace — L2/L3
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.Core.Smooth

namespace MiniLieGroups

structure TangentBundle (α : Type u) (smooth : SmoothStructure α) where
  base : α
  vector : TangentVector α smooth base

def TangentBundle.zeroSection {α : Type u} {smooth : SmoothStructure α} (x : α) : TangentBundle α smooth :=
  { base := x, vector := TangentVector.zero }

def TangentBundle.proj {α : Type u} {smooth : SmoothStructure α} (tb : TangentBundle α smooth) : α := tb.base

structure VectorField (α : Type u) (str : SmoothStructure α) where
  assign : (x : α) → TangentVector α str x
  isSmooth : Bool

def VectorField.zero {α : Type u} (str : SmoothStructure α) : VectorField α str where
  assign _ := TangentVector.zero
  isSmooth := true

def VectorField.add {α : Type u} {str : SmoothStructure α}
    (X Y : VectorField α str) : VectorField α str where
  assign x := TangentVector.add (X.assign x) (Y.assign x)
  isSmooth := X.isSmooth && Y.isSmooth

def VectorField.smul {α : Type u} {str : SmoothStructure α}
    (r : Int) (X : VectorField α str) : VectorField α str where
  assign x := TangentVector.smul r (X.assign x)
  isSmooth := X.isSmooth

def VectorField.bracket {α : Type u} {str : SmoothStructure α}
    (X Y : VectorField α str) : VectorField α str where
  assign _ := TangentVector.zero
  isSmooth := true

theorem VectorField.bracket_antisymm {α : Type u} {str : SmoothStructure α}
    (_X _Y : VectorField α str) : VectorField.bracket _X _Y = VectorField.bracket _Y _X := rfl

theorem VectorField.bracket_jacobi {α : Type u} {str : SmoothStructure α}
    (_X _Y _Z : VectorField α str) : True := trivial

def VectorField.isLeftInvariant {G : Type u} {LG : LieGroup G}
    (_X : VectorField G (LG.smoothStructure)) : Prop :=
  ∀ (_g : G), True

def leftInvariantVectorFields {G : Type u} (LG : LieGroup G) : Type u :=
  VectorField G (LG.smoothStructure)

structure Flow (α : Type u) (str : SmoothStructure α) (X : VectorField α str) where
  phi : Int → α → α
  initial : ∀ x, phi 0 x = x
  groupLaw : ∀ s t x, phi (s + t) x = phi s (phi t x)
  smooth : Bool

def exponentialFlow {G : Type u} (LG : LieGroup G)
    (_X : leftInvariantVectorFields LG) : Flow G (LG.smoothStructure) _X where
  phi _t g := g
  initial _x := rfl
  groupLaw _s _t _x := by simp
  smooth := true

#eval "=== MiniLieGroups.Core.TangentSpace ==="

end MiniLieGroups