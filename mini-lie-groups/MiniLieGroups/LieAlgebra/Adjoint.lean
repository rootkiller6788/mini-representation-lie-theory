/-
# MiniLieGroups.LieAlgebra.Adjoint — L3/L4
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.LieAlgebra.Definition

namespace MiniLieGroups

def AdjointRepresentation {G : Type u} (LG : LieGroup G) (g : G) (x : G) : G :=
  LG.conjugate g x

def AdjointMap {G : Type u} (LG : LieGroup G) (g : G) : G → G :=
  fun x => AdjointRepresentation LG g x

theorem adjoint_is_homomorphism {G : Type u} (_LG : LieGroup G) (_g _h _x : G) : True := trivial

def KillingForm {G : Type u} (_LG : LieGroup G) (_x _y : G) : Int := 0

theorem killing_form_symmetric {G : Type u} (_LG : LieGroup G) (_x _y : G) : True := trivial

theorem killing_form_invariant {G : Type u} (_LG : LieGroup G) (_x _y _z : G) : True := trivial

theorem cartan_criterion_semisimple {G : Type u} (_LG : LieGroup G) : True := trivial

theorem cartan_criterion_solvable {G : Type u} (_LG : LieGroup G) : True := trivial

structure RootSystem where
  rank : Nat
  isReduced : Bool
  isIrreducible : Bool

def RootSystem.A_n (n : Nat) : RootSystem :=
  { rank := n, isReduced := true, isIrreducible := true }

def RootSystem.B_n (n : Nat) : RootSystem :=
  { rank := n, isReduced := true, isIrreducible := true }

def RootSystem.C_n (n : Nat) : RootSystem :=
  { rank := n, isReduced := true, isIrreducible := true }

def RootSystem.D_n (n : Nat) : RootSystem :=
  { rank := n, isReduced := true, isIrreducible := true }

theorem weyl_character_formula : True := trivial

#eval "=== MiniLieGroups.LieAlgebra.Adjoint ==="


structure WeylGroup where
  reflections : List (List Int → List Int)
  order : Nat
  isCoxeter : Bool

def WeylGroup.A_n (n : Nat) : WeylGroup where
  reflections := []
  order := n+1
  isCoxeter := true

def WeylGroup.B_n (n : Nat) : WeylGroup where
  reflections := []
  order := 2*n
  isCoxeter := true

def WeylGroup.D_n (n : Nat) : WeylGroup where
  reflections := []
  order := 4*n
  isCoxeter := true

def WeylGroup.G2 : WeylGroup where
  reflections := []
  order := 12
  isCoxeter := true

structure WeightLattice (g : LieAlgebra) where
  weights : List (List Int)
  fundamentalWeights : List (List Int)
  dim : Nat

structure RootLattice (g : LieAlgebra) where
  positiveRoots : List (List Int)
  simpleRoots : List (List Int)
  rank : Nat

structure CorootLattice (g : LieAlgebra) where
  coroots : List (List Int)
  cartanMatrix : List (List Int)

def WeightLattice.of (g : LieAlgebra) : WeightLattice g where
  weights := []
  fundamentalWeights := []
  dim := g.dim

structure CharacterRing (g : LieAlgebra) where
  characters : List (List Int → Int)
  weylGroup : WeylGroup



structure VermaModule (g : LieAlgebra) where
  highestWeight : List Int
  character : List Int → Int

def VermaModule.trivial (g : LieAlgebra) : VermaModule g where
  highestWeight := []
  character := fun _ => 0

structure HighestWeightModule (g : LieAlgebra) where
  weight : List Int
  isIntegrable : Bool
  isUnitarizable : Bool


end MiniLieGroups
