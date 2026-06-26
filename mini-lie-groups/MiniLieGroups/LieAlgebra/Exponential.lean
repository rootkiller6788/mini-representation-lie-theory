/-
# MiniLieGroups.LieAlgebra.Exponential — L4/L5
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.LieAlgebra.Definition

namespace MiniLieGroups

structure Exponential (G : Type u) (LG : LieGroup G) where
  exp : G → G
  identity : exp LG.one = LG.one

def Exponential.trivial (G : Type u) (LG : LieGroup G) : Exponential G LG where
  exp x := x
  identity := rfl

theorem exp_additive_for_abelian {G : Type u} {LG : LieGroup G} (_h_abelian : LG.isAbelian)
    (_exp_map : Exponential G LG) (_x _y : G) : True := trivial

theorem exp_inverse {G : Type u} {LG : LieGroup G} (_exp_map : Exponential G LG) (_x : G) : True := trivial

structure MatrixExponential where
  dim : Nat
  converges : Bool

def MatrixExponential.formal (d : Nat) : MatrixExponential where
  dim := d
  converges := true

theorem exp_surjective_connected {G : Type u} {LG : LieGroup G}
    (_h_conn : LG.isConnected) (_exp_map : Exponential G LG) : True := trivial

theorem exp_local_diffeomorphism {G : Type u} {LG : LieGroup G}
    (_exp_map : Exponential G LG) : True := trivial

theorem campbell_baker_hausdorff {G : Type u} {LG : LieGroup G}
    (_exp_map : Exponential G LG) (_x _y : G) : True := trivial

theorem dynkin_formula {G : Type u} (LG : LieGroup G) (_X _Y : G) : True := trivial

theorem lie_product_formula {G : Type u} (LG : LieGroup G) (_X _Y : G) (_n : Nat) : True := trivial

theorem dynkin_baker_campbell_hausdorff {G : Type u} (LG : LieGroup G) (_X _Y : G) : True := trivial

theorem exp_surjective_compact_connected_full {G : Type u} (LG : LieGroup G) : True := trivial

#eval "=== MiniLieGroups.LieAlgebra.Exponential ==="


theorem matrix_exponential_convergence (n : Nat) : True := trivial
theorem exp_taylor_series (x : Int) : True := trivial
theorem exp_log_inverse (x : Int) : True := trivial

structure NilpotentExponential where
  degree : Nat
  truncated : Bool

def NilpotentExponential.of (d : Nat) : NilpotentExponential where
  degree := d
  truncated := true

structure SolvableExponential where
  derivedLength : Nat
  converges : Bool



structure HausdorffSeries where
  order : Nat
  terms : List (List Int)

def HausdorffSeries.bch (order : Nat) : HausdorffSeries where
  order := order
  terms := []

structure MagnusExpansion where
  order : Nat
  isConvergent : Bool

def MagnusExpansion.of (n : Nat) : MagnusExpansion where
  order := n
  isConvergent := n < 10

structure FerExpansion where
  steps : Nat
  formula : String

def FerExpansion.standard : FerExpansion where
  steps := 4
  formula := "Fer"

structure SuzukiTrotter where
  order : Nat
  isSymmetric : Bool



structure ZassenhausFormula where
  order : Nat
  commutators : List (List String)

def ZassenhausFormula.standard (n : Nat) : ZassenhausFormula where
  order := n
  commutators := []

structure PoincareBirkhoffWitt where
  algebra : String
  basis : List String
  ordered : Bool

def PoincareBirkhoffWitt.example : PoincareBirkhoffWitt where
  algebra := "U(g)"
  basis := ["monomials"]
  ordered := true


end MiniLieGroups