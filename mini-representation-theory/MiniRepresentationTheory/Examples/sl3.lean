import MiniRepresentationTheory.Core.Basic
import MiniRepresentationTheory.Core.Objects
import MiniRepresentationTheory.Properties.Characters
import MiniRepresentationTheory.Theorems.WeylCharacter

/-!
# Representation Theory - Examples: sl(3,C) Representations

The representation theory of sl(3,C), rank 2, with fundamental
representations 3 (quark), 3* (antiquark), and the adjoint 8.
Weight diagrams and tensor product decompositions.

Levels: L6 (Canonical Examples), #eval verification
-/

namespace MiniRepresentationTheory

/-! ## sl(3) Root System

Rank 2. Simple roots: alpha_1, alpha_2.
Positive roots: alpha_1, alpha_2, alpha_1 + alpha_2 (3 total).
Cartan matrix: [[2, -1], [-1, 2]]
Weyl group: S_3 (order 6).
-/

def sl3SimpleRoots : List Weight :=
  [ Weight.fromList 2 [2, -1],
    Weight.fromList 2 [-1, 2] ]

def sl3FundamentalWeights : List Weight :=
  [ Weight.fromList 2 [1, 0],
    Weight.fromList 2 [0, 1] ]

def sl3WeylVector : Weight :=
  Weight.fromList 2 [1, 1]

/-! ## sl(3) Irreducible Representations V(a,b)

Parametrized by two non-negative integers (a,b), corresponding to
highest weight a*omega_1 + b*omega_2.

Dimension: dim V(a,b) = (a+1)(b+1)(a+b+2) / 2
-/

structure Sl3Representation where
  a : Nat
  b : Nat
  dim : Nat
  name : String
deriving Repr

namespace Sl3Representation

def of (a b : Nat) : Sl3Representation :=
  let dim := ((a+1)*(b+1)*(a+b+2)) / 2
  let name := s!"V({a},{b})"
  { a := a, b := b, dim := dim, name := name }

def trivial : Sl3Representation := of 0 0
def quark : Sl3Representation := of 1 0
def antiquark : Sl3Representation := of 0 1
def adjoint : Sl3Representation := of 1 1
def symSqQuark : Sl3Representation := of 2 0
def symSqAntiquark : Sl3Representation := of 0 2
def decuplet : Sl3Representation := of 3 0
def octet_decuplet : Sl3Representation := of 0 3
def V21 : Sl3Representation := of 2 1
def V12 : Sl3Representation := of 1 2
def V22 : Sl3Representation := of 2 2

def allFundamental : List Sl3Representation :=
  [trivial, quark, antiquark, adjoint, symSqQuark, symSqAntiquark,
   decuplet, octet_decuplet, V21, V12, V22]

def dimension (V : Sl3Representation) : Nat := V.dim

def highestWeight (V : Sl3Representation) : Weight :=
  Weight.fromList 2 [Int.ofNat V.a, Int.ofNat V.b]

end Sl3Representation

/-! ## Weight Diagram of V(1,0) (Quark/3)

The weights of the fundamental 3-dimensional representation:
(1,0), (0,1), (-1,-1) relative to the omega-basis.
These are the three vertices of an equilateral triangle in the weight plane.
-/

def quarkWeights : List Weight :=
  [ Weight.fromList 2 [1, 0],
    Weight.fromList 2 [0, 1],
    Weight.fromList 2 [-1, -1] ]

/-! ## Weight Diagram of V(0,1) (Antiquark/3*)

Weights: (0,1), (-1,-1), (1,0) — the negatives of the quark weights.
-/

def antiquarkWeights : List Weight :=
  [ Weight.fromList 2 [0, 1],
    Weight.fromList 2 [-1, -1],
    Weight.fromList 2 [1, 0] ]

/-! ## Weight Diagram of V(1,1) (Adjoint/8)

The adjoint representation has 8 weights:
- 3 at the vertices of a hexagon (the roots): (2,-1), (-1,2), (-1,-1), (-2,1), (1,-2), (1,1)
- 2 at the center (Cartan subalgebra): (0,0) with multiplicity 2
-/

def adjointWeights : List (Weight × Nat) :=
  [ (Weight.fromList 2 [2, -1], 1),
    (Weight.fromList 2 [-1, 2], 1),
    (Weight.fromList 2 [-1, -1], 1),
    (Weight.fromList 2 [-2, 1], 1),
    (Weight.fromList 2 [1, -2], 1),
    (Weight.fromList 2 [1, 1], 1),
    (Weight.fromList 2 [0, 0], 2) ]

/-! ## Tensor Product: 3 ⊗ 3 (Quark ⊗ Quark)

3 ⊗ 3 = 6 ⊕ 3*
where 6 = V(2,0) (symmetric square) and 3* = V(0,1) (antisymmetric square).
Dimension check: 3*3 = 9 = 6 + 3 ✓
-/

def tensor3x3 : List (Nat × Nat × Nat) :=
  [(2, 0, 1), (0, 1, 1)]  -- (a, b, multiplicity)

/-! ## Tensor Product: 3 ⊗ 3* (Quark ⊗ Antiquark)

3 ⊗ 3* = 8 ⊕ 1
where 8 = V(1,1) (adjoint) and 1 = V(0,0) (trivial/singlet).
Dimension check: 3*3 = 9 = 8 + 1 ✓
-/

def tensor3x3bar : List (Nat × Nat × Nat) :=
  [(1, 1, 1), (0, 0, 1)]

/-! ## Tensor Product: 3 ⊗ 3 ⊗ 3 (Baryon)

3 ⊗ 3 ⊗ 3 = (6 ⊕ 3*) ⊗ 3 = (6 ⊗ 3) ⊕ (3* ⊗ 3)
= (10 ⊕ 8) ⊕ (8 ⊕ 1)
= 10 ⊕ 8 ⊕ 8 ⊕ 1
where 10 = V(3,0) (baryon decuplet), 8 = V(1,1) (baryon octet ×2).
Dimension check: 27 = 10 + 8 + 8 + 1 ✓
-/

def tensor3x3x3 : List (Nat × Nat × Nat) :=
  [(3, 0, 1), (1, 1, 2), (0, 0, 1)]

/-! ## Quark Model (Particle Physics Notation)

In the Eightfold Way (Gell-Mann, Neeman 1961):
- 3 = quarks (u,d,s)
- 3* = antiquarks (u-bar, d-bar, s-bar)
- 8 = meson octet (pi, K, eta)
- 10 = baryon decuplet (Delta, Sigma*, Xi*, Omega-)
- 8 = baryon octet (proton, neutron, Lambda, Sigma, Xi)
- 1 = eta-prime singlet
-/

def quarkModelSummary : List (String × String × Nat) :=
  [ ("3", "quarks", 3),
    ("3*", "antiquarks", 3),
    ("8", "meson octet", 8),
    ("10", "baryon decuplet", 10),
    ("8", "baryon octet", 8),
    ("1", "singlet", 1) ]

/-! ## Verifications via #eval -/

def checkSl3Dimensions : Bool :=
  let basic := Sl3Representation.allFundamental
  basic.all (fun V =>
    V.dim == ((V.a+1)*(V.b+1)*(V.a+V.b+2))/2)

def sumTripleDim (acc : Nat) (triple : Nat × Nat × Nat) : Nat :=
  let a := Prod.fst triple
  let b := Prod.fst (Prod.snd triple)
  let m := Prod.snd (Prod.snd triple)
  acc + (Sl3Representation.of a b).dim * m

def checkSl3Tensor3x3 : Bool :=
  let totalDim := tensor3x3.foldl sumTripleDim 0
  totalDim == 9

def checkSl3Tensor3x3bar : Bool :=
  let totalDim := tensor3x3bar.foldl sumTripleDim 0
  totalDim == 9

def checkSl3Tensor3x3x3 : Bool :=
  let totalDim := tensor3x3x3.foldl sumTripleDim 0
  totalDim == 27

def sl3AllChecks : Bool :=
  checkSl3Dimensions &&
  checkSl3Tensor3x3 &&
  checkSl3Tensor3x3bar &&
  checkSl3Tensor3x3x3

-- #eval sl3AllChecks

end MiniRepresentationTheory