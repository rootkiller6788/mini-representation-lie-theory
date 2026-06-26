import MiniRepresentationTheory.Core.Basic
import MiniRepresentationTheory.Core.Objects
import MiniRepresentationTheory.Core.Laws
import MiniRepresentationTheory.Properties.Irreducibility
import MiniRepresentationTheory.Properties.Characters
import MiniRepresentationTheory.Theorems.SchurLemma
import MiniRepresentationTheory.Theorems.HighestWeight
import MiniRepresentationTheory.Theorems.WeylCharacter

/-!
# Representation Theory - Examples: sl(2,C) Representations

The complete classification and construction of all finite-dimensional
representations of sl(2,C), the simplest semisimple Lie algebra.

sl(2,C) has basis {h, e, f} with relations:
[h, e] = 2e, [h, f] = -2f, [e, f] = h

Levels: L6 (Canonical Examples), #eval verification
-/

namespace MiniRepresentationTheory

/-! ## The Lie Algebra sl(2,C)

sl(2,C) is the Lie algebra of 2x2 traceless complex matrices.
Rank 1, with a single simple root alpha.
-/

inductive Sl2BasisElement
  | H | E | F
deriving BEq, Repr

namespace Sl2BasisElement

def toString : Sl2BasisElement -> String
  | Sl2BasisElement.H => "H"
  | Sl2BasisElement.E => "E"
  | Sl2BasisElement.F => "F"

def actionOnWeight (el : Sl2BasisElement) (w : Weight) : Option Weight :=
  match el with
  | Sl2BasisElement.H => some w
  | Sl2BasisElement.E =>
    -- E raises the weight by alpha
    some (Weight.add w (Weight.fromList 1 [2]))
  | Sl2BasisElement.F =>
    -- F lowers the weight by -alpha
    some (Weight.sub w (Weight.fromList 1 [2]))

end Sl2BasisElement

/-! ## Classification of sl(2) Irreducibles

For each non-negative integer n (or half-integer j = n/2), there is
a unique irreducible representation V_n of dimension n+1.

The representation V_n has a weight space decomposition:
V_n = V_{-n} ⊕ V_{-n+2} ⊕ ... ⊕ V_{n-2} ⊕ V_n

where V_k is the 1-dimensional weight space with weight k*alpha/2.
-/

structure Sl2Representation where
  highestWeight : Int
  dim : Nat
  weights : List Int
deriving Repr

namespace Sl2Representation

def ofSpin (n : Nat) : Sl2Representation :=
  let weights := List.range (n+1) |>.map (fun k => Int.ofNat (2*k) - Int.ofNat n)
  { highestWeight := Int.ofNat n,
    dim := n+1,
    weights := weights }

def fundamental : Sl2Representation := ofSpin 1
def trivial : Sl2Representation := ofSpin 0
def adjoint : Sl2Representation := ofSpin 2

def character (V : Sl2Representation) : FormalChar :=
  let terms := V.weights.map fun w =>
    ({ components := [w], rank := 1 }, 1)
  { terms := terms }

def toRepresentation (V : Sl2Representation) : Representation :=
  { algebraRank := 1,
    highestWt := { components := [V.highestWeight], rank := 1 },
    character := V.character,
    dim := V.dim }

end Sl2Representation

/-! ## Tensor Product Decomposition (Clebsch-Gordan)

V_n ⊗ V_m = V_{|n-m|} ⊕ V_{|n-m|+2} ⊕ ... ⊕ V_{n+m}

Proof: The character of V_n ⊗ V_m is:
(sin((n+1)theta)/sin(theta)) * (sin((m+1)theta)/sin(theta))
= sum_{k = |n-m|, step 2}^{n+m} sin((k+1)theta)/sin(theta)
-/

def clebschGordan (n m : Nat) : List (Nat × Nat) :=
  let minSp := if n >= m then n - m else m - n
  List.range ((n + m - minSp) / 2 + 1) |>.map fun k =>
    (minSp + 2*k, 1)

def verifyClebschGordanDim (n m : Nat) : Bool :=
  let decomp := clebschGordan n m
  let totalDim := decomp.foldl (fun acc (spin, mult) =>
    acc + (spin + 1) * mult) 0
  totalDim == (n + 1) * (m + 1)

/-! ## Explicit Casimir Operator for sl(2)

C = h^2 + 2(ef + fe) = h^2 + 2h + 4fe

On V_n, C acts as n(n+2) * id.
-/

def sl2CasimirEigenvalue (n : Nat) : Nat := n * (n + 2)

theorem sl2_casimir_nonneg (n : Nat) : sl2CasimirEigenvalue n >= 0 := by
  unfold sl2CasimirEigenvalue
  apply Nat.zero_le

/-! ## Complete List of sl(2) Irreducibles (Low Dimensions) -/

def sl2Irreducibles : List Sl2Representation :=
  List.range 11 |>.map Sl2Representation.ofSpin
  -- spins 0 through 10

def sl2IrreducibleDims : List Nat :=
  sl2Irreducibles.map (fun V => V.dim)

-- #eval sl2IrreducibleDims
-- Expected: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-! ## Weight Diagrams for sl(2) -/

def sl2WeightDiagram (n : Nat) : List (Int × Nat) :=
  -- Returns list of (weight, multiplicity) for V_n
  List.range (n+1) |>.map fun k =>
    let w := Int.ofNat (2*k) - Int.ofNat n
    (w, 1)

/-! ## Symmetric Powers of the Fundamental Representation

For sl(2), Sym^k(V_1) = V_k.
V_1 is the standard 2-dimensional representation.
-/

def symmetricPower (k : Nat) : Sl2Representation :=
  Sl2Representation.ofSpin k

theorem sym_power_fundamental (k : Nat) : (symmetricPower k).dim = k+1 := by rfl

/-! ## Exterior Powers

For sl(2), the exterior powers are:
Λ^0(V_n) = V_0 (trivial)
Λ^1(V_n) = V_n
Λ^2(V_n) = V_{2n-2} ⊕ V_{2n-6} ⊕ ...
For n=1: Λ^2(V_1) = V_0 (since dimV_1 = 2, exterior square is 1-dim)
-/

def exteriorSquare (n : Nat) : List (Nat × Nat) :=
  if n == 0 then [(0, 1)]
  else if n == 1 then [(0, 1)]
  else
    -- Λ^2(V_n) decomposes as sum of irreducibles
    let maxSpin := 2*n - 2
    List.range (maxSpin / 4 + 1) |>.map fun k =>
      (maxSpin - 4*k, 1)

/-! ## #eval Verifications

The following #eval commands verify key properties of sl(2) representations.
-/

def checkSl2Properties : Bool :=
  -- 1. Clebsch-Gordan dimension check for small cases
  let cg1 := verifyClebschGordanDim 1 1  -- 2 ⊗ 2 = 1 ⊕ 3
  let cg2 := verifyClebschGordanDim 1 2  -- 2 ⊗ 3 = 2 ⊕ 4
  let cg3 := verifyClebschGordanDim 2 2  -- 3 ⊗ 3 = 1 ⊕ 3 ⊕ 5

  -- 2. Dimension formula: dim V_n = n+1
  let dims := List.range 10 |>.all (fun n => (Sl2Representation.ofSpin n).dim == n+1)

  -- 3. Character sum: sum of weight spaces = dim
  let charSum := List.range 5 |>.all (fun n =>
    let V := Sl2Representation.ofSpin n
    V.weights.length == V.dim)

  cg1 && cg2 && cg3 && dims && charSum

-- #eval checkSl2Properties

end MiniRepresentationTheory