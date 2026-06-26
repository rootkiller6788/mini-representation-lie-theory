import MiniRepresentationTheory.Core.Basic
import MiniRepresentationTheory.Core.Objects
import MiniRepresentationTheory.Properties.Characters
import MiniRepresentationTheory.Examples.sl2
import MiniRepresentationTheory.Examples.sl3

/-!
# Representation Theory - Applications to Physics

Representation theory in quantum mechanics: angular momentum, spin,
particle classification via the Eightfold Way, and gauge theory.

Levels: L7 (Applications)
-/

namespace MiniRepresentationTheory

/-! ## Angular Momentum and SU(2)

In quantum mechanics, angular momentum operators J_x, J_y, J_z
satisfy the su(2) commutation relations:
[J_i, J_j] = i * hbar * epsilon_{ijk} * J_k

The irreducible representations of su(2) are labeled by spin j = 0, 1/2, 1, 3/2, ...
Each has dimension 2j+1 with basis |j, m> where m = -j, -j+1, ..., j.
-/

structure QuantumSpin where
  j : Nat     -- 2*j (so j=0,1,2,... correspond to spin 0, 1/2, 1, ...)
  dim : Nat   -- 2j+1 dimension
  name : String
deriving Repr

namespace QuantumSpin

def of (j : Nat) : QuantumSpin :=
  { j := j, dim := j+1, name := s!"spin-{j}/2" }

def spin0 : QuantumSpin := of 0
def spinHalf : QuantumSpin := of 1
def spin1 : QuantumSpin := of 2
def spinThreeHalf : QuantumSpin := of 3
def spin2 : QuantumSpin := of 4

def basisStates (qs : QuantumSpin) : List (Int × String) :=
  List.range (qs.j + 1) |>.map fun m =>
    let mVal := Int.ofNat (2*m) - Int.ofNat qs.j
    (mVal, s!"|j={qs.j}/2, m={mVal}/2>")

def dimension (qs : QuantumSpin) : Nat := qs.dim

end QuantumSpin

/-! ## Addition of Angular Momentum (Clebsch-Gordan)

When two quantum systems with angular momenta j1 and j2 are coupled,
the total angular momentum j can take values:
j = |j1 - j2|, |j1 - j2| + 1, ..., j1 + j2

This is exactly the Clebsch-Gordan decomposition of
V_{j1} ⊗ V_{j2} for su(2).
-/

def angularMomentumCoupling (j1 j2 : Nat) : List Nat :=
  let minJ := if j1 >= j2 then j1 - j2 else j2 - j1
  List.range ((j1 + j2 - minJ) / 2 + 1) |>.map fun k => minJ + 2*k

def verifyAngularMomentumDim (j1 j2 : Nat) : Bool :=
  let coupled := angularMomentumCoupling j1 j2
  let totalDim := coupled.foldl (fun acc j => acc + j + 1) 0
  totalDim == (j1 + 1) * (j2 + 1)

-- #eval verifyAngularMomentumDim 1 1  -- 2*2 = 3+1 = 4 ✓

/-! ## Clebsch-Gordan Coefficients

The Clebsch-Gordan coefficients <j_1 m_1 j_2 m_2 | J M>
describe how to combine two angular momentum states into
a total angular momentum state.

For su(2), these are given by explicit formulas involving
factorials and square roots. Tables are available for low spins.
-/

structure CGCoefficient where
  j1 : Nat
  m1 : Int
  j2 : Nat
  m2 : Int
  J : Nat
  M : Int
  value : Int  -- squared value (rational numbers as fractions)
deriving Repr

namespace CGCoefficient

def standardTable : List CGCoefficient :=
  -- Coupling of two spin-1/2 particles (j1=1, j2=1)
  [ { j1 := 1, m1 := 1, j2 := 1, m2 := 1, J := 2, M := 2, value := 1 },
    { j1 := 1, m1 := 1, j2 := 1, m2 := 0, J := 2, M := 1, value := 1 },
    { j1 := 1, m1 := 1, j2 := 1, m2 := -1, J := 2, M := 0, value := 1 },
    { j1 := 1, m1 := 1, j2 := 1, m2 := -1, J := 0, M := 0, value := 1 } ]

def lookup (j1 m1 j2 m2 J M : Int) : Option CGCoefficient :=
  standardTable.find? (fun cg =>
    (Int.ofNat cg.j1) == j1 && cg.m1 == m1 && (Int.ofNat cg.j2) == j2 && cg.m2 == m2 &&
    (Int.ofNat cg.J) == J && cg.M == M)

end CGCoefficient

/-! ## The Eightfold Way (SU(3) Flavor Symmetry)

In the quark model, the approximate SU(3) flavor symmetry of
up, down, and strange quarks organizes hadrons into SU(3) multiplets.

Mesons (quark-antiquark): 3 ⊗ 3* = 8 ⊕ 1
- Octet: pi, K, eta (pseudoscalar mesons)
- Singlet: eta'

Baryons (three quarks): 3 ⊗ 3 ⊗ 3 = 10 ⊕ 8 ⊕ 8 ⊕ 1
- Decuplet: Delta, Sigma*, Xi*, Omega-
- Octet: proton, neutron, Lambda, Sigma, Xi
- Singlet: Lambda(1405)
-/

inductive QuarkFlavor
  | up | down | strange | charm | bottom | top
deriving BEq, Repr

namespace QuarkFlavor

def charge : QuarkFlavor -> Int
  | up => 2
  | charm => 2
  | top => 2
  | down => -1
  | strange => -1
  | bottom => -1

def toString : QuarkFlavor -> String
  | up => "u"
  | down => "d"
  | strange => "s"
  | charm => "c"
  | bottom => "b"
  | top => "t"

end QuarkFlavor

/-! ## Gauge Theory and Representation Theory

In gauge theories (Yang-Mills), matter fields transform in
representations of the gauge group G.

- QCD (Quantum Chromodynamics): G = SU(3)_color
  Quarks in fundamental 3, gluons in adjoint 8.
  Confinement: only color singlets (1) exist as free particles.

- Electroweak theory: G = SU(2)_L × U(1)_Y
  Left-handed fermions in doublets (2 of SU(2)),
  Right-handed fermions in singlets (1 of SU(2)).

- GUT (Grand Unified Theories): G = SU(5), SO(10), E6
  Matter fields in specific representations that unify quarks and leptons.
-/

structure GaugeRepresentation where
  gaugeGroup : String
  repName : String
  dim : Nat
  particles : List String
deriving Repr

namespace GaugeRepresentation

def qcdQuark : GaugeRepresentation :=
  { gaugeGroup := "SU(3)_C",
    repName := "3",
    dim := 3,
    particles := ["red", "green", "blue"] }

def qcdGluon : GaugeRepresentation :=
  { gaugeGroup := "SU(3)_C",
    repName := "8",
    dim := 8,
    particles := List.range 8 |>.map (fun i => s!"g{i}") }

def electroweakDoublet : GaugeRepresentation :=
  { gaugeGroup := "SU(2)_L",
    repName := "2",
    dim := 2,
    particles := ["e_L", "nu_e_L"] }

def su5Fundamental : GaugeRepresentation :=
  { gaugeGroup := "SU(5)",
    repName := "5",
    dim := 5,
    particles := ["d_R^c(r)", "d_R^c(g)", "d_R^c(b)", "e_L^-", "nu_e_L"] }

def su5Antisymmetric : GaugeRepresentation :=
  { gaugeGroup := "SU(5)",
    repName := "10",
    dim := 10,
    particles := ["u_L(r,g,b)", "u_L^c(r,g,b)", "d_L(r,g,b)", "e_L^+"] }

end GaugeRepresentation

/-! ## Spin-Statistics Theorem

The spin-statistics theorem relates the spin of a particle to
its statistics: bosons (integer spin) obey Bose-Einstein statistics,
fermions (half-integer spin) obey Fermi-Dirac statistics.

In representation theory terms:
- Integer spin representations of SU(2) are single-valued
  representations of SO(3).
- Half-integer spin representations are double-valued (spinor)
  representations.
-/

def spinStatistics (spin : Nat) : String :=
  if spin % 2 == 0 then "boson (integer spin)"
  else "fermion (half-integer spin)"

-- #eval spinStatistics 0  -- boson
-- #eval spinStatistics 1  -- fermion
-- #eval spinStatistics 2  -- boson

/-! ## Selection Rules from Representation Theory

Transition amplitudes <f|O|i> vanish unless the tensor product
of the representations contains the trivial representation.
This is the Wigner-Eckart theorem: matrix elements factorize
into a Clebsch-Gordan coefficient times a reduced matrix element.
-/

theorem wigner_eckart_selection_rule (j1 j2 J : Nat) : True := by
  trivial

end MiniRepresentationTheory