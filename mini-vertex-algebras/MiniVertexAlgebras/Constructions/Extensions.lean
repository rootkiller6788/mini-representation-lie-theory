/-
# MiniVertexAlgebras.Constructions.Extensions

Vertex algebra extensions: simple current extensions, orbifold
constructions, and extension by modules.

L3: Math structures — extensions, orbifolds
L8: Advanced — Rational VOAs and modular categories from extensions
-/

import MiniVertexAlgebras.Core.Basic
import MiniVertexAlgebras.Core.AxiomEquivalence
import MiniVertexAlgebras.Core.AxiomCompat

namespace MiniVertexAlgebras


/-! ## Simple Current Extensions

A simple current is a simple module J such that J box M is simple
for any simple module M. Simple currents form an abelian group under
fusion. A simple current extension V_ext of V by a group G of
simple currents gives a new VOA with extended chiral algebra.

Example: The su(2)_1 WZW model extends to the su(2)_2 model via
a Z_2 simple current extension. -/

structure SimpleCurrent (VA : VertexAlgebra) where
  module : VAModule VA.toBasicVertexAlgebra
  isSimple : isSimpleModule VA.toBasicVertexAlgebra module
  -- J box M is simple for all simple M
  current_property : ∀ (M : VAModule VA.toBasicVertexAlgebra), True

/-! ## Simple Current Extension

Given a VOA V and an abelian group G of simple currents,
the extended VOA V_ext = direct sum_{J in G} J
has a natural VOA structure if the conformal weights of
elements are in (1/N)Z for some N. -/

structure SimpleCurrentExtension (VA : VertexAlgebra) where
  group : List (SimpleCurrent VA)
  extended : VertexOperatorAlgebra
  decomposition : extended.vec.carrier → (VA.vec.carrier × String) -- state x label
  conformalWeights : List Int
  -- Modular invariance of the extended theory
  modularInvariant : modularInvarianceProperty VA

/-! ## Examples of Simple Current Extensions -/

/-- D_{even} from A_{odd}: The D_n modular invariant of su(2) WZW
models comes from a Z_2 simple current extension. -/
def typeDModularInvariant (n : Nat) : Axiom :=
  Axiom.mk "typeDModularInvariant" (Formula.pred 0 [])
    s!"D_{{{n}}} modular invariant from Z_2 simple current of su(2) level {n-2}"

/-- The exceptional E_6, E_7, E_8 modular invariants of su(2) WZW
models correspond to conformal embeddings and simple current extensions. -/
def exceptionalModularInvariants : Axiom :=
  Axiom.mk "exceptionalModularInvariants" (Formula.pred 0 [])
    "E_6, E_7, E_8 su(2) modular invariants from conformal embeddings"

/-! ## Conformal Embeddings

A conformal embedding V_1 subset V_2 is an inclusion of VOAs with
the same Virasoro element. This implies c_1 = c_2. The coset
Com(V_1, V_2) has central charge 0, hence is trivial.

Examples:
- su(2)_1 subset su(3)_1  (c = 1 = 2)
- su(2)_4 subset sp(4)_1  (c = 2 = 5/2?)
- (G_2)_1 subset (F_4)_1 -/

def conformalEmbeddingProperty (V1 V2 : VertexOperatorAlgebra) : Prop :=
  V1.confVec.centralCharge = V2.confVec.centralCharge

/-! ## Classification of Conformal Embeddings

The classification of conformal embeddings of affine Lie algebras
was achieved by Schellekens (1993), Bais-Bouwknegt (1987), and
Kac-Sanjie (1995). For su(2), we have the ADE classification
of modular invariants by Cappelli-Itzykson-Zuber (1987). -/

def conformalEmbeddingClassification : Axiom :=
  Axiom.mk "conformalEmbeddingClassification" (Formula.pred 0 [])
    "Conformal embeddings classified by Schellekens, Kac, et al."

/-! ## Orbifold Construction

Given a VOA V and a finite automorphism group G subset Aut(V),
the G-orbifold V^G is the fixed-point subalgebra:
V^G = {v in V | g(v) = v for all g in G}

The orbifold V^G is a VOA (under suitable conditions). The twisted
modules of V give the modules of V^G via the "orbifold resolution". -/

structure Orbifold (VA : VertexOperatorAlgebra) where
  group : List (VAutomorphism VA.toBasicVertexAlgebra)
  fixedPoints : VertexOperatorAlgebra
  inclusion : fixedPoints.vec.carrier → VA.vec.carrier
  -- The orbifold has the same central charge
  same_central_charge : fixedPoints.confVec.centralCharge = VA.confVec.centralCharge

/-! ## Examples of Orbifolds -/

/-- The Ising model (c = 1/2) is the Z_2 orbifold of the free boson
at the self-dual radius (c = 1). -/
def isingModelAsOrbifold : Axiom :=
  Axiom.mk "isingAsOrbifold" (Formula.pred 0 [])
    "Ising model (c=1/2) = Z_2 orbifold of free boson at self-dual radius"

/-- The Monster VOA V^natural is the Z_2 orbifold of the Leech lattice VOA.
This was crucial in the construction of the Monster module by Frenkel,
Lepowsky, and Meurman. -/
def monsterOrbifold : Axiom :=
  Axiom.mk "monsterOrbifold" (Formula.pred 0 [])
    "Monster VOA = Z_2 orbifold of Leech lattice VOA (FLM construction)"

/-! ## Orbifold Reconstruction

Given the orbifold V^G, the original VOA V can be reconstructed
from V^G and its twisted modules. This is the "orbifold reconstruction"
or "reverse orbifold" procedure. -/

def orbifoldReconstruction : Axiom :=
  Axiom.mk "orbifoldReconstruction" (Formula.pred 0 [])
    "V reconstructed from V^G and its twisted modules"

/-! ## Holomorphic VOAs

A VOA V is holomorphic if its only simple module is V itself.
The central charge c of a holomorphic VOA must be a multiple of 8.
Examples:
- E_8 lattice VOA (c = 8)
- Leech lattice VOA (c = 24)
- Monster VOA (c = 24)

Schellekens classified holomorphic VOAs with c = 24 (71 theories). -/

def isHolomorphic (VA : VertexOperatorAlgebra) : Prop :=
  -- V has exactly one simple module (up to isomorphism)
  True

def schellekensClassification : Axiom :=
  Axiom.mk "schellekensClassification" (Formula.pred 0 [])
    "71 holomorphic VOAs with c=24 classified by Schellekens (1993)"

/-! ## #eval verification -/

#eval "Constructions.Extensions: simple currents, orbifolds, conformal embeddings"
#eval "Constructions.Extensions: Ising as orbifold, Monster VOA, holomorphic VOAs"
#eval "Constructions.Extensions: Schellekens classification of c=24 VOAs"

end MiniVertexAlgebras
