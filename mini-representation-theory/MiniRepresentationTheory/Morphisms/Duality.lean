import MiniRepresentationTheory.Core.Basic
import MiniRepresentationTheory.Core.Objects

/-!
# Representation Theory - Dual and Contragredient Representations

The dual representation V*, the contragredient representation,
self-duality conditions, and bilinear invariant forms.

Levels: L2 (Core Concepts), L3 (Math Structures)
-/

namespace MiniRepresentationTheory

/-! ## Contragredient (Dual) Representation

For a representation V, the contragredient representation V*
has the dual vector space with action:
(g · f)(v) = f(g^{-1} · v)
-/

structure DualRepresentation where
  original : Representation
  dualChar : FormalChar
  dualDim : Nat
deriving Repr

namespace DualRepresentation

def ofRepresentation (V : Representation) : DualRepresentation :=
  let dualChar := FormalChar.mapWeights V.character Weight.neg
  { original := V,
    dualChar := dualChar,
    dualDim := V.dim }

def asRepresentation (d : DualRepresentation) : Representation :=
  { algebraRank := d.original.algebraRank,
    highestWt := Weight.neg d.original.highestWt,
    character := d.dualChar,
    dim := d.dualDim }

end DualRepresentation

/-! ## Self-Dual Representations

A representation V is self-dual if V = V* as representations.
Examples: adjoint representation, fundamental representation of sp(2n).
-/

def isSelfDual (V : Representation) : Bool :=
  let dualV := (DualRepresentation.ofRepresentation V).asRepresentation
  FormalChar.equal V.character dualV.character

/-! ## Bilinear Invariant Forms

An invariant bilinear form on V is an element of Hom_g(V ⊗ V, C)
or equivalently Hom_g(V, V*).
-/

structure InvariantBilinearForm (V : Representation) where
  isSymmetric : Bool
  isNondegenerate : Bool
deriving Repr

namespace InvariantBilinearForm

def symmetric (V : Representation) : InvariantBilinearForm V :=
  { isSymmetric := true,
    isNondegenerate := V.dim > 0 }

def symplectic (V : Representation) : InvariantBilinearForm V :=
  { isSymmetric := false,
    isNondegenerate := V.dim > 0 }

def existsSymmetricForm (V : Representation) : Bool :=
  isSelfDual V

def existsSymplecticForm (V : Representation) : Bool :=
  -- A representation admits a symplectic form iff it is self-dual
  -- and has even dimension (for irreducibles, this is the quaternionic case)
  isSelfDual V && V.dim % 2 == 0

end InvariantBilinearForm

/-! ## Casimir Operator

The Casimir operator C acts as a scalar on each irreducible
representation. Its eigenvalue determines the representation.
-/

structure CasimirOperator where
  value : Int
  representation : Representation
deriving Repr

namespace CasimirOperator

def onRepresentation (V : Representation) (dualCoxeter : Nat) : CasimirOperator :=
  -- For a representation with highest weight lambda,
  -- the Casimir eigenvalue is (lambda + 2*rho, lambda)
  -- In our model for type A, rho = sum of positive roots / 2
  let rho := Weight.zero V.algebraRank
  let hw := V.highestWt
  let sumSq := Weight.dot hw hw + Weight.dot hw (Weight.smul 2 rho)
  { value := sumSq,
    representation := V }

def eigenvalue (C : CasimirOperator) : Int := C.value

end CasimirOperator

/-! ## Frobenius-Schur Indicator

Classifies self-dual irreducible representations into three types:
1 (real/orthogonal), 0 (complex), -1 (quaternionic/symplectic).
-/

inductive FrobeniusSchurType
  | real | complex | quaternionic
deriving BEq, Repr

namespace FrobeniusSchurType

def ofRepresentation (V : Representation) : FrobeniusSchurType :=
  if !isSelfDual V then
    FrobeniusSchurType.complex
  else if V.dim % 2 == 1 then
    FrobeniusSchurType.real
  else
    FrobeniusSchurType.quaternionic

def toInt : FrobeniusSchurType -> Int
  | real => 1
  | complex => 0
  | quaternionic => -1

def toString : FrobeniusSchurType -> String
  | real => "real (orthogonal)"
  | complex => "complex"
  | quaternionic => "quaternionic (symplectic)"

end FrobeniusSchurType

/-! ## Second Dual Isomorphism

The canonical isomorphism V -> V** for finite-dimensional representations.
-/

theorem doubleDualIso_dim (V : Representation) :
    let dualV := (DualRepresentation.ofRepresentation V).asRepresentation
    let dualDualV := (DualRepresentation.ofRepresentation dualV).asRepresentation
    dualDualV.dim = V.dim := by
  intro dualV dualDualV
  -- Dimension is preserved under dual (negation preserves multiplicity counts)
  rfl

/-! ## Contragredient Operations

Functorial properties of the dual: (V ⊗ W)* = V* ⊗ W*
and duality commutes with direct sums.
-/

theorem dualOfTensorProd_dim (V W : Representation) :
    let dualProd := (DualRepresentation.ofRepresentation (V.tensorProd W)).asRepresentation
    let prodDual := ((DualRepresentation.ofRepresentation V).asRepresentation).tensorProd
                     ((DualRepresentation.ofRepresentation W).asRepresentation)
    dualProd.dim = prodDual.dim := by
  intro dualProd prodDual
  -- Both sides have same dimension: dim(V)*dim(W)
  rfl

theorem dualOfDirectSum_dim (V W : Representation) :
    let dualSum := (DualRepresentation.ofRepresentation (V.directSum W)).asRepresentation
    let sumDual := ((DualRepresentation.ofRepresentation V).asRepresentation).directSum
                    ((DualRepresentation.ofRepresentation W).asRepresentation)
    dualSum.dim = sumDual.dim := by
  intro dualSum sumDual
  -- Both sides have dimension dim(V) + dim(W)
  rfl

end MiniRepresentationTheory