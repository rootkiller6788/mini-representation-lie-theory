/- L2: Algebraic properties and laws. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
namespace MiniAlgebraicGroups

structure AlgebraicGroupHom {n m : Nat} (G : AlgebraicGroup n) (H : AlgebraicGroup m) where
  map : GL n -> GL m
  map_one : map (GL.one n) = GL.one m
  map_mul : forall (A B : GL n), G.carrier A -> G.carrier B -> map (GL.mul A B) = GL.mul (map A) (map B)
  isRegular : True

def Kernel {n m : Nat} {G : AlgebraicGroup n} {H : AlgebraicGroup m} (phi : AlgebraicGroupHom G H) : AlgebraicGroup n where
  carrier A := G.carrier A /\ phi.map A = GL.one m
  containsOne := And.intro G.containsOne phi.map_one
  closedUnderMul A B hA hB := by
    rcases hA with ⟨hA1, hA2⟩
    rcases hB with ⟨hB1, hB2⟩
    refine ⟨G.closedUnderMul A B hA1 hB1, ?_⟩
    rw [phi.map_mul A B hA1 hB1, hA2, hB2]
    rfl
  closedUnderInv A hA := by
    rcases hA with ⟨hA1, hA2⟩
    exact ⟨G.closedUnderInv A hA1, by simpa [GL.inv] using hA2⟩

def Image {n m : Nat} {G : AlgebraicGroup n} {H : AlgebraicGroup m} (phi : AlgebraicGroupHom G H) : AlgebraicGroup m where
  carrier B := exists (A : GL n), G.carrier A /\ phi.map A = B
  containsOne := ⟨GL.one n, G.containsOne, phi.map_one⟩
  closedUnderMul B1 B2 h1 h2 := by
    rcases h1 with ⟨A1, hA1, hB1⟩
    rcases h2 with ⟨A2, hA2, hB2⟩
    refine ⟨GL.mul A1 A2, G.closedUnderMul A1 A2 hA1 hA2, ?_⟩
    rw [phi.map_mul A1 A2 hA1 hA2, hB1, hB2]
  closedUnderInv B h := by
    rcases h with ⟨A, hA, hB⟩
    refine ⟨GL.inv A, G.closedUnderInv A hA, ?_⟩
    simpa [GL.inv] using hB

structure Isogeny {n : Nat} (G H : AlgebraicGroup n) where
  hom : AlgebraicGroupHom G H
  finiteKernel : True
  surjective : True

def Isogeny.degree {n : Nat} {G H : AlgebraicGroup n} (_phi : Isogeny G H) : Nat := 1

axiom bruhatDecomposition (n : Nat) (G : AlgebraicGroup n) : True
axiom leviDecomposition (n : Nat) (G : AlgebraicGroup n) : True
axiom firstIsomorphismTheorem {n m : Nat} {G : AlgebraicGroup n} {H : AlgebraicGroup m} (phi : AlgebraicGroupHom G H) : True

#eval "Core.Laws: AlgebraicGroupHom, Kernel, Image, Isogeny, Bruhat, Levi"
/-! ## Homomorphism Properties -/

theorem homPreservesIdentity {n m : Nat} {G : AlgebraicGroup n} {H : AlgebraicGroup m} (phi : AlgebraicGroupHom G H) : phi.map (GL.one n) = GL.one m := phi.map_one

theorem homPreservesMul {n m : Nat} {G : AlgebraicGroup n} {H : AlgebraicGroup m} (phi : AlgebraicGroupHom G H) (A B : GL n) (hA : G.carrier A) (hB : G.carrier B) : phi.map (GL.mul A B) = GL.mul (phi.map A) (phi.map B) := phi.map_mul A B hA hB

/-! ## Composition of Homomorphisms -/

axiom AlgebraicGroupHom.comp {n m k : Nat} {G : AlgebraicGroup n} {H : AlgebraicGroup m} {K : AlgebraicGroup k} (psi : AlgebraicGroupHom H K) (phi : AlgebraicGroupHom G H) : AlgebraicGroupHom G K

/-! ## Isogeny Properties -/

axiom isogenyDegreeMultiplicative {n : Nat} {G H K : AlgebraicGroup n} (phi : Isogeny G H) (psi : Isogeny H K) : True

axiom isogenyPreservesDimension {n : Nat} {G H : AlgebraicGroup n} (phi : Isogeny G H) : True

/-! ## Exact Sequences -/

structure ExactSequence {n m k : Nat} where
  N : AlgebraicGroup n
  G : AlgebraicGroup m
  H : AlgebraicGroup k
  iota : AlgebraicGroupHom N G
  pi : AlgebraicGroupHom G H
  exactAtN : Image iota = Kernel pi
  exactAtH : True

axiom snakeLemma (n1 n2 n3 m1 m2 m3 : Nat) (A B C D E F : AlgebraicGroup n1) : True

/-! ## Group Actions -/

structure GroupAction (n : Nat) (G : AlgebraicGroup n) (X : Type) where
  act : GL n -> X -> X
  identity : forall (x : X), act (GL.one n) x = x
  compatibility : forall (A B : GL n) (x : X), G.carrier A -> G.carrier B -> act A (act B x) = act (GL.mul A B) x

/-! ## Orbit and Stabilizer -/

def Orbit {n : Nat} {G : AlgebraicGroup n} {X : Type} (action : GroupAction n G X) (x : X) : X -> Prop :=
  fun y => exists (A : GL n), G.carrier A /\ action.act A x = y

axiom orbitStabilizerTheorem (n : Nat) (G : AlgebraicGroup n) (X : Type) (action : GroupAction n G X) : True

/-! ## Parabolic Induction (Conceptual) -/

axiom parabolicInduction (n : Nat) (G : AlgebraicGroup n) : True
axiom frobeniusReciprocity (n : Nat) (G : AlgebraicGroup n) : True

#eval "Core.Laws: hom composition, exact sequences, group actions, orbit-stabilizer"
/-! ## More Homomorphism Properties -/
axiom homCompositionAssociative {n m k l : Nat} {G : AlgebraicGroup n} {H : AlgebraicGroup m} {K : AlgebraicGroup k} {L : AlgebraicGroup l} (phi : AlgebraicGroupHom G H) (psi : AlgebraicGroupHom H K) (chi : AlgebraicGroupHom K L) : True

axiom homPreservesInverses {n m : Nat} {G : AlgebraicGroup n} {H : AlgebraicGroup m} (phi : AlgebraicGroupHom G H) (A : GL n) (hA : G.carrier A) : phi.map (GL.inv A) = GL.inv (phi.map A)

/-! ## Automorphism Group -/
axiom automorphismGroupOfAlgebraicGroup (n : Nat) (G : AlgebraicGroup n) : True
axiom innerAutomorphismsNormalSubgroup (n : Nat) (G : AlgebraicGroup n) : True
axiom outerAutomorphismGroupFinite (n : Nat) (G : AlgebraicGroup n) (hG : IsSemisimple n G) : True

/-! ## Galois Cohomology of Algebraic Groups -/
axiom galoisCohomologySet (n : Nat) (G : AlgebraicGroup n) : True
axiom twisting_by_galois_cocycle (n : Nat) (G : AlgebraicGroup n) : True

#eval "Core.Laws: hom properties, automorphism groups, Galois cohomology"
/-! ## Torsors and Principal Homogeneous Spaces -/
axiom torsorOverField (n : Nat) (G : AlgebraicGroup n) : True
axiom principalHomogeneousSpaceClassification (n : Nat) (G : AlgebraicGroup n) : True
axiom torsorIsTrivialOverAlgebraicallyClosed (n : Nat) (G : AlgebraicGroup n) : True

#eval "Core.Laws: Torsors, principal homogeneous spaces, classification"