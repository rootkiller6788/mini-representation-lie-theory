/-
# MiniCharacterTheory.Constructions.TensorOperations

L3 Mathematical Structure: Tensor products, symmetric powers,
exterior powers of characters.
-/

import MiniCharacterTheory.Core.Operations
import MiniCharacterTheory.Core.AxiomCompat

namespace MiniCharacterTheory

def tensorProductChar {n : Nat} {G : FiniteGroup n}
    (chi psi : Character n G) : Character n G :=
  Character.mul chi psi

def symmetricSquareChar {n : Nat} {G : FiniteGroup n}
    (chi : Character n G) : Character n G :=
  fun g =>
    let chi_g := chi g
    let chi_g2 := chi (G.mul g g)
    (chi_g.mul chi_g).add chi_g2

def symmetricCubeChar {n : Nat} {G : FiniteGroup n}
    (chi : Character n G) : Character n G :=
  fun g =>
    let chi_g := chi g
    let chi_g2 := chi (G.mul g g)
    let chi_g3 := chi (G.mul (G.mul g g) g)
    let term1 := (chi_g.mul chi_g).mul chi_g
    let term2 := chi_g.mul chi_g2
    let term3 := CharValue.scalarMul 3 term2
    let term4 := CharValue.scalarMul 2 chi_g3
    (term1.add term3).add term4

def exteriorSquareChar {n : Nat} {G : FiniteGroup n}
    (chi : Character n G) : Character n G :=
  fun g =>
    let chi_g := chi g
    let chi_g2 := chi (G.mul g g)
    (chi_g.mul chi_g).sub chi_g2

def symmetricFourthChar {n : Nat} {G : FiniteGroup n}
    (chi : Character n G) : Character n G :=
  fun g =>
    let chi_g := chi g
    let chi_g2 := chi (G.mul g g)
    let chi_g3 := chi (G.mul (G.mul g g) g)
    let chi_g4 := chi (G.mul (G.mul (G.mul g g) g) g)
    let t1 := ((chi_g.mul chi_g).mul chi_g).mul chi_g
    let t2 := (chi_g.mul chi_g).mul chi_g2
    let t3 := chi_g2.mul chi_g2
    let t4 := chi_g.mul chi_g3
    (((t1.add (CharValue.scalarMul 6 t2)).add (CharValue.scalarMul 3 t3)).add
      (CharValue.scalarMul 8 t4)).add (CharValue.scalarMul 6 chi_g4)

def exteriorCubeChar {n : Nat} {G : FiniteGroup n}
    (chi : Character n G) : Character n G :=
  fun g =>
    let chi_g := chi g
    let chi_g2 := chi (G.mul g g)
    let chi_g3 := chi (G.mul (G.mul g g) g)
    let t1 := (chi_g.mul chi_g).mul chi_g
    let t2 := chi_g.mul chi_g2
    let t3 := chi_g3
    t1.sub ((CharValue.scalarMul 3 t2).add (CharValue.scalarMul 2 t3))

def tensorProductDecomposition : Axiom :=
  mkAxiom "tensorProductDecomposition"
    (Formula.pred 0 [])
    "chi otimes psi = sum_{tau in Irr(G)} <chi otimes psi, tau> * tau"

def plethysmSymmetricSquare : Axiom :=
  mkAxiom "plethysmSym2"
    (Formula.pred 0 [])
    "chi_{S^2(rho)}(g) = (chi(g)^2 + chi(g^2)) / 2"

def plethysmExteriorSquare : Axiom :=
  mkAxiom "plethysmExt2"
    (Formula.pred 0 [])
    "chi_{Lambda^2(rho)}(g) = (chi(g)^2 - chi(g^2)) / 2"

def schurPolynomialChar : Axiom :=
  mkAxiom "schurPolynomialChar"
    (Formula.pred 0 [])
    "Characters of GL(n) polynomial reps are Schur polynomials"

#eval "Constructions.TensorOperations: tensor product, symmetric/exterior powers"
#eval "Plethysm and Schur polynomial characters"

end MiniCharacterTheory
