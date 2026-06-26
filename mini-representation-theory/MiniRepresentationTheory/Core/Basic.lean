/-
# Representation Theory - Core Basic Definitions

Weight lattices, root systems, Cartan matrices, Dynkin diagrams,
and Weyl group actions. All constructions are combinatorial and
computable via `#eval`.

Levels covered: L1 (Definitions), L2 (Core Concepts), L3 (Math Structures)
-/

namespace MiniRepresentationTheory

/-! ## Helper Functions -/

def factorial : Nat -> Nat
  | 0 => 1
  | 1 => 1
  | n+1 => (n+1) * factorial n

/-! ## Weight Lattice

A weight is an element of the weight lattice P = Z^n.
-/

structure Weight where
  components : List Int
  rank : Nat
deriving BEq, Repr, Inhabited

namespace Weight

def zero (rank : Nat) : Weight :=
  { components := List.replicate rank 0, rank := rank }

def valid (w : Weight) : Bool :=
  w.components.length == w.rank

def add (w1 w2 : Weight) : Weight :=
  { components := List.zipWith (HAdd.hAdd) w1.components w2.components
    rank := w1.rank }

def sub (w1 w2 : Weight) : Weight :=
  { components := List.zipWith (HSub.hSub) w1.components w2.components
    rank := w1.rank }

def neg (w : Weight) : Weight :=
  { components := w.components.map (HMul.hMul (-1 : Int))
    rank := w.rank }

def smul (k : Int) (w : Weight) : Weight :=
  { components := w.components.map (HMul.hMul k)
    rank := w.rank }

def dot (w1 w2 : Weight) : Int :=
  List.zipWith (HMul.hMul) w1.components w2.components |>.sum

def equal (w1 w2 : Weight) : Bool :=
  w1.components == w2.components

def isZero (w : Weight) : Bool :=
  w.components.all (fun x => x == 0)

def get (w : Weight) (i : Nat) : Option Int :=
  w.components[i]?

def set (w : Weight) (i : Nat) (v : Int) : Weight :=
  { w with components := w.components.set i v }

def weightToString (w : Weight) : String :=
  let inner := String.intercalate ", " (w.components.map (fun (x : Int) => toString x))
  s!"({inner})"

instance : ToString Weight where
  toString w := weightToString w

def isDominantAux (comps : List Int) : Bool :=
  match comps with
  | [] => true
  | [_] => true
  | x::y::rest => x >= y && isDominantAux (y::rest)

def isDominantTypeA (w : Weight) : Bool :=
  isDominantAux w.components

def isIntegral (_w : Weight) : Bool := true

def toList (w : Weight) : List Int := w.components

def fromList (rank : Nat) (coeffs : List Int) : Weight :=
  { components := coeffs, rank := rank }

def scalarProduct (w : Weight) : Int := dot w w

def isRegular (_w : Weight) (_srs : SimpleRootSystem) : Bool := true

end Weight

/-! ## Cartan Matrix

The Cartan matrix A = (a_{ij}) encodes the geometry of the root system.
-/

structure CartanMatrix where
  rank : Nat
  entries : List (List Int)
deriving Repr, Inhabited

namespace CartanMatrix

def get (cm : CartanMatrix) (i j : Nat) : Option Int := do
  let row <- cm.entries[i]?
  row[j]?

def typeA (n : Nat) : CartanMatrix :=
  let rank := n - 1
  if _h : rank > 0 then
    let rows := List.range rank |>.map fun i =>
      List.range rank |>.map fun j =>
        if i == j then 2
        else if (i+1 == j || j+1 == i) then (-1 : Int)
        else 0
    { rank := rank, entries := rows }
  else { rank := 0, entries := [] }

def typeB (n : Nat) : CartanMatrix :=
  if _h : n > 0 then
    let rows := List.range n |>.map fun i =>
      List.range n |>.map fun j =>
        if i == j then 2
        else if (i+1 == j || j+1 == i) && i < n-1 then (-1 : Int)
        else if i == n-1 && j == n-2 then (-2 : Int)
        else if j == n-1 && i == n-2 then (-1 : Int)
        else 0
    { rank := n, entries := rows }
  else { rank := 0, entries := [] }

def typeC (n : Nat) : CartanMatrix :=
  if _h : n > 0 then
    let rows := List.range n |>.map fun i =>
      List.range n |>.map fun j =>
        if i == j then 2
        else if (i+1 == j || j+1 == i) && i < n-1 then (-1 : Int)
        else if i == n-1 && j == n-2 then (-1 : Int)
        else if j == n-1 && i == n-2 then (-2 : Int)
        else 0
    { rank := n, entries := rows }
  else { rank := 0, entries := [] }

def typeD (n : Nat) : CartanMatrix :=
  if _h : n > 3 then
    let rows := List.range n |>.map fun i =>
      List.range n |>.map fun j =>
        if i == j then 2
        else if (i+1 == j || j+1 == i) && i < n-2 then (-1 : Int)
        else 0
    { rank := n, entries := rows }
  else { rank := 0, entries := [] }

def typeE6 : CartanMatrix :=
  { rank := 6,
    entries := [
      [2, 0, -1, 0, 0, 0],
      [0, 2, 0, -1, 0, 0],
      [-1, 0, 2, -1, 0, 0],
      [0, -1, -1, 2, -1, 0],
      [0, 0, 0, -1, 2, -1],
      [0, 0, 0, 0, -1, 2]
    ] }

def typeE7 : CartanMatrix :=
  { rank := 7,
    entries := [
      [2, 0, -1, 0, 0, 0, 0],
      [0, 2, 0, -1, 0, 0, 0],
      [-1, 0, 2, -1, 0, 0, 0],
      [0, -1, -1, 2, -1, 0, 0],
      [0, 0, 0, -1, 2, -1, 0],
      [0, 0, 0, 0, -1, 2, -1],
      [0, 0, 0, 0, 0, -1, 2]
    ] }

def typeE8 : CartanMatrix :=
  { rank := 8,
    entries := [
      [2, 0, -1, 0, 0, 0, 0, 0],
      [0, 2, 0, -1, 0, 0, 0, 0],
      [-1, 0, 2, -1, 0, 0, 0, 0],
      [0, -1, -1, 2, -1, 0, 0, 0],
      [0, 0, 0, -1, 2, -1, 0, 0],
      [0, 0, 0, 0, -1, 2, -1, 0],
      [0, 0, 0, 0, 0, -1, 2, -1],
      [0, 0, 0, 0, 0, 0, -1, 2]
    ] }

def typeF4 : CartanMatrix :=
  { rank := 4,
    entries := [
      [2, -1, 0, 0],
      [-1, 2, -2, 0],
      [0, -1, 2, -1],
      [0, 0, -1, 2]
    ] }

def typeG2 : CartanMatrix :=
  { rank := 2,
    entries := [[2, -1], [-3, 2]] }

def det2 (cm : CartanMatrix) : Option Int := do
  let a <- cm.get 0 0
  let b <- cm.get 0 1
  let c <- cm.get 1 0
  let d <- cm.get 1 1
  some (a * d - b * c)

def isSymmetric (cm : CartanMatrix) : Bool :=
  List.range cm.rank |>.all fun i =>
    List.range cm.rank |>.all fun j =>
      match cm.get i j, cm.get j i with
      | some a, some b => a == b
      | _, _ => false

def isSymmetrizable (cm : CartanMatrix) : Bool :=
  let diag := List.range cm.rank |>.map fun i =>
    match cm.get i i with
    | some 2 => true
    | _ => false
  diag.all id

def trace (cm : CartanMatrix) : Option Int :=
  let entries := List.range cm.rank |>.map fun i =>
    match cm.get i i with
    | some v => v
    | none => 0
  some (entries.sum)

end CartanMatrix

/-! ## Simple Root System -/

structure SimpleRootSystem where
  rank : Nat
  cartan : CartanMatrix
  simpleRoots : List Weight
deriving Repr, Inhabited

namespace SimpleRootSystem

def typeA (n : Nat) : SimpleRootSystem :=
  let r := n - 1
  if _h : r > 0 then
    let simpleRoots := List.range r |>.map fun i =>
      let comps := List.range r |>.map fun j =>
        if j == i then (1 : Int)
        else if j+1 == i then (-1 : Int)
        else 0
      { components := comps, rank := r }
    { rank := r,
      cartan := CartanMatrix.typeA n,
      simpleRoots := simpleRoots }
  else
    { rank := 0, cartan := { rank := 0, entries := [] }, simpleRoots := [] }

def fundamentalWeights (srs : SimpleRootSystem) : List Weight :=
  match srs.rank with
  | 0 => []
  | _ =>
    List.range srs.rank |>.map fun i =>
      Weight.zero srs.rank |>.set i 1

def weylVector (srs : SimpleRootSystem) : Weight :=
  let fws := fundamentalWeights srs
  fws.foldl Weight.add (Weight.zero srs.rank)

def numPositiveRoots (srs : SimpleRootSystem) : Nat :=
  match srs.rank with
  | r => r * (r + 1) / 2

def coxeterNumber (srs : SimpleRootSystem) : Nat :=
  match srs.rank with
  | 0 => 0
  | r => r + 1

end SimpleRootSystem

/-! ## Weyl Group Action -/

structure WeylReflection where
  index : Nat
  root : Weight
deriving Repr

def simpleReflection (alpha : Weight) (lambda : Weight) : Weight :=
  let pairing := Weight.dot lambda alpha
  Weight.sub lambda (Weight.smul pairing alpha)

def signOfReflection (len : Nat) : Int :=
  if len % 2 == 0 then 1 else -1

/-! ## Dynkin Diagrams -/

inductive DynkinType
  | A (n : Nat)
  | B (n : Nat)
  | C (n : Nat)
  | D (n : Nat)
  | E6 | E7 | E8
  | F4 | G2
deriving BEq, Repr, Inhabited

namespace DynkinType

def rank : DynkinType -> Nat
  | A n => n
  | B n => n
  | C n => n
  | D n => n
  | E6 => 6
  | E7 => 7
  | E8 => 8
  | F4 => 4
  | G2 => 2

def dim : DynkinType -> Nat
  | A n => n * (n + 2)
  | B n => n * (2*n + 1)
  | C n => n * (2*n + 1)
  | D n => n * (2*n - 1)
  | E6 => 78
  | E7 => 133
  | E8 => 248
  | F4 => 52
  | G2 => 14

def numPosRoots : DynkinType -> Nat
  | A n => n * (n + 1) / 2
  | B n => n * n
  | C n => n * n
  | D n => n * (n - 1)
  | E6 => 36
  | E7 => 63
  | E8 => 120
  | F4 => 24
  | G2 => 6

def weylGroupOrder : DynkinType -> Nat
  | A n => factorial (n + 1)
  | B n => (2 ^ n) * factorial n
  | C n => (2 ^ n) * factorial n
  | D n => (2 ^ (n - 1)) * factorial n
  | E6 => 51840
  | E7 => 2903040
  | E8 => 696729600
  | F4 => 1152
  | G2 => 12

def dualCoxeterNumber : DynkinType -> Nat
  | A n => n + 1
  | B n => 2*n - 1
  | C n => n + 1
  | D n => 2*n - 2
  | E6 => 12
  | E7 => 18
  | E8 => 30
  | F4 => 9
  | G2 => 4

def dtToString : DynkinType -> String
  | A n => s!"A{n}"
  | B n => s!"B{n}"
  | C n => s!"C{n}"
  | D n => s!"D{n}"
  | E6 => "E6"
  | E7 => "E7"
  | E8 => "E8"
  | F4 => "F4"
  | G2 => "G2"

end DynkinType

/-! ## Positive Roots Enumeration

For computational purposes, we enumerate all positive roots.
-/

def positiveRootsTypeA (n : Nat) : List Weight :=
  if _h : n > 0 then
    (List.range n).foldl (fun acc i =>
      acc ++ ((List.range n).filterMap fun j =>
        if i < j then
          let comps := List.range n |>.map fun k =>
            if k == i then (1 : Int)
            else if k == j then (-1 : Int)
            else 0
          some { components := comps, rank := n }
        else none)) []
  else []

def weylVectorTypeA (n : Nat) : Weight :=
  let posRoots := positiveRootsTypeA n
  posRoots.foldl (fun acc r =>
    { components := List.zipWith (HAdd.hAdd) acc.components r.components,
      rank := acc.rank })
    (Weight.zero n)

end MiniRepresentationTheory