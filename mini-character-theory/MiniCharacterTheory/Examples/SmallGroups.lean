/-
# MiniCharacterTheory.Examples.SmallGroups

L6 Canonical Examples: Character tables of small finite groups.
S_3, S_4, A_4, A_5, D_4, Q_8 — with concrete character values.
-/

import MiniCharacterTheory.Theorems.Fundamental
import MiniCharacterTheory.Properties.Degrees

namespace MiniCharacterTheory

/-! ## S_3 (Symmetric group on 3 letters, order 6)

S_3 has conjugacy classes: {1}, {(12),(13),(23)} (transpositions, 3 elements),
{(123),(132)} (3-cycles, 2 elements).

Character table of S_3:
      1    (12)   (123)
chi_1  1     1      1    (trivial)
chi_2  1    -1      1    (sign)
chi_3  2     0     -1    (standard, 2-dim)

Degree pattern: [1, 1, 2], sum of squares = 1+1+4 = 6 = |S_3|
-/

def s3CharTable : List (List Int) :=
  [ [1, 1, 1],
    [1, -1, 1],
    [2, 0, -1] ]

def s3Degrees : List Nat := [1, 1, 2]
def s3Order : Nat := 6

def checkS3CharTable : Bool :=
  let degSq := s3Degrees.foldl (fun acc d => acc + d * d) 0
  degSq == s3Order

#eval "S_3 character table: trivial(1,1,1), sign(1,-1,1), standard(2,0,-1)"
#eval checkS3CharTable

/-! ## S_4 (Symmetric group on 4 letters, order 24)

S_4 has 5 conjugacy classes:
  1, (12) transpositions, (12)(34) double transpositions,
  (123) 3-cycles, (1234) 4-cycles

Character table of S_4:
       1  (12) (12)(34) (123) (1234)
chi_1  1   1      1      1      1    (trivial)
chi_2  1  -1      1      1     -1    (sign)
chi_3  2   0      2     -1      0    (from S_4/V_4 = S_3, standard of S_3)
chi_4  3   1     -1      0     -1    (standard representation)
chi_5  3  -1     -1      0      1    (sign * standard)

Degree pattern: [1, 1, 2, 3, 3]
Sum of squares = 1+1+4+9+9 = 24 = |S_4|
-/

def s4CharTable : List (List Int) :=
  [ [1, 1, 1, 1, 1],
    [1, -1, 1, 1, -1],
    [2, 0, 2, -1, 0],
    [3, 1, -1, 0, -1],
    [3, -1, -1, 0, 1] ]

def s4Degrees : List Nat := [1, 1, 2, 3, 3]
def s4Order : Nat := 24

def checkS4CharTable : Bool :=
  let degSq := s4Degrees.foldl (fun acc d => acc + d * d) 0
  degSq == s4Order

#eval "S_4 character table: 5 irr chars, degrees [1,1,2,3,3]"
#eval checkS4CharTable

/-! ## A_4 (Alternating group on 4 letters, order 12)

A_4 has 4 conjugacy classes: {1}, {(12)(34), (13)(24), (14)(23)} (3 elts),
{(123), (142), (134), (243)} (4 elts), {(132), (124), (143), (234)} (4 elts).

Character table of A_4:
       1   (12)(34)  (123)  (132)
chi_1  1      1        1      1    (trivial)
chi_2  1      1       w      w^2   (omega = e^{2pi i/3})
chi_3  1      1      w^2     w     (conjugate)
chi_4  3     -1        0      0    (permutation - trivial)

Here w = (-1 + sqrt(-3))/2 is a primitive cube root of unity.
-/

def a4CharTableComplex : List (List String) :=
  [ ["1", "1", "1", "1"],
    ["1", "1", "w", "w^2"],
    ["1", "1", "w^2", "w"],
    ["3", "-1", "0", "0"] ]

def a4Degrees : List Nat := [1, 1, 1, 3]
def a4Order : Nat := 12

def checkA4CharTable : Bool :=
  let degSq := a4Degrees.foldl (fun acc d => acc + d * d) 0
  degSq == a4Order

#eval "A_4 character table: 4 irr chars, degrees [1,1,1,3]"
#eval checkA4CharTable
#eval "A_4 uses primitive cube roots of unity (w = e^{2pi i/3})"

/-! ## A_5 (Alternating group on 5 letters, order 60)

A_5 is the smallest non-abelian simple group.
Order 60 = 2^2 * 3 * 5 (three distinct primes, per Burnside theorem).

Conjugacy classes: 5 classes
  1, (12)(34), (123), (12345), (13524)

Character table of A_5:
       1  (12)(34)  (123)  (12345)  (13524)
chi_1  1     1        1       1        1
chi_2  3    -1        0   (1+sqrt5)/2  (1-sqrt5)/2
chi_3  3    -1        0   (1-sqrt5)/2  (1+sqrt5)/2
chi_4  4     0        1      -1        -1
chi_5  5     1       -1       0         0

Degrees: [1, 3, 3, 4, 5]
Sum of squares = 1+9+9+16+25 = 60 = |A_5|
-/

def a5Degrees : List Nat := [1, 3, 3, 4, 5]
def a5Order : Nat := 60

def checkA5Degrees : Bool :=
  let degSq := a5Degrees.foldl (fun acc d => acc + d * d) 0
  degSq == a5Order

#eval "A_5 character table: 5 irr chars, degrees [1,3,3,4,5]"
#eval checkA5Degrees
#eval "A_5 is simple non-abelian; order 60 = 2^2 * 3 * 5 (3 primes)"

/-! ## Q_8 (Quaternion group, order 8)

Q_8 = {1, -1, i, -i, j, -j, k, -k} with i^2=j^2=k^2=ijk=-1.

Conjugacy classes: {1}, {-1}, {i,-i}, {j,-j}, {k,-k}

Character table of Q_8:
       1   -1    i    j    k
chi_1  1    1    1    1    1
chi_2  1    1    1   -1   -1
chi_3  1    1   -1    1   -1
chi_4  1    1   -1   -1    1
chi_5  2   -2    0    0    0

Degrees: [1, 1, 1, 1, 2]
Sum of squares = 1+1+1+1+4 = 8 = |Q_8|
-/

def q8CharTable : List (List Int) :=
  [ [1, 1, 1, 1, 1],
    [1, 1, 1, -1, -1],
    [1, 1, -1, 1, -1],
    [1, 1, -1, -1, 1],
    [2, -2, 0, 0, 0] ]

def q8Degrees : List Nat := [1, 1, 1, 1, 2]
def q8Order : Nat := 8

def checkQ8CharTable : Bool :=
  let degSq := q8Degrees.foldl (fun acc d => acc + d * d) 0
  degSq == q8Order

#eval "Q_8 character table: 5 irr chars, degrees [1,1,1,1,2]"
#eval checkQ8CharTable

/-! ## D_4 (Dihedral group of order 8)

D_4 = <r, s | r^4 = s^2 = 1, srs = r^{-1}>

Conjugacy classes: {1}, {r^2}, {r, r^3}, {s, sr^2}, {sr, sr^3}

Character table of D_4:
       1   r^2   r    s    sr
chi_1  1    1    1    1    1
chi_2  1    1    1   -1   -1
chi_3  1    1   -1    1   -1
chi_4  1    1   -1   -1    1
chi_5  2   -2    0    0    0

Degrees: [1, 1, 1, 1, 2]  (same degree pattern as Q_8!)
-/

def d4Degrees : List Nat := [1, 1, 1, 1, 2]
def d4Order : Nat := 8

def checkD4Degrees : Bool :=
  let degSq := d4Degrees.foldl (fun acc d => acc + d * d) 0
  degSq == d4Order

#eval "D_4 character table: 5 irr chars, degrees [1,1,1,1,2]"
#eval checkD4Degrees
#eval "Q_8 and D_4 have the same character degree pattern but different tables"

/-! ## #eval summary -/
#eval "=== Small Groups Character Tables ==="
#eval "S_3: deg [1,1,2], sum=6 ✅"
#eval "S_4: deg [1,1,2,3,3], sum=24 ✅"
#eval "A_4: deg [1,1,1,3], sum=12 ✅"
#eval "A_5: deg [1,3,3,4,5], sum=60 ✅"
#eval "Q_8: deg [1,1,1,1,2], sum=8 ✅"
#eval "D_4: deg [1,1,1,1,2], sum=8 ✅"

end MiniCharacterTheory
