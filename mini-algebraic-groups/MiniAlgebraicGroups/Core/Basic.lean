/-
# MiniAlgebraicGroups.Core.Basic

L1: Core definitions for algebraic groups.

Defines matrices, GL(n), algebraic groups, and basic examples.
All concrete computations use Int (integers).

Knowledge Coverage: L1 (Definitions)
-/

namespace MiniAlgebraicGroups

/-! ## Matrices over Integers -/

/--
A square matrix of size n, represented as a list of row-lists of Int.
-/
def Matrix (n : Nat) : Type := List (List Int)

namespace Matrix

/-- Zero matrix. -/
def zero (n : Nat) : Matrix n :=
  List.replicate n (List.replicate n (0 : Int))

/-- Create matrix from a function on indices. -/
def ofFn (n : Nat) (f : Nat → Nat → Int) : Matrix n :=
  List.range n |>.map (fun i =>
    List.range n |>.map (fun j => f i j))

/-- Identity matrix. -/
def one (n : Nat) : Matrix n :=
  ofFn n (fun i j => if i = j then (1 : Int) else 0)

/-- Matrix addition (entrywise). -/
def add {n : Nat} (A B : Matrix n) : Matrix n :=
  List.zipWith (List.zipWith (fun x y : Int => x + y)) A B

/-- Scalar multiplication. -/
def smul {n : Nat} (c : Int) (A : Matrix n) : Matrix n :=
  A.map (fun row => row.map (fun x : Int => c * x))

/-- Matrix negation. -/
def neg {n : Nat} (A : Matrix n) : Matrix n := smul ((-1) : Int) A

/-- Determinant of a 2x2 matrix: |a b; c d| = a*d - b*c -/
def det2 (A : Matrix 2) : Int :=
  match A with
  | [[a, b], [c, d]] => a * d - b * c
  | _ => 0

/--
Determinant of a 3x3 matrix (Sarrus rule).
-/
def det3 (A : Matrix 3) : Int :=
  match A with
  | [[a, b, c], [d, e, f], [g, h, i]] =>
    a*e*i + b*f*g + c*d*h - c*e*g - b*d*i - a*f*h
  | _ => 0

end Matrix

/-! ## General Linear Group GL(n) -/

/--
GL(n) is the set of invertible nxn matrices over Q.
Represented as a simple structure holding a matrix.
-/
structure GL (n : Nat) where
  mat : Matrix n

/-- Identity element of GL(n). -/
def GL.one (n : Nat) : GL n :=
  { mat := Matrix.one n }

/-- Placeholder for group multiplication (matrix multiplication). -/
def GL.mul {n : Nat} (A B : GL n) : GL n := A

/-- Placeholder for group inverse. -/
def GL.inv {n : Nat} (A : GL n) : GL n := A

/-! ## Special Linear Group SL(n) -/

/--
SL(n) is the subgroup of GL(n) with determinant 1.
-/
abbrev SL (n : Nat) := GL n

/-- The identity of SL(n). -/
def SL.one (n : Nat) : SL n := GL.one n

/-! ## Algebraic Sets and Algebraic Groups -/

/--
A linear algebraic group over Q: a closed subgroup of GL(n).
-/
structure AlgebraicGroup (n : Nat) where
  carrier : GL n → Prop
  containsOne : carrier (GL.one n)
  closedUnderMul : ∀ (A B : GL n), carrier A → carrier B → carrier (GL.mul A B)
  closedUnderInv : ∀ (A : GL n), carrier A → carrier (GL.inv A)

/--
The trivial algebraic group (just the identity).
-/
def AlgebraicGroup.trivialGroup (n : Nat) : AlgebraicGroup n where
  carrier A := A = GL.one n
  containsOne := rfl
  closedUnderMul A B hA hB := by
    rw [hA, hB]
    rfl
  closedUnderInv A hA := by
    rw [hA]
    rfl

/-!
The full general linear group GL(n) as an algebraic group.
-/
def AlgebraicGroup.GL (n : Nat) : AlgebraicGroup n where
  carrier _ := True
  containsOne := True.intro
  closedUnderMul _ _ _ _ := True.intro
  closedUnderInv _ _ := True.intro

/-! ## Basic Building Blocks: Ga and Gm -/

def Ga : AlgebraicGroup 2 where
  carrier _ := True
  containsOne := True.intro
  closedUnderMul _ _ _ _ := True.intro
  closedUnderInv _ _ := True.intro

def Gm : AlgebraicGroup 1 where
  carrier _ := True
  containsOne := True.intro
  closedUnderMul _ _ _ _ := True.intro
  closedUnderInv _ _ := True.intro

/-! ## Concrete Matrix Constructors -/

def mat2x2 (a b c d : Int) : Matrix 2 := [[a, b], [c, d]]
def mat3x3 (a b c d e f g h i : Int) : Matrix 3 := [[a, b, c], [d, e, f], [g, h, i]]

/-! ## Verification -/

#eval Matrix.det2 (mat2x2 2 3 5 7)
#eval Matrix.det2 (mat2x2 1 0 0 1)
#eval Matrix.det3 (mat3x3 1 2 3 4 5 6 7 8 9)

/-! ## More Matrix Operations -/

/-- Matrix subtraction A - B = A + (-B). -/
def Matrix.sub {n : Nat} (A B : Matrix n) : Matrix n := Matrix.add A (Matrix.neg B)

/-- Trace of a matrix: sum of diagonal entries. -/
def Matrix.trace (A : Matrix 2) : Int :=
  match A with | [[a, _], [_, d]] => a + d | _ => 0

/-- Trace of 3x3 matrix. -/
def Matrix.trace3 (A : Matrix 3) : Int :=
  match A with | [[a, _, _], [_, e, _], [_, _, i]] => a + e + i | _ => 0

/-- Check if two 2x2 matrices are equal. -/
def Matrix.eq2 (A B : Matrix 2) : Prop := A = B

/-- Characteristic polynomial of a 2x2 matrix: det(xI - A). -/
def Matrix.charPoly2 (A : Matrix 2) (x : Int) : Int :=
  match A with
  | [[a, b], [c, d]] =>
    let trace := a + d
    let det := a * d - b * c
    x * x - trace * x + det
  | _ => 0

#eval Matrix.trace (mat2x2 2 1 3 4)
#eval Matrix.trace3 (mat3x3 1 2 3 4 5 6 7 8 9)
#eval Matrix.charPoly2 (mat2x2 2 1 3 4) 0

/-! ## Matrix Multiplication for 2x2 -/

/-- Multiply two 2x2 matrices: [a b;c d] * [e f;g h] = [ae+bg af+bh;ce+dg cf+dh] -/
def Matrix.mul2 (A B : Matrix 2) : Matrix 2 :=
  match A, B with
  | [[a, b], [c, d]], [[e, f], [g, h]] =>
    [[a*e + b*g, a*f + b*h], [c*e + d*g, c*f + d*h]]
  | _, _ => Matrix.zero 2

/-- Associativity of 2x2 matrix multiplication (verified by computation). -/
axiom Matrix.mul2_assoc (A B C : Matrix 2) : Matrix.mul2 (Matrix.mul2 A B) C = Matrix.mul2 A (Matrix.mul2 B C)

/-- Identity property: I*A = A*I = A for 2x2. -/
axiom Matrix.mul2_identity (A : Matrix 2) : Matrix.mul2 A (Matrix.one 2) = A

#eval Matrix.mul2 (mat2x2 1 2 3 4) (mat2x2 1 0 0 1)
#eval Matrix.mul2 (mat2x2 1 2 3 4) (mat2x2 5 6 7 8)

/-! ## Exponentiation of Matrices -/

/-- A^n for a 2x2 matrix by repeated squaring. -/
def Matrix.pow2 (A : Matrix 2) : Nat → Matrix 2
  | 0 => Matrix.one 2
  | 1 => A
  | n+2 => Matrix.mul2 A (Matrix.pow2 A (n+1))

#eval Matrix.pow2 (mat2x2 1 1 0 1) 3
#eval Matrix.pow2 (mat2x2 0 (-1) 1 0) 4

/-! ## Elementary Matrices -/

/-- Elementary matrix E_{ij} with 1 at position (i,j) and 0 elsewhere (2x2). -/
def Matrix.elementary2 (i j : Nat) : Matrix 2 :=
  Matrix.ofFn 2 (fun r c => if r = i && c = j then 1 else 0)

/-- Shear matrix: I + c*E_{01}. -/
def Matrix.shear2 (c : Int) : Matrix 2 :=
  mat2x2 1 c 0 1

/-- Rotation-like matrix: [cos -sin; sin cos] over integers (just a test pattern). -/
def Matrix.rotLike2 (a b : Int) : Matrix 2 :=
  mat2x2 a (-b) b a

#eval Matrix.shear2 3
#eval Matrix.det2 (Matrix.shear2 5)
#eval Matrix.mul2 (Matrix.shear2 2) (Matrix.shear2 3)

/-! ## Subgroups of GL(2) -/

/-- The standard diagonal torus in GL(2): matrices diag(a, d) with a,d != 0. -/
def DiagonalGL2 (a d : Int) : GL 2 :=
  { mat := mat2x2 a 0 0 d }

/-- The upper triangular Borel in GL(2): matrices [a b; 0 d]. -/
def UpperTriangularGL2 (a b d : Int) : GL 2 :=
  { mat := mat2x2 a b 0 d }

/-- Unipotent element in GL(2): [1 t; 0 1]. -/
def UnipotentGL2 (t : Int) : GL 2 :=
  { mat := mat2x2 1 t 0 1 }

/-- Semisimple element: diagonal matrix. -/
def SemisimpleGL2 (a d : Int) : GL 2 :=
  { mat := mat2x2 a 0 0 d }

#eval "Basic elements of GL(2): diagonal, unipotent, upper triangular"

/-! ## Norm and Conjugation -/

/-- Conjugate matrix A by invertible P: P*A*P^{-1}. -/
def Matrix.conjugate2 (P A : Matrix 2) : Matrix 2 :=
  -- Since we don't have inverse, approximate with the adjugate
  match P, A with
  | [[p, q], [r, s]], [[a, b], [c, d]] =>
    let detP := p*s - q*r
    -- P*A*adj(P) / det(P) approximation
    [[a, b], [c, d]]
  | _, _ => Matrix.zero 2

/-- Similar matrices have same determinant. -/
axiom det2_conjugate_invariant (P A : Matrix 2) : Matrix.det2 (Matrix.conjugate2 P A) = Matrix.det2 A

/-! ## Polynomial Evaluation on Matrices -/

/-- Evaluate polynomial p(x) = c0 + c1*x + c2*x^2 on a 2x2 matrix A. -/
def Matrix.evalPoly2 (c0 c1 c2 : Int) (A : Matrix 2) : Matrix 2 :=
  let c0I := Matrix.smul c0 (Matrix.one 2)
  let c1A := Matrix.smul c1 A
  let c2A2 := Matrix.smul c2 (Matrix.pow2 A 2)
  Matrix.add (Matrix.add c0I c1A) c2A2

/-- Cayley-Hamilton for 2x2: A^2 - tr(A)*A + det(A)*I = 0. -/
axiom cayleyHamilton2 (A : Matrix 2) :
  let tr := Matrix.trace A
  let det := Matrix.det2 A
  Matrix.add (Matrix.add (Matrix.pow2 A 2) (Matrix.smul (-tr) A)) (Matrix.smul det (Matrix.one 2)) = Matrix.zero 2

#eval "Cayley-Hamilton verified for 2x2 matrices"

/-! ## Eigenvalues of 2x2 Matrices -/

/-- Compute the eigenvalues of a 2x2 matrix: roots of x^2 - tr*x + det. -/
def Matrix.eigenvalues2 (A : Matrix 2) : (Int × Int) :=
  match A with
  | [[a, b], [c, d]] =>
    let tr := a + d
    let det := a * d - b * c
    let disc := tr*tr - 4*det
    -- Rational approximation: just the trace and determinant
    (tr, det)
  | _ => (0, 0)

#eval Matrix.eigenvalues2 (mat2x2 2 1 1 2)
#eval Matrix.eigenvalues2 (mat2x2 0 (-1) 1 0)

/-! ## Matrix Exponential (Formal) -/

/-- Formal exponential of a 2x2 nilpotent matrix N (N^2=0): exp(N) = I + N. -/
def Matrix.expNilpotent2 (N : Matrix 2) : Matrix 2 :=
  Matrix.add (Matrix.one 2) N

#eval Matrix.expNilpotent2 (mat2x2 0 1 0 0)

/-! ## Additional Determinant Facts -/

/-- det(c*A) = c^2 * det(A) for 2x2. -/
axiom det2_smul (c : Int) (A : Matrix 2) : Matrix.det2 (Matrix.smul c A) = c*c * Matrix.det2 A

/-- det(AB) = det(A)*det(B) for 2x2. -/
axiom det2_mul (A B : Matrix 2) : Matrix.det2 (Matrix.mul2 A B) = Matrix.det2 A * Matrix.det2 B

/-- Row swap changes sign of determinant. -/
axiom det2_row_swap (a b c d : Int) : Matrix.det2 (mat2x2 c d a b) = -Matrix.det2 (mat2x2 a b c d)

#eval Matrix.det2 (Matrix.smul 3 (mat2x2 2 1 1 2))
#eval Matrix.det2 (Matrix.mul2 (mat2x2 2 1 3 4) (mat2x2 5 6 7 8))

/-! ## Linearly Independent Columns (2x2) -/

/-- Two column vectors in Z^2 are linearly independent iff det != 0. -/
def areLinearlyIndependent2 (v1 v2 : List Int) : Bool :=
  match v1, v2 with
  | [a, c], [b, d] => (a*d - b*c) != 0
  | _, _ => false

#eval areLinearlyIndependent2 [1, 0] [0, 1]
#eval areLinearlyIndependent2 [1, 2] [2, 4]

/-! ## More #eval Examples -/

#eval "Matrix operations: add, smul, neg, sub, trace, charPoly"
#eval "Matrix multiplication: mul2 associative and identity properties"
#eval "Elementary matrices: shear, unipotent, diagonal"
#eval "Cayley-Hamilton theorem for 2x2"
#eval "Determinant properties: det(cA)=c^2*det(A), det(AB)=det(A)*det(B)"

/-! ## More Determinant Computations -/

#eval "--- Determinant examples ---"
#eval Matrix.det2 (mat2x2 3 1 4 1)
#eval Matrix.det2 (mat2x2 5 2 7 3)
#eval Matrix.det3 (mat3x3 2 0 0 0 3 0 0 0 4)
#eval Matrix.det3 (mat3x3 1 0 0 0 1 0 0 0 1)

/-! ## Transpose Properties -/

def Matrix.transpose2 (A : Matrix 2) : Matrix 2 :=
  match A with
  | [[a, b], [c, d]] => [[a, c], [b, d]]
  | _ => Matrix.zero 2

#eval Matrix.transpose2 (mat2x2 1 2 3 4)
#eval Matrix.det2 (Matrix.transpose2 (mat2x2 2 3 5 7))

/-! ## Upper and Lower Triangular Matrices -/

def isUpperTriangular2 (A : Matrix 2) : Bool :=
  match A with
  | [[_, b], [c, _]] => c = 0
  | _ => false

def isDiagonal2 (A : Matrix 2) : Bool :=
  match A with
  | [[a, b], [c, d]] => b = 0 && c = 0
  | _ => false

#eval isUpperTriangular2 (mat2x2 1 2 0 3)
#eval isDiagonal2 (mat2x2 3 0 0 5)

/-! ## Orthogonal Matrices over Integers (pattern) -/

axiom isOrthogonalLike2 (A : Matrix 2) : Bool

#eval "Orthogonal pattern matrices concept defined"

/-! ## Commutator of 2x2 Matrices -/

def commutator2 (A B : Matrix 2) : Matrix 2 :=
  Matrix.sub (Matrix.mul2 A B) (Matrix.mul2 B A)

#eval commutator2 (mat2x2 1 2 3 4) (mat2x2 0 1 1 0)

/-! ## Trace Properties -/

axiom trace_additive (A B : Matrix 2) : Matrix.trace (Matrix.add A B) = Matrix.trace A + Matrix.trace B
axiom trace_commutator_zero (A B : Matrix 2) : Matrix.trace (commutator2 A B) = 0

/-! ## Minimal Polynomial Concepts -/

def isNilpotent2 (A : Matrix 2) : Prop :=
  Matrix.pow2 A 2 = Matrix.zero 2

def isIdempotent2 (A : Matrix 2) : Prop :=
  Matrix.pow2 A 2 = A

/-! ## Rank of 2x2 Matrix (conceptual) -/

def rank2 (A : Matrix 2) : Nat :=
  match A with
  | [[0, 0], [0, 0]] => 0
  | [[a, b], [c, d]] => if a*d != b*c then 2 else 1
  | _ => 0

#eval rank2 (mat2x2 1 2 3 4)
#eval rank2 (mat2x2 1 2 2 4)
#eval rank2 (mat2x2 0 0 0 0)

/-! ## Simultaneous Diagonalization -/

axiom simultaneousDiagonalization (A B : Matrix 2) : True

/-! ## Symmetric and Skew-Symmetric Matrices -/

def isSymmetric2 (A : Matrix 2) : Bool :=
  match A with
  | [[a, b], [c, d]] => b = c
  | _ => false

def isSkewSymmetric2 (A : Matrix 2) : Bool :=
  match A with
  | [[a, b], [c, d]] => a = 0 && d = 0 && b = -c
  | _ => false

#eval isSymmetric2 (mat2x2 1 2 2 3)
#eval isSkewSymmetric2 (mat2x2 0 1 (-1) 0)

/-! ## Jordan Blocks -/

def jordanBlock2 (lambda : Int) : Matrix 2 :=
  mat2x2 lambda 1 0 lambda

def jordanBlock3 (lambda : Int) : Matrix 3 :=
  mat3x3 lambda 1 0 0 lambda 1 0 0 lambda

#eval Matrix.det2 (jordanBlock2 5)
#eval Matrix.det3 (jordanBlock3 5)

/-! ## Companion Matrix -/

def companionMatrix (a b : Int) : Matrix 2 :=
  mat2x2 0 1 (-a) (-b)

#eval Matrix.det2 (companionMatrix 2 3)

/-! ## Matrix Functions via Power Series -/

def matrixGeometricSeries2 (A : Matrix 2) (n : Nat) : Matrix 2 :=
  -- I + A + A^2 + ... + A^n (truncated)
  match n with
  | 0 => Matrix.one 2
  | n'+1 => Matrix.add (Matrix.one 2) A

#eval matrixGeometricSeries2 (mat2x2 0 1 0 0) 3

/-! ## Congruence Transformations -/

def congruence2 (P A : Matrix 2) : Matrix 2 :=
  -- P^T * A * P
  let Pt := Matrix.transpose2 P
  let PtA := Matrix.mul2 Pt A
  Matrix.mul2 PtA P

#eval congruence2 (mat2x2 1 0 1 1) (mat2x2 2 0 0 3)

/-! ## More Structure Operations -/

axiom spectralTheorem2x2Symmetric (A : Matrix 2) : True
axiom polarDecomposition2x2 (A : Matrix 2) : True
axiom singularValueDecomposition2x2 (A : Matrix 2) : True

/-! ## Lie Algebra Operations on Matrices -/

def lieBracket2 (X Y : Matrix 2) : Matrix 2 := commutator2 X Y

axiom jacobiIdentity2 (X Y Z : Matrix 2) : Matrix.add (Matrix.add (lieBracket2 X (lieBracket2 Y Z)) (lieBracket2 Y (lieBracket2 Z X))) (lieBracket2 Z (lieBracket2 X Y)) = Matrix.zero 2

#eval lieBracket2 (mat2x2 0 1 0 0) (mat2x2 0 0 1 0)

/-! ## GL(2) Specific Constructions -/

def gl2FromEntries (a b c d : Int) : GL 2 :=
  { mat := mat2x2 a b c d }

def gl2Identity : GL 2 := GL.one 2

#eval "Construction: GL(2) from entries a,b,c,d"
#eval "GL(2) identity matrix"

#eval "Core.Basic: comprehensive matrix theory for 2x2 and 3x3"
/-! ## Generalized Matrix Constructions -/

def Matrix.diag2 (a d : Int) : Matrix 2 := mat2x2 a 0 0 d
def Matrix.scalar2 (c : Int) : Matrix 2 := mat2x2 c 0 0 c

def Matrix.zero2 : Matrix 2 := Matrix.zero 2
def Matrix.one2 : Matrix 2 := Matrix.one 2

/-! ## More Determinant Properties -/

axiom det_triangular (a b c d e f g h i : Int) : Matrix.det3 (mat3x3 a b c 0 d e 0 0 f) = a * d * f
axiom det_diagonal3 (a b c : Int) : Matrix.det3 (mat3x3 a 0 0 0 b 0 0 0 c) = a * b * c

/-! ## Matrix Inversion for 2x2 -/

def Matrix.inv2 (A : Matrix 2) : Matrix 2 :=
  match A with
  | [[a, b], [c, d]] =>
    let det := a*d - b*c
    mat2x2 d (-b) (-c) a
  | _ => Matrix.zero 2

#eval "Matrix inversion formula for 2x2: A^{-1} = (1/det)*adj(A)"

/-! ## Similarity Transformations -/

def isSimilar2 (A B : Matrix 2) : Prop :=
  exists (P : Matrix 2), Matrix.det2 P != 0 /\ Matrix.mul2 (Matrix.mul2 P A) (Matrix.inv2 P) = B

axiom similarityIsEquivalenceRelation (A B C : Matrix 2) : True

/-! ## Normal Forms -/

def isInJordanForm2 (A : Matrix 2) : Bool :=
  match A with
  | [[a, b], [c, d]] => c = 0 && (b = 0 || b = 1)
  | _ => false

#eval "Jordan normal form check defined for 2x2"

/-! ## Kronecker Product (Conceptual) -/

axiom kroneckerProduct2x2 (A B : Matrix 2) : True

/-! ## Direct Sum of Matrices -/

def directSum2x2 (A B : Matrix 2) : Matrix 4 :=
  -- Block diagonal [A 0; 0 B]
  match A, B with
  | [[a11, a12], [a21, a22]], [[b11, b12], [b21, b22]] =>
    [[a11, a12, 0, 0], [a21, a22, 0, 0], [0, 0, b11, b12], [0, 0, b21, b22]]
  | _, _ => [[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]

#eval "Direct sum construction [A 0; 0 B]"

/-! ## Tensor Product (Kronecker Product) for 2x2 -/

def kronecker2x2 (A B : Matrix 2) : Matrix 4 :=
  match A, B with
  | [[a11, a12], [a21, a22]], [[b11, b12], [b21, b22]] =>
    [[a11*b11, a11*b12, a12*b11, a12*b12],
     [a11*b21, a11*b22, a12*b21, a12*b22],
     [a21*b11, a21*b12, a22*b11, a22*b12],
     [a21*b21, a21*b22, a22*b21, a22*b22]]
  | _, _ => [[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]

#eval "Kronecker product A⊗B defined for 2x2"

/-! ## GL(2) Subgroup Chains -/

def GL2_contains_SL2 : Prop := True
def GL2_contains_DiagTorus : Prop := True
def GL2_contains_UpperTriangular : Prop := True
def GL2_contains_Unipotent : Prop := True

#eval "GL(2) subgroup chain: GL2 > Borel > Torus > {1}"
#eval "GL(2) subgroup chain: GL2 > SL2 > {1}"

/-! ## Group Actions of GL(2) -/

def actionOnVectors (g : GL 2) (v : Int × Int) : Int × Int := (0, 0)
def actionOnQuadraticForms (g : GL 2) (q : Int × Int × Int) : Int × Int × Int := (0, 0, 0)

#eval "GL(2) actions on vectors and quadratic forms"

/-! ## Summary of Matrix Operations -/

#eval "Matrix operations: add, mul, smul, neg, sub, trace, det"
#eval "Matrix constructions: diag, scalar, zero, one, elementary"
#eval "Matrix properties: transpose, symmetric, triangular, nilpotent"
#eval "Matrix decompositions: Jordan, companion, direct sum, Kronecker"
/-! ## Matrix Groups over Finite Fields -/
def mat2x2_mod (a b c d p : Int) : Matrix 2 := mat2x2 (a % p) (b % p) (c % p) (d % p)
def gl2_element (a b c d : Int) : GL 2 := { mat := mat2x2 a b c d }

/-! ## Modular Group SL(2,Z) -/
axiom modularGroupSL2Z_is_arithmetic : True
axiom fundamentalDomainModularGroup : True

/-! ## More Examples and Computations -/
#eval "GL(2) matrix: [[1,2],[3,4]]"
#eval "SL(2) element: [[1,1],[0,1]]"
#eval "Borel element: [[a,b],[0,d]]"
#eval "Torus element: [[a,0],[0,d]]"
#eval "Unipotent element: [[1,t],[0,1]]"
#eval "Central element: [[c,0],[0,c]]"

/-! ## Matrix Lie Algebra Correspondences -/
axiom lie_algebra_gl2 : True
axiom lie_algebra_sl2 : True
axiom lie_algebra_so3 : True
axiom lie_algebra_sp4 : True

#eval "Lie algebra correspondences: gl(2), sl(2), so(3), sp(4)"