import MiniQuantumGroups.Core.Basic
namespace MiniQuantumGroups
structure RepresentationData where
  dim : Nat
  e_mat : List (List Nat)
  f_mat : List (List Nat)
  k_mat : List (List Nat)
def spinHalfRep (q : Nat) : RepresentationData :=
  { dim := 2
    e_mat := [[0, 1], [0, 0]]
    f_mat := [[0, 0], [1, 0]]
    k_mat := [[q, 0], [0, 1]] }
def spinOneRep (q : Nat) : RepresentationData :=
  { dim := 3
    e_mat := [[0, qNumber q 2, 0], [0, 0, qNumber q 2], [0, 0, 0]]
    f_mat := [[0, 0, 0], [qNumber q 2, 0, 0], [0, qNumber q 2, 0]]
    k_mat := [[q^2, 0, 0], [0, 1, 0], [0, 0, 1]] }
def tensorDim (d1 d2 : Nat) : Nat := d1 * d2
def tensorProductDim (r1 r2 : RepresentationData) : Nat := r1.dim * r2.dim
inductive SLq2Generator : Type | A | B | C | D
  deriving BEq, Repr, Inhabited, DecidableEq
structure SLq2Monomial where
  a_pow : Nat
  b_pow : Nat
  c_pow : Nat
  d_pow : Nat
  deriving BEq, Repr, Inhabited
def SLq2_counit (g : SLq2Generator) : Nat :=
  match g with
  | .A => 1
  | .B => 0
  | .C => 0
  | .D => 1
def cgDecomp (j k : Nat) : List Nat :=
  let min_val := if j ≥ k then j - k else k - j
  (List.range (j + k + 1 - min_val)).map (λ l => min_val + l)
#eval cgDecomp 1 1
#eval cgDecomp 2 1
#eval (spinHalfRep 2).dim
#eval SLq2_counit .A
#eval tensorDim 2 3
end MiniQuantumGroups
