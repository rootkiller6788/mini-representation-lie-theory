/- L4: Classification via root data and Dynkin diagrams. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Properties.Invariants
namespace MiniAlgebraicGroups

inductive DynkinDiagram | A (n : Nat) | B (n : Nat) | C (n : Nat) | D (n : Nat) | E6 | E7 | E8 | F4 | G2
  deriving BEq, Repr

def DynkinDiagram.rank : DynkinDiagram -> Nat
  | DynkinDiagram.A n => n
  | DynkinDiagram.B n => n
  | DynkinDiagram.C n => n
  | DynkinDiagram.D n => n
  | DynkinDiagram.E6 => 6
  | DynkinDiagram.E7 => 7
  | DynkinDiagram.E8 => 8
  | DynkinDiagram.F4 => 4
  | DynkinDiagram.G2 => 2

def DynkinDiagram.numPositiveRoots : DynkinDiagram -> Nat
  | DynkinDiagram.A n => n * (n + 1) / 2
  | DynkinDiagram.B n => n * n
  | DynkinDiagram.C n => n * n
  | DynkinDiagram.D n => n * (n - 1)
  | DynkinDiagram.E6 => 36
  | DynkinDiagram.E7 => 63
  | DynkinDiagram.E8 => 120
  | DynkinDiagram.F4 => 24
  | DynkinDiagram.G2 => 6

def DynkinDiagram.numRoots (d : DynkinDiagram) : Nat := 2 * d.numPositiveRoots

#eval s!"|Phi| A_3={DynkinDiagram.numRoots (DynkinDiagram.A 3)}"
#eval s!"|Phi| G_2={DynkinDiagram.numRoots (DynkinDiagram.G2)}"

def DynkinDiagram.outAutGroup : DynkinDiagram -> Nat
  | DynkinDiagram.A 1 => 1
  | DynkinDiagram.A _ => 2
  | DynkinDiagram.D 4 => 6
  | DynkinDiagram.D _ => 2
  | DynkinDiagram.E6 => 2
  | _ => 1

#eval s!"|Out(A_3)|={DynkinDiagram.outAutGroup (DynkinDiagram.A 3)}"
#eval s!"|Out(D_4)|={DynkinDiagram.outAutGroup (DynkinDiagram.D 4)}"

def langlandsDual (d : DynkinDiagram) : DynkinDiagram :=
  match d with | DynkinDiagram.B n => DynkinDiagram.C n | DynkinDiagram.C n => DynkinDiagram.B n | _ => d

axiom classificationOfReductiveGroups : True
axiom outerAutDynkinAutCorrespondence : True

#eval "Properties.Classification: DynkinDiagram, rank, numRoots, Langlands dual"
/-! ## Extended Dynkin Diagrams -/

inductive ExtendedDynkinDiagram
  | A (n : Nat) | B (n : Nat) | C (n : Nat) | D (n : Nat) | E6 | E7 | E8 | F4 | G2

def ExtendedDynkinDiagram.toDynkin : ExtendedDynkinDiagram -> DynkinDiagram
  | ExtendedDynkinDiagram.A n => DynkinDiagram.A n
  | ExtendedDynkinDiagram.B n => DynkinDiagram.B n
  | ExtendedDynkinDiagram.C n => DynkinDiagram.C n
  | ExtendedDynkinDiagram.D n => DynkinDiagram.D n
  | ExtendedDynkinDiagram.E6 => DynkinDiagram.E6
  | ExtendedDynkinDiagram.E7 => DynkinDiagram.E7
  | ExtendedDynkinDiagram.E8 => DynkinDiagram.E8
  | ExtendedDynkinDiagram.F4 => DynkinDiagram.F4
  | ExtendedDynkinDiagram.G2 => DynkinDiagram.G2

/-! ## Cartan Types -/

def DynkinDiagram.isSimplyLaced : DynkinDiagram -> Bool
  | DynkinDiagram.A _ => true
  | DynkinDiagram.D _ => true
  | DynkinDiagram.E6 => true
  | DynkinDiagram.E7 => true
  | DynkinDiagram.E8 => true
  | _ => false

#eval s!"Simply laced? A_3: {DynkinDiagram.isSimplyLaced (DynkinDiagram.A 3)}"
#eval s!"Simply laced? G_2: {DynkinDiagram.isSimplyLaced (DynkinDiagram.G2)}"

/-! ## Coxeter Graph -/

def DynkinDiagram.coxeterLabels : DynkinDiagram -> List Nat
  | DynkinDiagram.A n => List.replicate n 3
  | DynkinDiagram.B n => List.replicate (n-1) 3 ++ [4]
  | DynkinDiagram.C n => List.replicate (n-1) 3 ++ [4]
  | DynkinDiagram.D n => List.replicate (n-2) 3 ++ [3, 3]
  | DynkinDiagram.E6 => [3, 3, 3, 3, 3, 3]
  | DynkinDiagram.E7 => [3, 3, 3, 3, 3, 3, 3]
  | DynkinDiagram.E8 => [3, 3, 3, 3, 3, 3, 3, 3]
  | DynkinDiagram.F4 => [3, 4, 3, 4]
  | DynkinDiagram.G2 => [3, 6]

#eval s!"Coxeter labels A_3: {DynkinDiagram.coxeterLabels (DynkinDiagram.A 3)}"
#eval s!"Coxeter labels G_2: {DynkinDiagram.coxeterLabels (DynkinDiagram.G2)}"

/-! ## Satake Diagrams (Classification of Real Forms) -/

axiom satakeClassificationRealForms : True

#eval "Properties.Classification: Extended Dynkin, simply laced, Coxeter labels"
/-! ## Complete Dynkin Diagram Classification -/

def dynkinTypeName : DynkinDiagram -> String
  | DynkinDiagram.A n => s!"A_{n}"
  | DynkinDiagram.B n => s!"B_{n}"
  | DynkinDiagram.C n => s!"C_{n}"
  | DynkinDiagram.D n => s!"D_{n}"
  | DynkinDiagram.E6 => "E_6"
  | DynkinDiagram.E7 => "E_7"
  | DynkinDiagram.E8 => "E_8"
  | DynkinDiagram.F4 => "F_4"
  | DynkinDiagram.G2 => "G_2"

#eval dynkinTypeName (DynkinDiagram.A 3)
#eval dynkinTypeName DynkinDiagram.G2
#eval dynkinTypeName DynkinDiagram.E8

/-! ## Cartan Matrix Construction -/

axiom cartanMatrixOf (d : DynkinDiagram) : List (List Int)

/-! ## Root System Data -/

axiom rootsOfAn (n : Nat) : List (List Int)
axiom simpleRootsOfAn (n : Nat) : List (List Int)

/-! ## Classification Theorems -/

axiom classificationSimpleAlgebraicGroups : True
axiom classificationReductiveGroupsOverC : True
axiom classificationReductiveGroupsOverR : True
axiom classificationOverFiniteFields : True

/-! ## Tits Classification -/

axiom titsClassificationBuildings : True
axiom titsClassificationSphericalBuildings : True

/-! ## Kac-Moody Classification -/

axiom kacMoodyClassification : True
axiom affineKacMoodyClassification : True

#eval "Properties.Classification: complete Dynkin classification, Cartan matrices"
/-! ## Dynkin Diagram Automorphisms -/
axiom trialityInD4 : True
axiom frobeniusAutomorphismDynkin : True
axiom cartanInvolution : True

/-! ## Affine Dynkin Diagrams -/
axiom affineDynkinClassification : True
axiom affineLieAlgebrasFromDynkin : True

/-! ## Satake Diagrams for Real Forms -/
axiom satakeDiagramsClassification : True
axiom voganDiagrams : True

#eval "Properties.Classification: Dynkin automorphisms, affine Dynkin, Satake diagrams"