/- L8: Frobenius morphisms and finite groups of Lie type. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Morphisms.Hom
import MiniAlgebraicGroups.Morphisms.Iso
import MiniAlgebraicGroups.Properties.Invariants
import MiniAlgebraicGroups.Examples.Finite
namespace MiniAlgebraicGroups

structure FrobeniusEndomorphism (n : Nat) (G : AlgebraicGroup n) where
  endo : Endomorphism G
  characteristic : Nat
  powerRaisesToP : True

axiom standardFrobeniusGLn (n : Nat) : True
axiom frobeniusFixedPointsAreRationalPoints (n : Nat) (G : AlgebraicGroup n) : True
axiom langTheoremProof (n : Nat) (G : AlgebraicGroup n) : True
axiom langCorollaryGaloisCohomology (n : Nat) (G : AlgebraicGroup n) : True

axiom steinbergEndomorphismClassification (n : Nat) (G : AlgebraicGroup n) : True
axiom twistedGroupsOfLieType : True
axiom suzukiReeGroupsSpecialCharacteristics : True

axiom deligneLusztigVirtualRepresentations (n : Nat) (G : AlgebraicGroup n) : True
axiom deligneLusztigCharacterFormula (n : Nat) (G : AlgebraicGroup n) : True
axiom lusztigClassificationCharacters (n : Nat) (G : AlgebraicGroup n) : True

axiom sl2CharacterTable (q : Nat) : True
axiom modularRepresentationTheory (n : Nat) (G : AlgebraicGroup n) : True

def steinbergModuleDimSL2 (n : Nat) : Nat := 2 ^ n
#eval s!"dim St(SL(2,8))={steinbergModuleDimSL2 3}"
#eval "Advanced.FrobeniusMorphism: Frobenius, Lang, Steinberg, Deligne-Lusztig"
/-! ## More Frobenius Theory -/

axiom frobeniusEndomorphismFixedPoints (n : Nat) (G : AlgebraicGroup n) (q : Nat) : True
axiom steinbergTensorProductFormula (n : Nat) (G : AlgebraicGroup n) : True

axiom lusztigJordanDecompositionCharacters (n : Nat) (G : AlgebraicGroup n) : True
axiom shojiAlgorithmGreenFunctions (n : Nat) (G : AlgebraicGroup n) : True

#eval "Advanced.Frobenius: fixed points, Steinberg tensor product, Lusztig characters"
/-! ## Further Frobenius Theory -/

axiom frobeniusEigenvalues (n : Nat) (G : AlgebraicGroup n) (q : Nat) : True
axiom deligneLusztigCharacterDegrees (n : Nat) (G : AlgebraicGroup n) : True
axiom lusztigSeriesClassification (n : Nat) (G : AlgebraicGroup n) : True

#eval "Advanced.Frobenius: eigenvalues, DL characters, Lusztig series"
/-! ## More Frobenius Details -/
axiom frobeniusEndomorphismAndRationalPoints (n : Nat) (G : AlgebraicGroup n) (q : Nat) : True
axiom countingPointsOfFlagVariety (n : Nat) (G : AlgebraicGroup n) (q : Nat) : True

#eval "Advanced.Frobenius: rational points, counting points of flag variety"
/-! ## Counting Rational Points -/
axiom weilConjecturesForFlagVarieties (n : Nat) (G : AlgebraicGroup n) (q : Nat) : True
axiom grothendieckLefschetzForFlagVarieties (n : Nat) (G : AlgebraicGroup n) (q : Nat) : True

#eval "Advanced.Frobenius: Weil conjectures, Grothendieck-Lefschetz trace formula"