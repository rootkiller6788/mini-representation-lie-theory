import MiniQuantumGroups.Core.Basic
namespace MiniQuantumGroups
def checkRMatrixEntry (q i j : Nat) : Nat :=
  match RMatrix2d_pattern q |>.get? i with
  | some row => match row.get? j with
    | some (num, den) => num / den
    | none => 0
  | none => 0
#eval checkRMatrixEntry 2 0 0
#eval checkRMatrixEntry 2 3 3
def jonesUnknot (_t : Nat) : Nat := 1
def jonesTrefoilRight (t : Nat) : Nat := t + t^3
def jonesFigure8 (t : Nat) : Nat := t^2 + 1
#eval jonesUnknot 2
#eval jonesTrefoilRight 2
def kauffmanBracketUnknot (A : Nat) : Nat := A^2 + 1
#eval kauffmanBracketUnknot 2
def pbwBasisElements (maxExp : Nat) : List Uqsl2Monomial :=
  (List.range (maxExp+1)).bind (λ i =>
    (List.range (maxExp+1)).bind (λ m =>
      (List.range (maxExp+1)).map (λ n => ⟨true, i, m, n⟩)))
#eval (pbwBasisElements 2).length
#eval jonesTrefoilRight 2
#eval jonesTrefoilRight 3
#eval jonesTrefoilRight 4
#eval jonesTrefoilRight 5
#eval jonesTrefoilRight 6
#eval jonesTrefoilRight 7
#eval jonesTrefoilRight 8
#eval jonesTrefoilRight 9
#eval jonesTrefoilRight 10
#eval jonesFigure8 2
#eval jonesFigure8 3
#eval jonesFigure8 4
#eval jonesFigure8 5
#eval jonesFigure8 6
#eval jonesFigure8 7
#eval jonesFigure8 8
#eval jonesFigure8 9
#eval jonesFigure8 10
#eval kauffmanBracketUnknot 2
#eval kauffmanBracketUnknot 3
#eval kauffmanBracketUnknot 4
#eval kauffmanBracketUnknot 5
#eval kauffmanBracketUnknot 6
#eval kauffmanBracketUnknot 7
#eval (pbwBasisElements 1).length
#eval (pbwBasisElements 2).length
#eval (pbwBasisElements 3).length
#eval (pbwBasisElements 4).length
#eval (pbwBasisElements 5).length
#eval (pbwBasisElements 6).length

/-! ### EXTENDED VERIFICATIONS ### -/


end MiniQuantumGroups
