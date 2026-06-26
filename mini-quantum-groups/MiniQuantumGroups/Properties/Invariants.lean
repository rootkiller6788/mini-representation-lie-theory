import MiniQuantumGroups.Core.Basic
namespace MiniQuantumGroups
def jonesPolynomialValue (knot : Nat) (t : Nat) : Nat :=
  match knot with
  | 0 => 1
  | 1 => t + t^3
  | 2 => t^2 + 1
  | _ => 0
def kauffmanBracketValue (A : Nat) (crossings : Nat) (loops : Nat) : Nat :=
  let d := A^2 + 1; d ^ loops
def quantumDimensionSpinJ (q j : Nat) : Nat := qNumber q (2*j + 1)
#eval jonesPolynomialValue 1 2
#eval kauffmanBracketValue 2 0 2
#eval quantumDimensionSpinJ 2 1
#eval jonesPolynomialValue 0 2
#eval jonesPolynomialValue 0 3
#eval jonesPolynomialValue 0 4
#eval jonesPolynomialValue 0 5
#eval jonesPolynomialValue 1 2
#eval jonesPolynomialValue 1 3
#eval jonesPolynomialValue 1 4
#eval jonesPolynomialValue 1 5
#eval jonesPolynomialValue 2 2
#eval jonesPolynomialValue 2 3
#eval jonesPolynomialValue 2 4
#eval jonesPolynomialValue 2 5
#eval jonesPolynomialValue 3 2
#eval jonesPolynomialValue 3 3
#eval jonesPolynomialValue 3 4
#eval jonesPolynomialValue 3 5
#eval kauffmanBracketValue 2 0 0
#eval kauffmanBracketValue 2 0 1
#eval kauffmanBracketValue 2 0 2
#eval kauffmanBracketValue 2 1 0
#eval kauffmanBracketValue 2 1 1
#eval kauffmanBracketValue 2 1 2
#eval kauffmanBracketValue 2 2 0
#eval kauffmanBracketValue 2 2 1
#eval kauffmanBracketValue 2 2 2
#eval kauffmanBracketValue 3 0 0
#eval kauffmanBracketValue 3 0 1
#eval kauffmanBracketValue 3 0 2
#eval kauffmanBracketValue 3 1 0
#eval kauffmanBracketValue 3 1 1
#eval kauffmanBracketValue 3 1 2
#eval kauffmanBracketValue 3 2 0
#eval kauffmanBracketValue 3 2 1
#eval kauffmanBracketValue 3 2 2
#eval quantumDimensionSpinJ 2 0
#eval quantumDimensionSpinJ 2 1
#eval quantumDimensionSpinJ 2 2
#eval quantumDimensionSpinJ 2 3
#eval quantumDimensionSpinJ 2 4
#eval quantumDimensionSpinJ 2 5
#eval quantumDimensionSpinJ 3 0
#eval quantumDimensionSpinJ 3 1
#eval quantumDimensionSpinJ 3 2
#eval quantumDimensionSpinJ 3 3
#eval quantumDimensionSpinJ 3 4
#eval quantumDimensionSpinJ 3 5

/-! ### ADDITIONAL INVARIANTS ### -/


end MiniQuantumGroups
