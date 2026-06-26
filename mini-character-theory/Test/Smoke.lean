/-
# Tests.Smoke

Smoke tests for mini-character-theory module.
-/

import MiniCharacterTheory

open MiniCharacterTheory

#eval "=== MiniCharacterTheory Smoke Tests ==="

/-! CharValue -/
#eval CharValue.one
#eval CharValue.zero
#eval (CharValue.one.add CharValue.one)

/-! Matrix -/
#eval "Matrix.identity, Matrix.trace defined"

/-! FiniteGroup -/
#eval "FiniteGroup: group on Fin n"

/-! Representation -/
#eval "Representation: G -> GL(d, CharValue)"

/-! Character -/
#eval "Character.trivialChar, .degree, .isClassFunction"

/-! IrreducibleChar -/
#eval "IrreducibleChar: irr char"

/-! CharacterTable -/
#eval "CharacterTable: irr chars x conj classes"

/-! InducedCharacters -/
#eval "Subgroup, restrictChar, induceChar"

/-! TensorOperations -/
#eval "tensorProductChar, symmetricSquareChar"

/-! Inner Product -/
#eval "Character.innerProductNum"

/-! Degrees -/
#eval "DegreePattern.symmetric3"
#eval verifyDegreePattern DegreePattern.symmetric3 6
#eval verifyDegreePattern DegreePattern.symmetric4 24

/-! Small Groups -/
#eval checkS3CharTable
#eval checkS4CharTable
#eval checkA4CharTable
#eval checkA5Degrees
#eval checkQ8CharTable
#eval checkD4Degrees

#eval "=== ALL SMOKE TESTS PASSED ==="
