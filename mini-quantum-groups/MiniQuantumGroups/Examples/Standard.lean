import MiniQuantumGroups.Core.Basic
import MiniQuantumGroups.Core.Laws
namespace MiniQuantumGroups

#eval qNumber 2 1
#eval qNumber 2 2
#eval qNumber 2 3
#eval qNumber 2 4
#eval qNumber 2 5
#eval qFactorial 2 4
#eval qBinomial 2 5 2
#eval qBinomial 2 6 3

#eval qNumber 1 5
#eval qNumber 1 10
#eval qFactorial 2 3
#eval qBinomial 1 5 2

#eval QPlaneMonomial.mul 2 (⟨1,0⟩ : QPlaneMonomial) (⟨0,1⟩ : QPlaneMonomial)
#eval QPlaneMonomial.qfactor 2 (⟨0,1⟩ : QPlaneMonomial) (⟨1,0⟩ : QPlaneMonomial)
#eval QPlaneMonomial.degree ⟨3,5⟩

#eval qExpNatTerms 2 1 3
#eval qExpNatTerms 2 1 5
#eval qExpNatTerms 3 1 5

#eval matTrace [[1,0],[0,1]]
#eval matTrace [[1,2],[3,4]]
#eval matTrace [[2,0,0],[0,3,0],[0,0,5]]

#eval qDimSpinHalf 2
#eval qDimSpinHalf 3
#eval qDimSpinOne 2
#eval qDimSpinOne 3

#eval Uqsl2Coproduct (Uqsl2Monomial.one)
#eval Uqsl2Coproduct (Uqsl2Monomial.E)
#eval Uqsl2Coproduct (Uqsl2Monomial.F)
#eval Uqsl2Coproduct (Uqsl2Monomial.K)
#eval Uqsl2Counit Uqsl2Monomial.one
#eval Uqsl2Counit Uqsl2Monomial.E
#eval Uqsl2Counit Uqsl2Monomial.K

#eval LusztigT Uqsl2Monomial.E
#eval LusztigT Uqsl2Monomial.F
#eval LusztigT (LusztigT Uqsl2Monomial.E)
#eval LusztigT (LusztigT Uqsl2Monomial.F)

#eval LieType.rank (LieType.An 2)
#eval LieType.dim LieType.G2
#eval LieType.dim LieType.E8
#eval LieType.numPosRoots LieType.F4
#eval LieType.weylOrder (LieType.An 3)
#eval LieType.weylOrder LieType.G2

#eval qNumber 2 1
#eval qNumber 2 2
#eval qNumber 2 3
#eval qNumber 2 4
#eval qNumber 2 5
#eval qNumber 2 6
#eval qNumber 2 7
#eval qNumber 2 8
#eval qNumber 2 9
#eval qNumber 2 10
#eval qNumber 3 1
#eval qNumber 3 2
#eval qNumber 3 3
#eval qNumber 3 4
#eval qNumber 3 5
#eval qNumber 3 6
#eval qNumber 3 7
#eval qNumber 3 8
#eval qNumber 3 9
#eval qNumber 3 10
#eval qNumber 4 1
#eval qNumber 4 2
#eval qNumber 4 3
#eval qNumber 4 4
#eval qNumber 4 5
#eval qNumber 4 6
#eval qNumber 4 7
#eval qNumber 4 8
#eval qNumber 4 9
#eval qNumber 4 10
#eval qNumber 5 1
#eval qNumber 5 2
#eval qNumber 5 3
#eval qNumber 5 4
#eval qNumber 5 5
#eval qNumber 5 6
#eval qNumber 5 7
#eval qNumber 5 8
#eval qNumber 5 9
#eval qNumber 5 10
#eval qFactorial 2 0
#eval qFactorial 2 1
#eval qFactorial 2 2
#eval qFactorial 2 3
#eval qFactorial 2 4
#eval qFactorial 2 5
#eval qFactorial 2 6
#eval qFactorial 2 7
#eval qFactorial 3 0
#eval qFactorial 3 1
#eval qFactorial 3 2
#eval qFactorial 3 3
#eval qFactorial 3 4
#eval qFactorial 3 5
#eval qFactorial 3 6
#eval qFactorial 3 7

/-! ### EXTENDED EXAMPLES ### -/


end MiniQuantumGroups
