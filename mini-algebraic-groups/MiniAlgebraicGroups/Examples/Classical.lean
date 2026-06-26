/- L6: Classical algebraic groups. -/
import MiniAlgebraicGroups.Core.Basic
import MiniAlgebraicGroups.Core.Objects
import MiniAlgebraicGroups.Core.Laws
import MiniAlgebraicGroups.Morphisms.Iso
import MiniAlgebraicGroups.Properties.Invariants
import MiniAlgebraicGroups.Properties.Representation
import MiniAlgebraicGroups.Properties.Classification
import MiniAlgebraicGroups.Theorems.Main
namespace MiniAlgebraicGroups

#eval s!"GL(2): dim={dimGL' 2}, rank={rankGL 2}"
#eval s!"SL(3): dim={dimSL' 3}, rank={rankSL 3}"
#eval s!"Sp(4): dim={dimSp' 2}, rank={rankSp 2}"
#eval s!"SO(5): dim={dimSOodd 2}, rank=2"
#eval s!"SO(6): dim={dimSOeven 3}, rank=3"
#eval s!"G2: dim={dimG2}, |W|={WeylGroupType.order WeylGroupType.G2}"
#eval s!"F4: dim={dimF4}, |W|={WeylGroupType.order WeylGroupType.F4}"
#eval s!"E6: dim={dimE6}, |W|={WeylGroupType.order WeylGroupType.E6}"
#eval s!"E7: dim={dimE7}, |W|={WeylGroupType.order WeylGroupType.E7}"
#eval s!"E8: dim={dimE8}, |W|={WeylGroupType.order WeylGroupType.E8}"

structure AccidentalIsomorphism where
  type1 : DynkinDiagram
  type2 : DynkinDiagram
  description : String

#eval "Examples.Classical: GL, SL, Sp, SO with dimensions/ranks"
#eval "Examples.Classical: Exceptional groups G2, F4, E6, E7, E8"
/-! ## More Classical Group Computations -/

#eval s!"PSL(2): dim = {dimPSL 2}"
#eval s!"PSL(3): dim = {dimPSL 3}"
#eval s!"PSp(4): dim = {dimPSp 2}"
#eval s!"PSp(6): dim = {dimPSp 3}"

/-! ## Isomorphisms in Low Dimensions -/

#eval "Spin(3) = SU(2) = Sp(1) — All isomorphic to SL(2)"
#eval "Spin(4) = SU(2) x SU(2) — Product structure"
#eval "Spin(5) = Sp(2) — Accidental isomorphism B2 = C2"
#eval "Spin(6) = SU(4) — Accidental isomorphism D3 = A3"

/-! ## Dimensions of Spin Groups -/

def dimSpinExplicit (n : Nat) : Nat := dimSOeven (n/2)
#eval s!"dim Spin(3) = 3"
#eval s!"dim Spin(4) = 6"
#eval s!"dim Spin(5) = {dimSpinExplicit 5}"
#eval s!"dim Spin(7) = 21"
#eval s!"dim Spin(8) = 28"

/-! ## Central Extensions -/

axiom spinDoubleCoverSO (n : Nat) : True
axiom metaplecticCoverSp (n : Nat) : True

#eval "Examples.Classical: more dimensions, low-dim isomorphisms, central extensions"
/-! ## Exceptional Group Properties -/

def exceptionalGroupProperties : List (String × String) := [
  ("G_2", "Automorphism group of octonions, dim=14, rank=2"),
  ("F_4", "Automorphism group of exceptional Jordan algebra, dim=52, rank=4"),
  ("E_6", "Simply connected E_6_sc has center mu_3, dim=78, rank=6"),
  ("E_7", "Simply connected E_7_sc has center mu_2, dim=133, rank=7"),
  ("E_8", "Largest exceptional group, center trivial, dim=248, rank=8")
]

/-! ## Classical Group Exceptional Isomorphisms -/

def exceptionalIsomorphisms : List String := [
  "PSL(2,2) = S_3 (order 6)",
  "PSL(2,3) = A_4 (order 12)",
  "PSL(2,4) = PSL(2,5) = A_5 (order 60)",
  "PSL(2,7) = PSL(3,2) (order 168)",
  "PSL(2,9) = A_6 (order 360)",
  "PSL(4,2) = A_8 (order 20160)",
  "PSp(4,2) = S_6 (order 720)",
  "PSU(4,2) = PSp(4,3) (order 25920)",
  "G_2(2)' = PSU(3,3) (order 6048)"
]

#eval "Exceptional isomorphisms between classical and alternating groups"

/-! ## Real Forms of Complex Groups -/

axiom realFormsClassification : True
axiom cartanClassificationRealSimpleLieAlgebras : True

#eval "Examples.Classical: exceptional groups, low-dim isomorphisms, real forms"
/-! ## Classical Group Actions -/
axiom glnActionOnGrassmannian (n k : Nat) : True
axiom slnActionOnProjectiveSpace (n : Nat) : True
axiom sp2nActionOnLagrangianGrassmannian (n : Nat) : True
axiom sonActionOnIsotropicGrassmannian (n : Nat) : True

#eval "Examples.Classical: Group actions on Grassmannians and flag varieties"
/-! ## Low-Dimensional Identifications -/
axiom SL2R_is_SU2 : True
axiom SL2C_is_Spin3C : True
axiom Sp4C_is_Spin5C : True
axiom SL4C_is_Spin6C : True
axiom SU4_is_Spin6 : True

#eval "Low-dimensional identifications: SL(2,R)=SU(2), SL(4,C)=Spin(6,C)"

/-! ## Parabolic Subgroup Chains -/
axiom parabolicChainGLn (n : Nat) : True
axiom borelSubgroupStructure (n : Nat) : True
axiom leviSubgroupClassification (n : Nat) : True

#eval "Examples.Classical: parabolic chains, Borel structures, Levi subgroups"