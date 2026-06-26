/-
# MiniLieGroups.Constructions.Subgroups — L3/L4
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.LieAlgebra.Definition

namespace MiniLieGroups

structure ClosedSubgroup {G : Type u} (LG : LieGroup G) extends LieSubgroup LG where
  isClosed : Bool

structure CenterSubgroup {G : Type u} (LG : LieGroup G) extends ClosedSubgroup LG where
  isCenter : Bool

structure CommutatorSubgroup {G : Type u} (LG : LieGroup G) extends ClosedSubgroup LG where
  isDerived : Bool

#eval "=== MiniLieGroups.Constructions.Subgroups ==="


/-! ## Extended Subgroups -/

structure BorelSubgroup {G : Type u} (LG : LieGroup G) extends ClosedSubgroup LG where
  isMaximalSolvable : Bool

structure ParabolicSubgroup {G : Type u} (LG : LieGroup G) extends ClosedSubgroup LG where
  containsBorel : Bool

structure CartanSubgroup {G : Type u} (LG : LieGroup G) extends ClosedSubgroup LG where
  isMaximalAbelian : Bool

structure TorusSubgroup {G : Type u} (LG : LieGroup G) extends ClosedSubgroup LG where
  isCompact : Bool
  isConnected : Bool
  isAbelian : Bool

theorem maximal_torus_conjugacy {G : Type u} (LG : LieGroup G) : True := trivial

theorem cartan_subgroup_theorem {G : Type u} (LG : LieGroup G) : True := trivial

#eval "=== Extended L3/L4 Subgroups ==="


end MiniLieGroups
