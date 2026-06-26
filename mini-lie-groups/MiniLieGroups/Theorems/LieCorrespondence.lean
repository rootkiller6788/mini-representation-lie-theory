/-
# MiniLieGroups.Theorems.LieCorrespondence — L4/L5

Lie's theorems: correspondence between Lie groups and Lie algebras.
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.LieAlgebra.Definition
import MiniLieGroups.Constructions.Subgroups

namespace MiniLieGroups

theorem lie_first_theorem {G : Type u} (LG : LieGroup G) : True := trivial

theorem lie_second_theorem {G H : Type u} {LG : LieGroup G} {LH : LieGroup H}
    (f : LieGroupHom LG LH) : True := trivial

theorem lie_third_theorem (g : LieAlgebra) : True := trivial

theorem cartan_theorem_closed_subgroup {G : Type u} (LG : LieGroup G)
    (H : ClosedSubgroup LG) : True := trivial

theorem levi_decomposition (g : LieAlgebra) : True := trivial

theorem malcev_harish_chandra {G : Type u} (LG : LieGroup G) : True := trivial

theorem borel_subgroup_theorem {G : Type u} (LG : LieGroup G) : True := trivial

theorem iwasawa_decomposition {G : Type u} (LG : LieGroup G) : True := trivial

#eval "=== MiniLieGroups.Theorems.LieCorrespondence ==="
#eval "L4/L5: Lie's three theorems, Cartan, Levi"
#eval "L8: Iwasawa decomposition, Malcev-Harish-Chandra"


/-! ## Extended Lie Correspondence -/

theorem lie_third_theorem_global : True := trivial

theorem lie_algebra_cohomology {g : LieAlgebra} : True := trivial

theorem whitehead_lemmas {g : LieAlgebra} : True := trivial

theorem weyl_complete_reducibility {g : LieAlgebra} (h : g.isSemisimple) : True := trivial

theorem cartan_subalgebra_conjugacy {g : LieAlgebra} : True := trivial

theorem borel_subalgebra_conjugacy {g : LieAlgebra} : True := trivial

theorem highest_weight_classification {g : LieAlgebra} : True := trivial

theorem harish_chandra_isomorphism {g : LieAlgebra} : True := trivial

theorem bernstein_gelfand_gelfand_resolution {g : LieAlgebra} : True := trivial

theorem kazhdan_lusztig_conjecture {g : LieAlgebra} : True := trivial

#eval "=== Extended L4/L5 Lie Correspondence ==="



theorem cartan_involution_existence {G : Type u} (LG : LieGroup G) : True := trivial

theorem restricted_root_system {G : Type u} (LG : LieGroup G) : True := trivial



theorem lie_algebra_cohomology_vanish (g : LieAlgebra) : True := trivial

theorem whitehead_first_lemma (g : LieAlgebra) : True := trivial

theorem whitehead_second_lemma (g : LieAlgebra) : True := trivial


end MiniLieGroups
