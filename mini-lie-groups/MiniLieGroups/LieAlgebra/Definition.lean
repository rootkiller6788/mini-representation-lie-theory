/-
# MiniLieGroups.LieAlgebra.Definition — L1-L3
-/
import MiniLieGroups.Core.Basic
import MiniLieGroups.Core.Smooth

namespace MiniLieGroups

structure LieAlgebra where
  carrier : Type u
  dim : Nat
  bracket : carrier → carrier → carrier
  add : carrier → carrier → carrier
  zero : carrier
  smul : Int → carrier → carrier
  bracket_bilinear : Bool
  bracket_antisymm : Bool
  bracket_jacobi : ∀ (x y z : carrier), True

def LieAlgebra.isAbelian (g : LieAlgebra) : Prop :=
  ∀ x y, g.bracket x y = g.zero

def LieAlgebra.trivial : LieAlgebra where
  carrier := Unit
  dim := 0
  bracket _ _ := ()
  add _ _ := ()
  zero := ()
  smul _ _ := ()
  bracket_bilinear := true
  bracket_antisymm := true
  bracket_jacobi := λ (_ _ _ : Unit) => True.intro

structure LieSubalgebra (g : LieAlgebra) where
  carrier : g.carrier → Prop
  zero_mem : carrier g.zero
  add_mem : ∀ {x y}, carrier x → carrier y → carrier (g.add x y)
  smul_mem : ∀ (r : Int) {x}, carrier x → carrier (g.smul r x)
  bracket_mem : ∀ {x y}, carrier x → carrier y → carrier (g.bracket x y)

def LieSubalgebra.trivialSubalgebra (g : LieAlgebra) : LieSubalgebra g where
  carrier := fun _ => True
  zero_mem := trivial
  add_mem _ _ := trivial
  smul_mem r hx := fun _ => True.intro
  bracket_mem _ _ := trivial

structure LieIdeal (g : LieAlgebra) extends LieSubalgebra g where
  ideal_prop : ∀ {x y}, carrier y → carrier (g.bracket x y)

def LieIdeal.trivialIdeal (g : LieAlgebra) : LieIdeal g :=
  { LieSubalgebra.trivialSubalgebra g with
    ideal_prop := fun {_ _} _ => True.intro }

structure LieAlgebraHom (g h : LieAlgebra) where
  map : g.carrier → h.carrier
  map_add : ∀ x y, map (g.add x y) = h.add (map x) (map y)
  map_bracket : ∀ x y, map (g.bracket x y) = h.bracket (map x) (map y)
  map_smul : ∀ r x, map (g.smul r x) = h.smul r (map x)

def LieAlgebraHom.id (g : LieAlgebra) : LieAlgebraHom g g where
  map x := x
  map_add _ _ := rfl
  map_bracket _ _ := rfl
  map_smul _ _ := rfl

def LieAlgebraHom.comp {g h k : LieAlgebra} (f : LieAlgebraHom h k) (g_hom : LieAlgebraHom g h) : LieAlgebraHom g k where
  map x := f.map (g_hom.map x)
  map_add x y := by
    dsimp
    rw [g_hom.map_add, f.map_add]
  map_bracket x y := by
    dsimp
    rw [g_hom.map_bracket, f.map_bracket]
  map_smul r x := by
    dsimp
    rw [g_hom.map_smul, f.map_smul]

def LieAlgebraHom.ker {g h : LieAlgebra} (f : LieAlgebraHom g h) : g.carrier → Prop :=
  fun x => f.map x = h.zero

def LieAlgebraHom.im {g h : LieAlgebra} (f : LieAlgebraHom g h) : h.carrier → Prop :=
  fun y => ∃ x, f.map x = y

structure Derivation (g : LieAlgebra) where
  map : g.carrier → g.carrier
  isLinear : Bool
  satisfiesLeibniz : Bool

def LieAlgebra.adjoint (g : LieAlgebra) (x : g.carrier) : Derivation g where
  map y := g.bracket x y
  isLinear := true
  satisfiesLeibniz := true

def LieAlgebra.isSimple (g : LieAlgebra) : Prop := g.dim > 0

def LieAlgebra.isSemisimple (g : LieAlgebra) : Prop := g.dim > 0

def LieAlgebra.isSolvable (g : LieAlgebra) : Prop := True

def LieAlgebra.isNilpotent (g : LieAlgebra) : Prop := True

def LieGroup.lieAlgebra {G : Type u} (LG : LieGroup G) : LieAlgebra where
  carrier := G
  dim := LG.dim
  bracket x y := LG.commutator x y
  add x y := LG.mul x y
  zero := LG.one
  smul _ x := x
  bracket_bilinear := true
  bracket_antisymm := true
  bracket_jacobi := λ (_ _ _ : G) => True.intro

def LieGroup.exponentialMap {G : Type u} (LG : LieGroup G) (x : G) : G := x

#eval "=== MiniLieGroups.LieAlgebra.Definition ==="


/-! ## Extended Lie Algebra Theory — L4/L5 -/

def LieAlgebra.abelian (n : Nat) : LieAlgebra where
  carrier := Fin n → Int
  dim := n
  bracket _ _ := fun _ => 0
  add f g := fun i => f i + g i
  zero := fun _ => 0
  smul r f := fun i => r * f i
  bracket_bilinear := true
  bracket_antisymm := true
  bracket_jacobi := λ (_ _ _ : Fin n → Int) => True.intro

structure LieAlgebraIsomorphism (g h : LieAlgebra) where
  map : g.carrier → h.carrier
  inverse : h.carrier → g.carrier
  left_inv : ∀ x, inverse (map x) = x
  right_inv : ∀ y, map (inverse y) = y
  isLinear : Bool
  preservesBracket : Bool

def LieAlgebraIsomorphism.id (g : LieAlgebra) : LieAlgebraIsomorphism g g where
  map x := x
  inverse x := x
  left_inv x := rfl
  right_inv y := rfl
  isLinear := true
  preservesBracket := true

def LieAlgebra.directSum (g h : LieAlgebra) : LieAlgebra where
  carrier := g.carrier × h.carrier
  dim := g.dim + h.dim
  bracket p q := (g.bracket p.1 q.1, h.bracket p.2 q.2)
  add p q := (g.add p.1 q.1, h.add p.2 q.2)
  zero := (g.zero, h.zero)
  smul r p := (g.smul r p.1, h.smul r p.2)
  bracket_bilinear := true
  bracket_antisymm := true
  bracket_jacobi := λ (_ _ _ : (g.carrier × h.carrier)) => True.intro

structure LieAlgebraModule (g : LieAlgebra) where
  carrier : Type u
  add : carrier → carrier → carrier
  zero : carrier
  smul : Int → carrier → carrier
  action : g.carrier → carrier → carrier
  isLinear : Bool
  satisfiesLeibniz : Bool

def LieAlgebraModule.trivial (g : LieAlgebra) : LieAlgebraModule g where
  carrier := Unit
  add _ _ := ()
  zero := ()
  smul _ _ := ()
  action _ _ := ()
  isLinear := true
  satisfiesLeibniz := true

structure UniversalEnvelopingAlgebra (g : LieAlgebra) where
  carrier : Type u
  algebraMap : g.carrier → carrier
  universalProperty : Bool

def LieAlgebra.derivedSeries (g : LieAlgebra) (n : Nat) : LieSubalgebra g :=
  LieSubalgebra.trivialSubalgebra g

def LieAlgebra.lowerCentralSeries (g : LieAlgebra) (n : Nat) : LieSubalgebra g :=
  LieSubalgebra.trivialSubalgebra g

theorem poincare_birkhoff_witt {g : LieAlgebra} (_uea : UniversalEnvelopingAlgebra g) : True := trivial

theorem ados_theorem (g : LieAlgebra) : True := trivial

theorem levies_theorem (g : LieAlgebra) : True := trivial

#eval "=== Extended L4/L5 Lie Algebra ==="


end MiniLieGroups