/-
# MiniCharacterTheory.Core.AxiomCompat

Self-contained definitions for Formula, Axiom, AxiomSet, AxiomSystem.
Defined locally for module independence.
-/

namespace MiniCharacterTheory

/-! ## Formula Type -/

inductive Formula : Type where
  | atom : Nat -> Formula
  | trueF : Formula
  | falseF : Formula
  | notF : Formula -> Formula
  | andF : Formula -> Formula -> Formula
  | orF : Formula -> Formula -> Formula
  | implF : Formula -> Formula -> Formula
  | equivF : Formula -> Formula -> Formula
deriving BEq, DecidableEq, Repr, Inhabited

namespace Formula

def eval (f : Formula) (assignment : Nat -> Bool) : Bool :=
  match f with
  | atom n => assignment n
  | trueF => true
  | falseF => false
  | notF A => !(eval A assignment)
  | andF A B => eval A assignment && eval B assignment
  | orF A B => eval A assignment || eval B assignment
  | implF A B => !(eval A assignment) || eval B assignment
  | equivF A B => eval A assignment == eval B assignment

def atoms : Formula -> List Nat
  | atom n => [n]
  | trueF => []
  | falseF => []
  | notF A => atoms A
  | andF A B => atoms A ++ atoms B
  | orF A B => atoms A ++ atoms B
  | implF A B => atoms A ++ atoms B
  | equivF A B => atoms A ++ atoms B

end Formula

/-! ## Axiom type -/

structure Axiom where
  name : String
  statement : Formula
  description : Option String
deriving Repr, Inhabited

def Axiom.simple (name : String) (statement : Formula) : Axiom :=
  { name, statement, description := none }

def Axiom.described (name : String) (statement : Formula) (desc : String) : Axiom :=
  { name, statement, description := some desc }

def Axiom.label (a : Axiom) : String := a.name

/-! ## AxiomSet -/

structure AxiomSet where
  axioms : List Axiom
deriving Repr, Inhabited

namespace AxiomSet

def empty : AxiomSet := { axioms := [] }
def add (s : AxiomSet) (a : Axiom) : AxiomSet := { axioms := s.axioms ++ [a] }
def addAll (s : AxiomSet) (as : List Axiom) : AxiomSet := { axioms := s.axioms ++ as }
def containsName (s : AxiomSet) (name : String) : Bool :=
  s.axioms.any (fun a => a.name == name)
def findByName (s : AxiomSet) (name : String) : Option Axiom :=
  s.axioms.find? (fun a => a.name == name)
def size (s : AxiomSet) : Nat := s.axioms.length

end AxiomSet

/-! ## AxiomSystem -/

structure AxiomSystem where
  name : String
  version : String
  axioms : AxiomSet
  description : Option String
deriving Repr, Inhabited

namespace AxiomSystem

def emptyDefault : AxiomSystem :=
  { name := "CharacterTheory", version := "1.0", axioms := AxiomSet.empty, description := none }

def empty (name version : String) : AxiomSystem :=
  { name, version, axioms := AxiomSet.empty, description := none }

def addAxiom (sys : AxiomSystem) (ax : Axiom) : AxiomSystem :=
  { sys with axioms := sys.axioms.add ax }

def addAxioms (sys : AxiomSystem) (axs : List Axiom) : AxiomSystem :=
  { sys with axioms := sys.axioms.addAll axs }

def length (sys : AxiomSystem) : Nat := sys.axioms.size

def axiomsList (sys : AxiomSystem) : List Axiom := sys.axioms.axioms

end AxiomSystem

/-! ## Helper: Formula.pred placeholder -/

def Formula.pred (_arity : Nat) (_args : List Nat) : Formula :=
  Formula.atom 0

/-! ## Helper: Axiom construction (used throughout the codebase) -/

def mkAxiom (name : String) (statement : Formula) (description : String) : Axiom :=
  Axiom.described name statement description

def mkSimpleAxiom (name : String) (description : String) : Axiom :=
  Axiom.described name (Formula.atom 0) description

/-! ## Dependency stubs -/

namespace Dependency

structure TheoryNode where
  name : String
  deps : List String
deriving Repr, Inhabited

def node (name : String) (deps : List String) : TheoryNode :=
  { name, deps }

end Dependency

/-! ## #eval -/
#eval "AxiomCompat: Formula, Axiom, AxiomSet, AxiomSystem defined locally"

end MiniCharacterTheory
