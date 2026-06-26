/-
# MiniVertexAlgebras.Core.AxiomCompat

Local compatibility stubs for Axiom, Formula, AxiomSystem types.
Provides these types without external kernel dependencies.
-/

namespace MiniVertexAlgebras

/-! ## Formula type

A propositional formula with labeled atoms. Used as a placeholder
for axiom statements. -/

inductive Formula where
  | atom : Nat → Formula
  | true : Formula
  | false : Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | impl : Formula → Formula → Formula
  deriving Repr, Inhabited

/-- Construct a predicate formula (placeholder for n-ary predicates) -/
def Formula.pred (_arity : Nat) (_args : List Nat) : Formula :=
  Formula.atom 0

/-! ## Axiom type

An axiom is a named statement with a description. -/

structure Axiom where
  name : String
  statement : Formula
  description : String
  deriving Repr, Inhabited

/-- Construct a simple axiom with just name and description.
Uses the auto-generated Axiom.mk constructor for standard axioms. -/
def Axiom.mkSimple (name : String) (description : String) : Axiom :=
  { name, statement := Formula.atom 0, description }

/-- The label (name) accessor for Axiom -/
def Axiom.label (a : Axiom) : String := a.name

/-! ## AxiomSet

A collection of axioms with a name. -/

structure AxiomSet where
  name : String
  axioms : List Axiom
  deriving Repr, Inhabited

/-! ## AxiomSystem

An axiom system is a named axiom set with version information. -/

structure AxiomSystem where
  name : String
  version : String
  axioms : AxiomSet
  deriving Repr, Inhabited

/-- Construct an empty axiom system -/
def AxiomSystem.empty (name : String) (version : String) : AxiomSystem :=
  { name, version, axioms := { name := name, axioms := [] } }

/-- Add axioms to an axiom system -/
def AxiomSystem.addAxioms (sys : AxiomSystem) (newAxioms : List Axiom) : AxiomSystem :=
  { sys with axioms := { sys.axioms with axioms := sys.axioms.axioms ++ newAxioms } }

/-- Number of axioms in the system -/
def AxiomSystem.length (sys : AxiomSystem) : Nat :=
  sys.axioms.axioms.length

/-- Get axioms as list -/
def AxiomSystem.axiomsList (sys : AxiomSystem) : List Axiom :=
  sys.axioms.axioms

/-! ## #eval verification -/

#eval "Core.AxiomCompat: Formula, Axiom, AxiomSet, AxiomSystem defined locally"

end MiniVertexAlgebras
